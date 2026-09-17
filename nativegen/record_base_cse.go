package nativegen

import "github.com/SCKelemen/oak/asm"

type recordBaseSite struct {
	start, middle, def int
	stride, dest       asm.Register
	index, base        asm.Register
	low, high          asm.Immediate
	uses               []int
	localUseBoundary   int
	rewritable         bool
}

// shareRecordBase eliminates repeated materializations of one record-span
// element base after register allocation:
//
//	movz wT, #lo; ...; movk wT, #hi, lsl #16; ...; umaddl xD, wI, wT, xB
//
// Independent scheduled instructions may remain between those three
// instructions. A control boundary or any intervening mention of wT refuses
// the site. The first result is retargeted to a declared caller-saved scratch
// register unused for the whole region; later identical triples disappear and
// their block-local reads use that result. The first definition must dominate
// every replacement, index/base must be unchanged on every path, and calls
// delimit the region. A destination live past a control boundary refuses its
// site. The whole candidate remains verifier-gated.
func shareRecordBase(fn *asm.Function) int {
	return shareRecordBaseWith(fn, false)
}

// reuseRecordBaseDestination makes the first computed base itself the carrier
// when it remains unmodified through every replacement use. It is separate
// from shareRecordBase so candidate search retains the established
// scratch-carried result as a verifier-gated fallback.
func reuseRecordBaseDestination(fn *asm.Function) int {
	return shareRecordBaseWith(fn, true)
}

func shareRecordBaseWith(fn *asm.Function, existingDestinationOnly bool) int {
	if fn == nil || (fn.Arch != "" && fn.Arch != asm.ArchArm64) {
		return 0
	}
	items := fn.Items
	succ, ok := itemSuccessors(items)
	if !ok || itemCFGHasCycle(succ) {
		return 0
	}
	live := liveAfter(items)
	var sites []recordBaseSite
	for i := 0; i+2 < len(items); i++ {
		site, ok := recordBaseAt(items, live, succ, i, existingDestinationOnly)
		if ok {
			sites = append(sites, site)
		}
	}
	for firstIndex, first := range sites {
		group := []recordBaseSite{first}
		for _, site := range sites[firstIndex+1:] {
			if !site.rewritable {
				continue
			}
			same := sameRecordBase(first, site)
			dominates := itemDominates(succ, first.def, site.def)
			stable := guardOperandsStable(items, succ, first.def+1, site.def, first.index.Num, first.base.Num)
			strideDead := live[site.def]&(1<<uint(site.stride.Num)) == 0
			if !same || !dominates || !stable || !strideDead {
				continue
			}
			group = append(group, site)
		}
		if len(group) < 2 {
			continue
		}
		carrier, found := asm.Register{}, false
		if existingDestinationOnly {
			carrier, found = existingRecordBaseCarrier(items, first, group)
		} else {
			carrier, found = recordBaseScratch(fn.Clobbers, items, first.start, first)
		}
		if !found {
			continue
		}
		out := append([]asm.Item(nil), items...)
		remove := make([]bool, len(items))
		if carrier.Num != first.dest.Num {
			definition := out[first.def].(asm.Instruction)
			operands := append([]asm.Operand(nil), definition.Operands...)
			operands[0] = carrier
			definition.Operands = operands
			definition.CheckedFacts = nil
			out[first.def] = definition
			for _, use := range first.uses {
				out[use] = renameReads(out[use].(asm.Instruction), first.dest.Num, carrier)
			}
		}
		for _, site := range group[1:] {
			remove[site.start], remove[site.middle], remove[site.def] = true, true, true
			for _, use := range site.uses {
				out[use] = renameReads(out[use].(asm.Instruction), site.dest.Num, carrier)
			}
		}
		fn.Items = fn.Items[:0]
		for i, item := range out {
			if !remove[i] {
				fn.Items = append(fn.Items, item)
			}
		}
		return len(group) - 1
	}
	return 0
}

// existingRecordBaseCarrier admits the first destination only when every
// instruction that will remain preserves it until all rewritten reads. The
// linear no-write condition is stronger than path-sensitive liveness: it also
// rejects writes on branches which do not reach the final textual use.
func existingRecordBaseCarrier(items []asm.Item, first recordBaseSite, group []recordBaseSite) (asm.Register, bool) {
	removed := make(map[int]bool, 3*(len(group)-1))
	lastUse := first.def
	for _, site := range group[1:] {
		removed[site.start], removed[site.middle], removed[site.def] = true, true, true
		for _, use := range site.uses {
			if use > lastUse {
				lastUse = use
			}
		}
	}
	if lastUse == first.def {
		return asm.Register{}, false
	}
	for i := first.def + 1; i <= lastUse; i++ {
		if removed[i] {
			continue
		}
		instruction, ok := items[i].(asm.Instruction)
		if !ok {
			continue
		}
		if instruction.Mnemonic == "bl" || instruction.Mnemonic == "blr" || writesGeneral(instruction, first.dest.Num) {
			return asm.Register{}, false
		}
	}
	return first.dest, true
}

func itemCFGHasCycle(succ [][]int) bool {
	state := make([]uint8, len(succ))
	var visit func(int) bool
	visit = func(at int) bool {
		if state[at] == 1 {
			return true
		}
		if state[at] == 2 {
			return false
		}
		state[at] = 1
		for _, next := range succ[at] {
			if visit(next) {
				return true
			}
		}
		state[at] = 2
		return false
	}
	for at := range succ {
		if state[at] == 0 && visit(at) {
			return true
		}
	}
	return false
}

// The scheduler only moves nearby independent instructions into these
// materializations. Keeping the recognition window small avoids turning this
// local cleanup into unbounded instruction search.
const recordBaseMaterializationSpan = 6

func recordBaseAt(items []asm.Item, live []uint32, succ [][]int, start int, allowCarriedDestination bool) (recordBaseSite, bool) {
	a, okA := items[start].(asm.Instruction)
	if !okA || a.Mnemonic != "movz" || a.Cond != "" || len(a.Operands) != 2 {
		return recordBaseSite{}, false
	}
	strideA, strideAOK := generalReg(a.Operands[0])
	low, lowOK := a.Operands[1].(asm.Immediate)
	if !strideAOK || !lowOK || strideA.Class != asm.ClassW || low.Shift != 0 || low.Value < 0 || low.Value > 0xffff {
		return recordBaseSite{}, false
	}
	middle, ok := nextGeneralRegisterMention(items, start+1, start+recordBaseMaterializationSpan, strideA.Num)
	if !ok {
		return recordBaseSite{}, false
	}
	b := items[middle].(asm.Instruction)
	if b.Mnemonic != "movk" || b.Cond != "" || len(b.Operands) != 2 {
		return recordBaseSite{}, false
	}
	strideB, strideBOK := generalReg(b.Operands[0])
	high, highOK := b.Operands[1].(asm.Immediate)
	if !strideBOK || !highOK || strideB.Class != asm.ClassW || strideA.Num != strideB.Num ||
		high.Shift != 16 || high.Value < 0 || high.Value > 0xffff {
		return recordBaseSite{}, false
	}
	def, ok := nextGeneralRegisterMention(items, middle+1, start+recordBaseMaterializationSpan, strideA.Num)
	if !ok {
		return recordBaseSite{}, false
	}
	c := items[def].(asm.Instruction)
	if c.Mnemonic != "umaddl" || c.Cond != "" || len(c.Operands) != 4 {
		return recordBaseSite{}, false
	}
	dest, destOK := generalReg(c.Operands[0])
	index, indexOK := generalReg(c.Operands[1])
	strideC, strideCOK := generalReg(c.Operands[2])
	base, baseOK := generalReg(c.Operands[3])
	if !destOK || !indexOK || !strideCOK || !baseOK || strideC.Class != asm.ClassW || index.Class != asm.ClassW ||
		dest.Class != asm.ClassX || base.Class != asm.ClassX || strideA.Num != strideC.Num ||
		strideA.Num == index.Num || strideA.Num == base.Num || dest.Num == index.Num || dest.Num == base.Num {
		return recordBaseSite{}, false
	}
	uses, boundary, ok := localDefinitionUses(items, live, def, dest.Num)
	rewritable := ok && len(uses) > 0
	if !rewritable && allowCarriedDestination {
		uses, boundary, rewritable = carriedDefinitionUses(items, succ, def, dest.Num)
	}
	if !rewritable && !allowCarriedDestination {
		return recordBaseSite{}, false
	}
	return recordBaseSite{start: start, middle: middle, def: def, stride: strideA, dest: dest, index: index, base: base, low: low, high: high, uses: uses, localUseBoundary: boundary, rewritable: rewritable}, true
}

// carriedDefinitionUses follows a definition across labels and branches only
// while the linear suffix contains no possible overwrite. Each renamed read
// must also be dominated by the definition. This is deliberately stricter
// than full reaching-definitions analysis, but admits a base carried through
// a read-only conditional without conflating values at a join.
func carriedDefinitionUses(items []asm.Item, succ [][]int, def, reg int) ([]int, int, bool) {
	var uses []int
	for i := def + 1; i < len(items); i++ {
		instruction, isInstruction := items[i].(asm.Instruction)
		if !isInstruction {
			continue
		}
		if instruction.Mnemonic == "bl" || instruction.Mnemonic == "blr" || writesGeneral(instruction, reg) {
			return uses, i, len(uses) > 0
		}
		if readsGeneral(instruction, reg) && itemDominates(succ, def, i) {
			uses = append(uses, i)
		}
	}
	return uses, len(items) - 1, len(uses) > 0
}

// nextGeneralRegisterMention finds the next read or write of reg without
// crossing a label, branch, or call. The caller checks the exact instruction
// which is allowed to make that mention.
func nextGeneralRegisterMention(items []asm.Item, from, through, reg int) (int, bool) {
	if through >= len(items) {
		through = len(items) - 1
	}
	for i := from; i <= through; i++ {
		ins, isIns := items[i].(asm.Instruction)
		if !isIns || isBranchMnemonic(ins.Mnemonic) {
			return 0, false
		}
		if readsGeneral(ins, reg) || writesGeneral(ins, reg) {
			return i, true
		}
	}
	return 0, false
}

func localDefinitionUses(items []asm.Item, live []uint32, def, reg int) ([]int, int, bool) {
	var uses []int
	for i := def + 1; i < len(items); i++ {
		ins, isIns := items[i].(asm.Instruction)
		if !isIns {
			if live[i]&(1<<uint(reg)) != 0 {
				return nil, i, false
			}
			return uses, i, true
		}
		if readsGeneral(ins, reg) {
			uses = append(uses, i)
		}
		if writesGeneral(ins, reg) {
			return uses, i, true
		}
		if isBranchMnemonic(ins.Mnemonic) {
			if live[i]&(1<<uint(reg)) != 0 {
				return nil, i, false
			}
			return uses, i, true
		}
	}
	return uses, len(items) - 1, true
}

func sameRecordBase(a, b recordBaseSite) bool {
	return a.index.Num == b.index.Num && a.index.Class == b.index.Class && a.base.Num == b.base.Num && a.base.Class == b.base.Class &&
		a.low == b.low && a.high == b.high
}

func recordBaseScratch(clobbers []asm.Register, items []asm.Item, from int, expression recordBaseSite) (asm.Register, bool) {
	declared := map[int]bool{}
	for _, reg := range clobbers {
		if reg.Class == asm.ClassW || reg.Class == asm.ClassX {
			declared[reg.Num] = true
		}
	}
	for _, candidate := range []int{17, 16, 15, 14, 13, 12, 11, 10, 9} {
		if !declared[candidate] || candidate == expression.index.Num || candidate == expression.base.Num {
			continue
		}
		used := false
		// The carried value is live until every replacement use. Requiring the
		// scratch to be absent from the entire suffix is deliberately stronger
		// than a linear interval check: a branch around the last textual use
		// cannot expose a clobber or a pre-existing live value.
		for i := from; i < len(items); i++ {
			if ins, ok := items[i].(asm.Instruction); ok && (readsGeneral(ins, candidate) || writesGeneral(ins, candidate)) {
				used = true
				break
			}
		}
		if !used {
			return xr(candidate), true
		}
	}
	return asm.Register{}, false
}

// SharedRecordBases reports how many repeated three-instruction record-base
// materializations a candidate removed.
func SharedRecordBases(fn *asm.Function) int { return sharedRecordBases[fn] }

var sharedRecordBases = map[*asm.Function]int{}

// ReusedRecordBaseDestinations reports how many repeated materializations
// used the first computed destination as their carried base.
func ReusedRecordBaseDestinations(fn *asm.Function) int { return reusedRecordBaseDestinations[fn] }

var reusedRecordBaseDestinations = map[*asm.Function]int{}

// RescheduledRecordBaseCarriers reports how many instructions moved when the
// final carrier-aware dependency graph was scheduled again.
func RescheduledRecordBaseCarriers(fn *asm.Function) int { return rescheduledRecordBaseCarriers[fn] }

var rescheduledRecordBaseCarriers = map[*asm.Function]int{}
