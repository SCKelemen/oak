package nativegen

import "github.com/SCKelemen/oak/asm"

type recordBaseSite struct {
	start, def       int
	stride, dest     asm.Register
	index, base      asm.Register
	low, high        asm.Immediate
	uses             []int
	localUseBoundary int
}

// shareRecordBase eliminates repeated materializations of one record-span
// element base after register allocation:
//
//	movz wT, #lo; movk wT, #hi, lsl #16; umaddl xD, wI, wT, xB
//
// The first result is retargeted to a declared caller-saved scratch register
// unused for the whole region; later identical triples disappear and their
// block-local reads use that result. The first definition must dominate every
// replacement, index/base must be unchanged on every path, and calls delimit
// the region. A destination live past a control boundary refuses its site.
// The whole candidate remains verifier-gated.
func shareRecordBase(fn *asm.Function) int {
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
		site, ok := recordBaseAt(items, live, i)
		if ok {
			sites = append(sites, site)
		}
	}
	for firstIndex, first := range sites {
		group := []recordBaseSite{first}
		for _, site := range sites[firstIndex+1:] {
			same := sameRecordBase(first, site)
			dominates := itemDominates(succ, first.def, site.start)
			stable := guardOperandsStable(items, succ, first.def+1, site.start, first.index.Num, first.base.Num)
			strideDead := live[site.def]&(1<<uint(site.stride.Num)) == 0
			if !same || !dominates || !stable || !strideDead {
				continue
			}
			group = append(group, site)
		}
		if len(group) < 2 {
			continue
		}
		scratch, found := recordBaseScratch(fn.Clobbers, items, first.start, first)
		if !found {
			continue
		}
		out := append([]asm.Item(nil), items...)
		remove := make([]bool, len(items))
		definition := out[first.def].(asm.Instruction)
		operands := append([]asm.Operand(nil), definition.Operands...)
		operands[0] = scratch
		definition.Operands = operands
		definition.CheckedFacts = nil
		out[first.def] = definition
		for _, use := range first.uses {
			out[use] = renameReads(out[use].(asm.Instruction), first.dest.Num, scratch)
		}
		for _, site := range group[1:] {
			remove[site.start], remove[site.start+1], remove[site.def] = true, true, true
			for _, use := range site.uses {
				out[use] = renameReads(out[use].(asm.Instruction), site.dest.Num, scratch)
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

func recordBaseAt(items []asm.Item, live []uint32, start int) (recordBaseSite, bool) {
	a, okA := items[start].(asm.Instruction)
	b, okB := items[start+1].(asm.Instruction)
	c, okC := items[start+2].(asm.Instruction)
	if !okA || !okB || !okC || a.Mnemonic != "movz" || b.Mnemonic != "movk" || c.Mnemonic != "umaddl" ||
		a.Cond != "" || b.Cond != "" || c.Cond != "" || len(a.Operands) != 2 || len(b.Operands) != 2 || len(c.Operands) != 4 {
		return recordBaseSite{}, false
	}
	strideA, strideAOK := generalReg(a.Operands[0])
	strideB, strideBOK := generalReg(b.Operands[0])
	dest, destOK := generalReg(c.Operands[0])
	index, indexOK := generalReg(c.Operands[1])
	strideC, strideCOK := generalReg(c.Operands[2])
	base, baseOK := generalReg(c.Operands[3])
	low, lowOK := a.Operands[1].(asm.Immediate)
	high, highOK := b.Operands[1].(asm.Immediate)
	if !strideAOK || !strideBOK || !destOK || !indexOK || !strideCOK || !baseOK || !lowOK || !highOK ||
		strideA.Class != asm.ClassW || strideB.Class != asm.ClassW || strideC.Class != asm.ClassW || index.Class != asm.ClassW ||
		dest.Class != asm.ClassX || base.Class != asm.ClassX || strideA.Num != strideB.Num || strideA.Num != strideC.Num ||
		low.Shift != 0 || low.Value < 0 || low.Value > 0xffff || high.Shift != 16 || high.Value < 0 || high.Value > 0xffff ||
		dest.Num == index.Num || dest.Num == base.Num {
		return recordBaseSite{}, false
	}
	uses, boundary, ok := localDefinitionUses(items, live, start+2, dest.Num)
	if !ok || len(uses) == 0 {
		return recordBaseSite{}, false
	}
	return recordBaseSite{start: start, def: start + 2, stride: strideA, dest: dest, index: index, base: base, low: low, high: high, uses: uses, localUseBoundary: boundary}, true
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
