package nativegen

import (
	"math/bits"
	"strings"

	"github.com/SCKelemen/oak/asm"
)

// Late copy and branch cleanup (docs/spec/94-assembler.md §9 "Late
// cleanup"; docs/notes/optimizer-search-2026-09.md §11 "Machine"). The
// lowering spells a value's path through a scratch register wherever an
// expression's result meets the place it is used — `mov w10, w24; cbz w10,
// else`, `movz w10, #1; mov w9, w10`, `mov x10, x12; mov x22, x10` — and
// a branch to the label that follows it when an arm's tail is empty. The
// pass changes machine shape only (Lane.Cleanup, TransformCleanup). Every
// candidate must pass the seam checker. The whole-function verifier judges it
// where its subset applies; on trusted bodies, the local rules instead remain
// compiler obligations backed by the narrow equalities named below and by the
// fail-closed matcher tests. A trusted verdict is not a verifier proof.
//
// The rules are block-local, under a whole-function liveness of the
// general registers over the item list (blocks split at labels and after
// branches; a call kills x0–x18 and x30 and reads x0–x8; a return reads
// x0, x1, x8):
//
//  1. `mov rS, rX` followed by an instruction that reads rS, with rS's
//     old value dead after it: rX replaces rS in that instruction's reads
//     and the mov goes (a W copy's readers must read the W view, since
//     the copy zeroed the upper half). rX is never sp or the zero register,
//     and the reader must name rS in an operand (a call's implicit
//     argument read is not renamed).
//  2. an instruction of the retargetable set defining rS, followed by
//     `mov rD, rS` at the same width with rS dead after: the definition
//     writes rD and the mov goes.
//  3. `b L` followed by the label L: the branch goes.
//  4. `mov rA, rA`: goes.
//  5. `mov rV, rS; mov wI, wzr; str rV, [rB, wI, uxtw #scale]`
//     becomes `str rS, [rB]` when both temporaries are dead. The source may
//     be the matching zero register; aliases that would change the base or
//     source are rejected (`Oak.Forwarding.zero_index_store`).
//
// The pass runs to a fixpoint; cleanedCopies counts the instructions it
// removed.

// cleanupItems applies the rules to a function's items and reports how
// many instructions it removed.
func cleanupItems(items []asm.Item) ([]asm.Item, int) {
	return cleanupItemsWith(items, false)
}

// cleanupItemsWith is cleanupItems with the zero-store rule (rule 8)
// enabled: a store of the zero register is the scheduled machine's final
// spelling, so the rule runs in the post-schedule cleanup only — the
// register reallocation that follows the early cleanup reads a store's
// source as an allocatable value and spilled a whole body around one.
func cleanupItemsWith(items []asm.Item, zeroStores bool) ([]asm.Item, int) {
	removed := 0
	// The local rules expose the shapes the fold reads (a copy forwarded
	// into its compare, a Bool fused into its branch), and the fold exposes
	// shapes for the rules (a decided branch leaving a copy dead), so the
	// two alternate to a fixpoint.
	for pass := 0; pass < constPassLimit; pass++ {
		folded, n := foldConstantBranches(items)
		ruled, m := cleanupItemsRules(folded, zeroStores)
		items = ruled
		removed += n + m
		if n == 0 && m == 0 {
			break
		}
	}
	return items, removed
}

func cleanupItemsRules(items []asm.Item, zeroStores bool) ([]asm.Item, int) {
	removed := 0
	for {
		next, n := cleanupOnce(items, zeroStores)
		if n == 0 {
			return next, removed
		}
		items = next
		removed += n
	}
}

// generalReg reports a plain W or X register operand: not sp, not the zero
// register, not a vector.
func generalReg(o asm.Operand) (asm.Register, bool) {
	r, isReg := o.(asm.Register)
	if !isReg || (r.Class != asm.ClassW && r.Class != asm.ClassX) || r.Num < 0 || r.Num > 30 || r.ZeroRegister() {
		return asm.Register{}, false
	}
	return r, true
}

// isRegisterMove recognizes `mov rD, rS` between two general registers of
// one class.
func isRegisterMove(ins asm.Instruction) (dst, src asm.Register, ok bool) {
	if ins.Mnemonic != "mov" || len(ins.Operands) != 2 {
		return asm.Register{}, asm.Register{}, false
	}
	d, okD := generalReg(ins.Operands[0])
	s, okS := generalReg(ins.Operands[1])
	if !okD || !okS || d.Class != s.Class {
		return asm.Register{}, asm.Register{}, false
	}
	return d, s, true
}

// isRegisterOrZeroMove extends the ordinary move recognizer only for a source
// zero register of the same width. It deliberately excludes sp and every
// vector/RV64 register class.
func isRegisterOrZeroMove(ins asm.Instruction) (dst, src asm.Register, ok bool) {
	if ins.Mnemonic != "mov" || len(ins.Operands) != 2 {
		return asm.Register{}, asm.Register{}, false
	}
	dst, ok = generalReg(ins.Operands[0])
	src, isReg := ins.Operands[1].(asm.Register)
	if !ok || !isReg || src.Class != dst.Class {
		return asm.Register{}, asm.Register{}, false
	}
	if _, ordinary := generalReg(src); !ordinary && !src.ZeroRegister() {
		return asm.Register{}, asm.Register{}, false
	}
	return dst, src, true
}

// foldZeroIndexStore replaces exactly the scalar STR shape emitted for a
// constant-zero span index. It does not reason about bounds: the rewritten
// direct access must still pass the independent seam checker. The local
// address/value equality is `Oak.Forwarding.zero_index_store`; a trusted
// whole-body verifier verdict does not strengthen that claim.
func foldZeroIndexStore(dataMove, indexMove, store asm.Instruction) (asm.Instruction, int, int, bool) {
	dataTmp, dataSource, dataOK := isRegisterOrZeroMove(dataMove)
	indexTmp, indexSource, indexOK := isRegisterOrZeroMove(indexMove)
	if !dataOK || !indexOK || indexTmp.Class != asm.ClassW || !indexSource.ZeroRegister() ||
		dataMove.Cond != "" || indexMove.Cond != "" || store.Cond != "" ||
		store.Mnemonic != "str" || len(store.Operands) != 2 {
		return asm.Instruction{}, 0, 0, false
	}
	stored, isStored := store.Operands[0].(asm.Register)
	memory, isMemory := store.Operands[1].(asm.Memory)
	expectedShift := 3
	if dataTmp.Class == asm.ClassW {
		expectedShift = 2
	}
	if !isStored || !isMemory || stored.Class != dataTmp.Class || stored.Num != dataTmp.Num ||
		memory.Mode != asm.MemOffset || memory.Offset != 0 || memory.Index == nil ||
		memory.Index.Class != asm.ClassW || memory.Index.Num != indexTmp.Num ||
		memory.Extend != "uxtw" || memory.Shift != expectedShift || memory.MulVL ||
		memory.Base.Class != asm.ClassX || memory.Base.ZeroRegister() ||
		dataTmp.Num == memory.Base.Num || indexTmp.Num == memory.Base.Num ||
		indexTmp.Num == dataTmp.Num || (!dataSource.ZeroRegister() && indexTmp.Num == dataSource.Num) {
		return asm.Instruction{}, 0, 0, false
	}
	memory.Index = nil
	memory.Shift = 0
	memory.Extend = ""
	out := store
	out.Operands = []asm.Operand{dataSource, memory}
	// The indexed proof no longer describes an operand. A direct span access
	// must stand on a dominating length guard or the seam checker rejects it.
	out.CheckedFacts = nil
	return out, dataTmp.Num, indexTmp.Num, true
}

// liveAfter computes, for every instruction, the set of general registers
// live after it (a 31-bit mask over x0–x30), by a backward fixpoint over
// the blocks the labels and branches delimit.
func liveAfter(items []asm.Item) []uint32 {
	n := len(items)
	labelAt := map[string]int{}
	for i, item := range items {
		if l, isLabel := item.(asm.Label); isLabel {
			labelAt[l.Name] = i
		}
	}
	// Block starts: item 0, every label, every item after a branch.
	starts := make([]bool, n+1)
	starts[0] = true
	for i, item := range items {
		if _, isLabel := item.(asm.Label); isLabel {
			starts[i] = true
		}
		if ins, isIns := item.(asm.Instruction); isIns && isBranchMnemonic(ins.Mnemonic) && ins.Mnemonic != "bl" && ins.Mnemonic != "blr" && i+1 <= n {
			starts[i+1] = true
		}
	}
	var blocks [][2]int // [start, end)
	for i := 0; i < n; {
		j := i + 1
		for j < n && !starts[j] {
			j++
		}
		blocks = append(blocks, [2]int{i, j})
		i = j
	}
	blockOf := make([]int, n)
	for b, blk := range blocks {
		for i := blk[0]; i < blk[1]; i++ {
			blockOf[i] = b
		}
	}
	// Successors of a block: the fall-through block unless the block ends
	// in an unconditional branch, a return, or a trap; the branch target.
	succ := make([][]int, len(blocks))
	for b, blk := range blocks {
		last := blk[1] - 1
		fallthrough_ := true
		if ins, isIns := items[last].(asm.Instruction); isIns {
			switch ins.Mnemonic {
			case "b":
				fallthrough_ = ins.Cond != ""
			case "ret", "brk", "eret", "br":
				fallthrough_ = false
			}
			if isBranchMnemonic(ins.Mnemonic) && ins.Mnemonic != "bl" && ins.Mnemonic != "blr" && ins.Mnemonic != "ret" {
				if target := branchTarget(ins); target != "" {
					if at, known := labelAt[target]; known {
						succ[b] = append(succ[b], blockOf[at])
					}
				}
			}
		}
		if fallthrough_ && b+1 < len(blocks) {
			succ[b] = append(succ[b], b+1)
		}
	}
	const all = uint32(1<<31 - 1)
	useMask := func(ins asm.Instruction) uint32 {
		var m uint32
		for r := 0; r <= 30; r++ {
			if readsGeneral(ins, r) {
				m |= 1 << uint(r)
			}
		}
		return m
	}
	defMask := func(ins asm.Instruction) uint32 {
		var m uint32
		switch ins.Mnemonic {
		case "bl", "blr":
			// A call clobbers the caller-saved general registers.
			for r := 0; r <= 18; r++ {
				m |= 1 << uint(r)
			}
			return m | 1<<30
		}
		for _, r := range writtenGeneral(ins) {
			if r >= 0 && r <= 30 {
				m |= 1 << uint(r)
			}
		}
		return m
	}
	uses := make([]uint32, n)
	defs := make([]uint32, n)
	for i, item := range items {
		if ins, isIns := item.(asm.Instruction); isIns {
			uses[i], defs[i] = useMask(ins), defMask(ins)
		}
	}
	liveIn := make([]uint32, len(blocks))
	liveOut := make([]uint32, len(blocks))
	for changed := true; changed; {
		changed = false
		for b := len(blocks) - 1; b >= 0; b-- {
			var out uint32
			for _, s := range succ[b] {
				out |= liveIn[s]
			}
			if last := blocks[b][1] - 1; last >= 0 {
				if ins, isIns := items[last].(asm.Instruction); isIns && ins.Mnemonic == "ret" {
					// The result registers and the restored callee-saved
					// registers leave through the return.
					out |= 1 | 1<<1 | 1<<8
					for r := 19; r <= 30; r++ {
						out |= 1 << uint(r)
					}
				}
			}
			in := out
			for i := blocks[b][1] - 1; i >= blocks[b][0]; i-- {
				in = (in &^ defs[i]) | uses[i]
			}
			if in != liveIn[b] || out != liveOut[b] {
				liveIn[b], liveOut[b] = in, out
				changed = true
			}
		}
	}
	_ = all
	after := make([]uint32, n)
	for b, blk := range blocks {
		live := liveOut[b]
		for i := blk[1] - 1; i >= blk[0]; i-- {
			after[i] = live
			live = (live &^ defs[i]) | uses[i]
		}
	}
	return after
}

// cleanupOnce applies the rules once, left to right.
func cleanupOnce(items []asm.Item, zeroStores bool) ([]asm.Item, int) {
	after := liveAfter(items)
	dead := func(i int, reg int) bool { return after[i]&(1<<uint(reg)) == 0 }
	out := make([]asm.Item, 0, len(items))
	removed := 0
	for i := 0; i < len(items); i++ {
		ins, isIns := items[i].(asm.Instruction)
		if !isIns {
			out = append(out, items[i])
			continue
		}
		if i+2 < len(items) {
			second, secondOK := items[i+1].(asm.Instruction)
			third, thirdOK := items[i+2].(asm.Instruction)
			if secondOK && thirdOK {
				// Rule 5: forward the data source and erase a materialized zero
				// index only when neither temporary survives the store.
				if folded, dataTmp, indexTmp, ok := foldZeroIndexStore(ins, second, third); ok &&
					dead(i+2, dataTmp) && dead(i+2, indexTmp) {
					out = append(out, folded)
					removed += 2
					i += 2
					continue
				}
			}
		}
		var next asm.Instruction
		hasNext := false
		if i+1 < len(items) {
			next, hasNext = items[i+1].(asm.Instruction)
		}
		// Rule 4: a register moved onto itself.
		if d, s, isMove := isRegisterMove(ins); isMove && d.Num == s.Num {
			removed++
			continue
		}
		// Rule 3: a branch to a label that follows it, through a run of
		// labels with no instruction between (`b endif` before `else:`
		// `endif:` — an arm's empty alternative).
		if ins.Mnemonic == "b" {
			target := branchTarget(ins)
			fallsThrough := false
			for j := i + 1; j < len(items); j++ {
				l, isLabel := items[j].(asm.Label)
				if !isLabel {
					break
				}
				if l.Name == target {
					fallsThrough = true
					break
				}
			}
			if fallsThrough {
				removed++
				continue
			}
		}
		if i+2 < len(items) {
			second, secondOK := items[i+1].(asm.Instruction)
			third, thirdOK := items[i+2].(asm.Instruction)
			if secondOK && thirdOK {
				// Rule 7: a bit tested by mask, compare, and branch —
				// `and xT, xS, #(1<<k); cmp xT, #0; b.ne L` — is `tbnz xS,
				// #k, L` (`b.eq`: `tbz`) when xT is dead after the branch,
				// and the branch's target does not read the flags the
				// compare set (a block starting with a conditional branch
				// reuses them). The walkers test a descriptor's valid bit
				// this way at every level.
				if fused, ok := fuseBitTest(ins, second, third); ok && dead(i+2, fusedRegister(ins)) && !blockReadsFlags(items, branchTarget(third)) {
					out = append(out, fused)
					removed += 2
					i += 2
					continue
				}
			}
		}
		if hasNext {
			// Rule 6: a Bool materialized only to be branched on. `cset wN,
			// cond; cbz wN, L` with wN dead after the branch is `b.!cond L`
			// (`cbnz`: `b.cond L`): the status conditionals of the OS page
			// walkers, `r = oor ? u8(0) | r`, spent the cset and a register
			// per test. The flags are the compare's still — nothing between
			// the two instructions.
			if fused, ok := fuseFlagBranch(ins, next); ok && dead(i+1, fusedRegister(ins)) {
				out = append(out, fused)
				removed++
				i++
				continue
			}
			// Rule 8: a zero moved into a register only to be stored is the
			// zero register stored (`mov x9, xzr; str x9, [x14]`), the
			// scheduler's independent instructions between them kept.
			if d, s, isMove := isRegisterOrZeroMove(ins); isMove && zeroStores && s.ZeroRegister() {
				if at, store, ok := zeroStoreAfter(items, i, d); ok && dead(at, d.Num) {
					for j := i + 1; j < at; j++ {
						out = append(out, items[j])
					}
					out = append(out, store)
					removed++
					i = at
					continue
				}
			}
			// Rule 1: a copy read once by the next instruction.
			if d, s, isMove := isRegisterMove(ins); isMove && readsGeneral(next, d.Num) && !isCallOrReturn(next) && !writesBackTo(next, d.Num) &&
				(writesGeneral(next, d.Num) || dead(i+1, d.Num)) &&
				(d.Class == asm.ClassX || readsOnlyAsClass(next, d.Num, asm.ClassW)) {
				renamed := renameReads(next, d.Num, s)
				if !sameInstruction(renamed, next) {
					out = append(out, renamed)
					removed++
					i++
					continue
				}
			}
			// Rule 2: a definition copied once to its destination.
			if d, s, isMove := isRegisterMove(next); isMove && retargetable[ins.Mnemonic] && !strings.HasPrefix(ins.Mnemonic, "st") && len(ins.Operands) > 0 && dead(i+1, s.Num) {
				if dst, isReg := generalReg(ins.Operands[0]); isReg && dst.Num == s.Num && dst.Class == d.Class && len(writtenGeneral(ins)) == 1 && !readsGeneral(ins, s.Num) {
					renamed := ins
					renamed.Operands = append([]asm.Operand(nil), ins.Operands...)
					renamed.Operands[0] = d
					out = append(out, renamed)
					removed++
					i++
					continue
				}
			}
		}
		out = append(out, ins)
	}
	return out, removed
}

// fuseBitTest reads `and xT, xS, #(1<<k); cmp xT, #0; b.cond L` with cond
// ne or eq and returns `tbnz xS, #k, L` or `tbz xS, #k, L`.
func fuseBitTest(mask, compare, branch asm.Instruction) (asm.Instruction, bool) {
	if mask.Mnemonic != "and" || mask.Cond != "" || len(mask.Operands) != 3 || compare.Mnemonic != "cmp" || len(compare.Operands) != 2 || branch.Mnemonic != "b." || len(branch.Operands) != 1 {
		return asm.Instruction{}, false
	}
	dst, dstOK := generalReg(mask.Operands[0])
	src, srcOK := generalReg(mask.Operands[1])
	bit, bitOK := mask.Operands[2].(asm.Immediate)
	tested, testedOK := generalReg(compare.Operands[0])
	zero, zeroOK := compare.Operands[1].(asm.Immediate)
	target, targetOK := branch.Operands[0].(asm.Symbol)
	if !dstOK || !srcOK || !bitOK || !testedOK || !zeroOK || !targetOK || bit.Shift != 0 || zero.Value != 0 || zero.Shift != 0 {
		return asm.Instruction{}, false
	}
	if dst.Num != tested.Num || dst.Class != tested.Class || dst.Class != src.Class || dst.Num == src.Num || src.ZeroRegister() {
		return asm.Instruction{}, false
	}
	v := uint64(bit.Value)
	if v == 0 || v&(v-1) != 0 {
		return asm.Instruction{}, false
	}
	k := int64(bits.TrailingZeros64(v))
	if dst.Class == asm.ClassW && k >= 32 {
		return asm.Instruction{}, false
	}
	mnemonic := ""
	switch branch.Cond {
	case "ne":
		mnemonic = "tbnz"
	case "eq":
		mnemonic = "tbz"
	default:
		return asm.Instruction{}, false
	}
	// The encoding reads a bit below 32 from the W register, above from X.
	bitReg := xr(src.Num)
	if k < 32 {
		bitReg = wr(src.Num)
	}
	return asm.Instruction{Mnemonic: mnemonic, Operands: []asm.Operand{bitReg, asm.Immediate{Value: k}, target}, Line: branch.Line}, true
}

// A Bool materialized only to be selected on (`cset wT, cond; …; cmp wT,
// #0; csel …, ne`) is deliberately not fused into a select on the cset's
// condition: the fused shape lands the verifier's decision of the OS
// walker `translate`'s status cell past its node budget (the plain form
// decides at 1.9M nodes, the fused one not at all under the escalated
// budget), and the stage2 walkers gain nothing from it.

// blockReadsFlags reports a label whose block begins with a conditional
// branch: the flags reach it from a compare before a branch to it, which a
// fused bit test would no longer set.
func blockReadsFlags(items []asm.Item, label string) bool {
	for i, item := range items {
		if l, isLabel := item.(asm.Label); isLabel && l.Name == label {
			for j := i + 1; j < len(items); j++ {
				switch it := items[j].(type) {
				case asm.Label:
					continue
				case asm.Instruction:
					return it.Mnemonic == "b." || it.Mnemonic == "cset" || it.Mnemonic == "csel" || it.Mnemonic == "csinc" || it.Mnemonic == "cinc"
				}
			}
			return false
		}
	}
	return false
}

// zeroStoreAfter finds, within a few items after the zero move at i, the
// store of the moved register — `str wD/xD, [mem]` with mem not reading D
// — with only instructions that neither mention D nor touch memory
// between, and returns the store rewritten to store the zero register.
func zeroStoreAfter(items []asm.Item, i int, d asm.Register) (int, asm.Instruction, bool) {
	for j := i + 1; j < len(items) && j <= i+4; j++ {
		ins, isIns := items[j].(asm.Instruction)
		if !isIns {
			return 0, asm.Instruction{}, false
		}
		if strings.HasPrefix(ins.Mnemonic, "str") && len(ins.Operands) == 2 {
			src, isReg := ins.Operands[0].(asm.Register)
			mem, isMem := ins.Operands[1].(asm.Memory)
			if isReg && isMem && src.Num == d.Num && src.Class == d.Class && !memoryMentions(mem, d.Num) {
				zero := wr(31)
				if d.Class == asm.ClassX {
					zero = xr(31)
				}
				renamed := ins
				renamed.Operands = []asm.Operand{zero, mem}
				return j, renamed, true
			}
			return 0, asm.Instruction{}, false
		}
		if readsGeneral(ins, d.Num) || writesGeneral(ins, d.Num) || strings.HasPrefix(ins.Mnemonic, "ld") || strings.HasPrefix(ins.Mnemonic, "st") || isBranchMnemonic(ins.Mnemonic) {
			return 0, asm.Instruction{}, false
		}
	}
	return 0, asm.Instruction{}, false
}

// memoryMentions reports a memory operand reading the register.
func memoryMentions(mem asm.Memory, reg int) bool {
	if mem.Base.Num == reg && !mem.Base.ZeroRegister() {
		return true
	}
	return mem.Index != nil && mem.Index.Num == reg
}

// invertedCondition is the AArch64 condition code that holds exactly when
// the given one does not.
var invertedCondition = map[string]string{
	"eq": "ne", "ne": "eq", "hs": "lo", "lo": "hs", "cs": "cc", "cc": "cs",
	"hi": "ls", "ls": "hi", "ge": "lt", "lt": "ge", "gt": "le", "le": "gt",
	"mi": "pl", "pl": "mi", "vs": "vc", "vc": "vs",
}

// fuseFlagBranch reads `cset wN, cond` followed by `cbz wN, L` or `cbnz
// wN, L` and returns the conditional branch on the flags that decides the
// same: `b.!cond L` for cbz (taken when the Bool is zero, the condition
// false), `b.cond L` for cbnz. The caller checks that wN is dead after
// the branch.
func fuseFlagBranch(set, branch asm.Instruction) (asm.Instruction, bool) {
	if set.Mnemonic != "cset" || set.Cond != "" || len(set.Operands) != 2 || len(branch.Operands) != 2 {
		return asm.Instruction{}, false
	}
	if branch.Mnemonic != "cbz" && branch.Mnemonic != "cbnz" {
		return asm.Instruction{}, false
	}
	dst, dstOK := generalReg(set.Operands[0])
	cond, condOK := set.Operands[1].(asm.Condition)
	tested, testedOK := generalReg(branch.Operands[0])
	target, targetOK := branch.Operands[1].(asm.Symbol)
	if !dstOK || !condOK || !testedOK || !targetOK || dst.Num != tested.Num || dst.Class != asm.ClassW || tested.Class != asm.ClassW {
		return asm.Instruction{}, false
	}
	code := cond.Code
	if branch.Mnemonic == "cbz" {
		inverted, known := invertedCondition[code]
		if !known {
			return asm.Instruction{}, false
		}
		code = inverted
	} else if _, known := invertedCondition[code]; !known {
		return asm.Instruction{}, false
	}
	return asm.Instruction{Mnemonic: "b.", Cond: code, Operands: []asm.Operand{target}, Line: branch.Line}, true
}

// fusedRegister is the Bool register a fused `cset` wrote.
func fusedRegister(set asm.Instruction) int {
	if r, ok := generalReg(set.Operands[0]); ok {
		return r.Num
	}
	return -1
}

func isCallOrReturn(ins asm.Instruction) bool {
	switch ins.Mnemonic {
	case "bl", "blr", "ret", "br":
		return true
	}
	return false
}

// sameInstruction compares two instructions by their spelling.
func sameInstruction(a, b asm.Instruction) bool {
	return Describe(&asm.Function{Items: []asm.Item{a}}) == Describe(&asm.Function{Items: []asm.Item{b}})
}

// CleanedCopies reports how many instructions the late cleanup removed
// from a lowering under Lane.Cleanup.
func CleanedCopies(fn *asm.Function) int { return cleanedCopies[fn] }

var cleanedCopies = map[*asm.Function]int{}
