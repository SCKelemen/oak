package nativegen

import (
	"strings"

	"github.com/SCKelemen/oak/asm"
)

// Late copy and branch cleanup (docs/spec/94-assembler.md §9 "Late
// cleanup"; docs/notes/optimizer-search-2026-09.md §11 "Machine"). The
// lowering spells a value's path through a scratch register wherever an
// expression's result meets the place it is used — `mov w10, w24; cbz w10,
// else`, `movz w10, #1; mov w9, w10`, `mov x10, x12; mov x22, x10` — and
// a branch to the label that follows it when an arm's tail is empty. The
// verifier proves each cleaned body equal to its Oak text as it proves the
// uncleaned one; the pass changes machine shape only (Lane.Cleanup,
// TransformCleanup), and the compiler keeps the uncleaned lowering where
// the checker or the verifier refuses the cleaned form.
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
//
// The pass runs to a fixpoint; cleanedCopies counts the instructions it
// removed.

// cleanupItems applies the rules to a function's items and reports how
// many instructions it removed.
func cleanupItems(items []asm.Item) ([]asm.Item, int) {
	removed := 0
	for {
		next, n := cleanupOnce(items)
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
			case "b", "ret", "brk", "eret", "br":
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
func cleanupOnce(items []asm.Item) ([]asm.Item, int) {
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
		// Rule 3: a branch to the label that follows it.
		if ins.Mnemonic == "b" && i+1 < len(items) {
			if l, isLabel := items[i+1].(asm.Label); isLabel && branchTarget(ins) == l.Name {
				removed++
				continue
			}
		}
		if hasNext {
			// Rule 1: a copy read once by the next instruction.
			if d, s, isMove := isRegisterMove(ins); isMove && readsGeneral(next, d.Num) && !isCallOrReturn(next) &&
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
