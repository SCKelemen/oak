package nativegen

// Constant branch folding (docs/spec/94-assembler.md §9, the late cleanup):
// a forward constant propagation over the item list — registers written by
// `movz`, `movk`, or a move from the zero register carry known constants
// inside a block, any other write forgets them, and a label meets its
// predecessors (a register is known at a label when every predecessor
// knows the same value) — folds `cmp wR, #k; b.cond L` where R is known
// (taken: `b L`; not taken: both instructions go) and threads `b L` whose
// target block begins with such a compare that R's value on that edge
// decides, then removes blocks nothing reaches. The OS page walkers keep a
// status byte `r` that each level compares with 1 after conditionally
// clearing it; on the path that cleared it the compare is decided, and on
// the path that did not, `r` still holds the 1 it was set to.

import "github.com/SCKelemen/oak/asm"

// constPassLimit bounds the fold-and-thread iterations.
const constPassLimit = 8

// registerConsts is the known constants of the general registers.
type registerConsts map[int]uint64

func (k registerConsts) copy() registerConsts {
	out := make(registerConsts, len(k))
	for r, v := range k {
		out[r] = v
	}
	return out
}

// meet keeps the constants two states agree on; nil (unknown everything)
// meets as the other state's absence: an unreached predecessor.
func meetConsts(a, b registerConsts, aKnown, bKnown bool) (registerConsts, bool) {
	if !aKnown {
		return b, bKnown
	}
	if !bKnown {
		return a, true
	}
	out := registerConsts{}
	for r, v := range a {
		if w, ok := b[r]; ok && w == v {
			out[r] = v
		}
	}
	return out, true
}

// constantWrite reads an instruction that leaves a register a known
// constant: `movz wR, #imm[, lsl #s]`, `movk wR, #imm, lsl #s` over a known
// register, `mov wR, wzr`. Any other instruction writing R forgets it.
func stepConsts(state registerConsts, ins asm.Instruction) {
	switch ins.Mnemonic {
	case "movz":
		if dst, ok := generalReg(ins.Operands[0]); ok && len(ins.Operands) == 2 {
			if imm, isImm := ins.Operands[1].(asm.Immediate); isImm && imm.Value >= 0 {
				state[dst.Num] = uint64(imm.Value) << uint(imm.Shift)
				return
			}
		}
	case "movk":
		if dst, ok := generalReg(ins.Operands[0]); ok && len(ins.Operands) == 2 {
			if imm, isImm := ins.Operands[1].(asm.Immediate); isImm && imm.Value >= 0 {
				if prev, known := state[dst.Num]; known {
					state[dst.Num] = prev&^(uint64(0xffff)<<uint(imm.Shift)) | uint64(imm.Value)<<uint(imm.Shift)
					return
				}
			}
		}
	case "mov":
		if dst, src, ok := isRegisterOrZeroMove(ins); ok && src.ZeroRegister() {
			state[dst.Num] = 0
			return
		}
		if dst, src, ok := isRegisterMove(ins); ok {
			if v, known := state[src.Num]; known && dst.Class == src.Class {
				state[dst.Num] = v
				return
			}
		}
	}
	for _, r := range writtenGeneral(ins) {
		delete(state, r)
	}
	if ins.Mnemonic == "bl" || ins.Mnemonic == "blr" {
		for r := 0; r <= 18; r++ {
			delete(state, r)
		}
		delete(state, 30)
	}
}

// decidedCompare reads `cmp wR, #k` followed by `b.cond L` with R known
// and returns whether the branch is taken.
func decidedCompare(state registerConsts, compare, branch asm.Instruction) (taken bool, ok bool) {
	if compare.Mnemonic != "cmp" || len(compare.Operands) != 2 || branch.Mnemonic != "b." || len(branch.Operands) != 1 {
		return false, false
	}
	reg, regOK := generalReg(compare.Operands[0])
	imm, immOK := compare.Operands[1].(asm.Immediate)
	if !regOK || !immOK || reg.ZeroRegister() || imm.Value < 0 {
		return false, false
	}
	v, known := state[reg.Num]
	if !known {
		return false, false
	}
	width := 64
	if reg.Class == asm.ClassW {
		width = 32
		v &= 0xffffffff
	}
	k := uint64(imm.Value) << uint(imm.Shift)
	return conditionHolds(branch.Cond, v, k, width)
}

// conditionHolds evaluates an AArch64 condition over two constants
// compared as `cmp a, b`.
func conditionHolds(cond string, a, b uint64, width int) (bool, bool) {
	sa, sb := int64(a), int64(b)
	if width == 32 {
		sa, sb = int64(int32(uint32(a))), int64(int32(uint32(b)))
	}
	switch cond {
	case "eq":
		return a == b, true
	case "ne":
		return a != b, true
	case "hs", "cs":
		return a >= b, true
	case "lo", "cc":
		return a < b, true
	case "hi":
		return a > b, true
	case "ls":
		return a <= b, true
	case "ge":
		return sa >= sb, true
	case "lt":
		return sa < sb, true
	case "gt":
		return sa > sb, true
	case "le":
		return sa <= sb, true
	}
	return false, false
}

// foldConstantBranches runs the propagation and the rewrites to a fixpoint
// and reports the instructions removed.
func foldConstantBranches(items []asm.Item) ([]asm.Item, int) {
	removed := 0
	for pass := 0; pass < constPassLimit; pass++ {
		next, n := foldConstantBranchesOnce(items)
		if n == 0 {
			return items, removed
		}
		items, removed = next, removed+n
	}
	return items, removed
}

func foldConstantBranchesOnce(items []asm.Item) ([]asm.Item, int) {
	succ, ok := itemSuccessors(items)
	if !ok {
		return items, 0
	}
	n := len(items)
	labelAt := map[string]int{}
	for i, item := range items {
		if l, isLabel := item.(asm.Label); isLabel {
			labelAt[l.Name] = i
		}
	}
	// Predecessors, from the successor lists.
	pred := make([][]int, n)
	for i, ss := range succ {
		for _, s := range ss {
			pred[s] = append(pred[s], i)
		}
	}
	// in[i] is the state before item i; out[i] after. Iterated to a fixpoint
	// over the acyclic and cyclic parts alike (a loop back edge forgets
	// what its body changes).
	in := make([]registerConsts, n)
	out := make([]registerConsts, n)
	reached := make([]bool, n)
	if n > 0 {
		in[0], reached[0] = registerConsts{}, true
	}
	for iter := 0; iter < n+2; iter++ {
		changed := false
		for i := 0; i < n; i++ {
			var state registerConsts
			known := false
			if i == 0 {
				state, known = registerConsts{}, true
			}
			for _, p := range pred[i] {
				state, known = meetConsts(state, out[p], known, reached[p])
			}
			if !known {
				continue
			}
			if !reached[i] || !sameConsts(in[i], state) {
				in[i], reached[i] = state, true
				changed = true
			}
			after := state.copy()
			if ins, isIns := items[i].(asm.Instruction); isIns {
				stepConsts(after, ins)
			}
			out[i] = after
		}
		if !changed {
			break
		}
	}
	// Rewrites over a copy: decided compares first, then threaded jumps.
	// replace holds the items standing in for one item (a threaded jump
	// carries the target block's leading moves with it).
	result := append([]asm.Item(nil), items...)
	replace := map[int][]asm.Item{}
	remove := make([]bool, n)
	removed := 0
	for i := 0; i+1 < n; i++ {
		compare, okC := items[i].(asm.Instruction)
		branch, okB := items[i+1].(asm.Instruction)
		if !okC || !okB || !reached[i] || remove[i] {
			continue
		}
		taken, decided := decidedCompare(in[i], compare, branch)
		if !decided {
			continue
		}
		// The compare's flags must reach no reader: the fall-through and
		// the target begin with their own compares in the shapes folded.
		if !flagsDeadFrom(items, succ, i+2) || (taken && !flagsDeadFrom(items, succ, labelAt[branchTarget(branch)])) {
			continue
		}
		remove[i] = true
		removed++
		if taken {
			result[i+1] = asm.Instruction{Mnemonic: "b", Operands: branch.Operands, Line: branch.Line}
		} else {
			remove[i+1] = true
			removed++
		}
	}
	if removed == 0 {
		// Thread `b L` where L's block begins with a compare the edge's
		// state decides.
		for i, item := range items {
			ins, isIns := item.(asm.Instruction)
			if !isIns || ins.Mnemonic != "b" || ins.Cond != "" || !reached[i] {
				continue
			}
			at, found := labelAt[branchTarget(ins)]
			if !found {
				continue
			}
			// The target block's leading moves and constants are stepped
			// through on the edge's state (`mov w4, w9; cmp w4, #1`).
			// Threading past them copies them onto the edge, so a merge
			// move the target performs (`mov w4, w9`) still happens.
			edge := out[i].copy()
			var leads []asm.Item
			j := at
			for j < n {
				if _, isLabel := items[j].(asm.Label); isLabel {
					j++
					continue
				}
				lead, isIns := items[j].(asm.Instruction)
				if !isIns || (lead.Mnemonic != "mov" && lead.Mnemonic != "movz" && lead.Mnemonic != "movk") {
					break
				}
				stepConsts(edge, lead)
				leads = append(leads, lead)
				j++
			}
			if j+1 >= n {
				continue
			}
			compare, okC := items[j].(asm.Instruction)
			branch, okB := items[j+1].(asm.Instruction)
			if !okC || !okB {
				continue
			}
			taken, decided := decidedCompare(edge, compare, branch)
			if !decided || !taken {
				// A not-taken thread would need a label after the branch;
				// the shapes folded thread onto the taken side and leave
				// the fall-through to the decided-compare rule once its
				// other predecessors are gone.
				continue
			}
			replace[i] = append(append([]asm.Item(nil), leads...), asm.Instruction{Mnemonic: "b", Operands: branch.Operands, Line: ins.Line})
			removed++ // counted as a rewrite so the caller iterates; nothing deleted
		}
		if removed == 0 {
			return items, 0
		}
		// Count threaded jumps as changes, not removals, for the caller's
		// fixpoint; the removal count below is what actually went.
		out := make([]asm.Item, 0, n)
		for i := range result {
			if rep, isRep := replace[i]; isRep {
				out = append(out, rep...)
			} else if !remove[i] {
				out = append(out, result[i])
			}
		}
		return removeUnreachableBlocks(out), removed
	}
	compact := make([]asm.Item, 0, n)
	for i := range result {
		if !remove[i] {
			compact = append(compact, result[i])
		}
	}
	return removeUnreachableBlocks(compact), removed
}

// removeUnreachableBlocks drops a labeled block that no branch targets and
// no instruction falls into (the previous item is an unconditional
// transfer), keeping the lowering's own labels (head_, ret_, trap_).
func removeUnreachableBlocks(items []asm.Item) []asm.Item {
	for {
		targets := map[string]bool{}
		for _, item := range items {
			if ins, ok := item.(asm.Instruction); ok {
				if t := branchTarget(ins); t != "" {
					targets[t] = true
				}
			}
		}
		removedAny := false
		out := make([]asm.Item, 0, len(items))
		for i := 0; i < len(items); i++ {
			l, isLabel := items[i].(asm.Label)
			if !isLabel || targets[l.Name] || i == 0 || protectedLabel(l.Name) {
				out = append(out, items[i])
				continue
			}
			prev, prevIns := items[i-1].(asm.Instruction)
			if !prevIns || !unconditionalTransfer(prev) {
				out = append(out, items[i])
				continue
			}
			// Drop the label and its instructions up to the next label.
			j := i + 1
			for j < len(items) {
				if _, nextLabel := items[j].(asm.Label); nextLabel {
					break
				}
				j++
			}
			if j == i+1 {
				// An empty label run: the label alone goes.
				removedAny = true
				continue
			}
			removedAny = true
			i = j - 1
		}
		items = out
		if !removedAny {
			return items
		}
	}
}

func protectedLabel(name string) bool {
	for _, prefix := range []string{"head_", "ret_", "trap_", "loop", "optir_b0"} {
		if len(name) >= len(prefix) && name[:len(prefix)] == prefix {
			return true
		}
	}
	return false
}

func unconditionalTransfer(ins asm.Instruction) bool {
	switch ins.Mnemonic {
	case "b":
		return ins.Cond == ""
	case "ret", "brk", "eret", "br":
		return true
	}
	return false
}

func sameConsts(a, b registerConsts) bool {
	if len(a) != len(b) {
		return false
	}
	for r, v := range a {
		if w, ok := b[r]; !ok || w != v {
			return false
		}
	}
	return true
}
