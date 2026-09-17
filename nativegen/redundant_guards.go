package nativegen

import "github.com/SCKelemen/oak/asm"

// elideRedundantGuards removes a repeated span guard only when an identical
// earlier guard dominates it and neither operand can change on any path
// between them. The first guard still traps before every effect on invalid
// inputs; every path reaching the repeated guard has therefore established
// the same unsigned relation already. Flags must be dead after the removed
// pair. Calls delimit the optimization, even for callee-saved operands.
//
// This changes no memory operation and grants no checker authority. It is a
// verifier-gated candidate; a body that does not prove keeps all guards.
func elideRedundantGuards(items []asm.Item) ([]asm.Item, int) {
	succ, ok := itemSuccessors(items)
	if !ok || len(items) == 0 {
		return items, 0
	}
	type site struct {
		at          int
		left, right asm.Register
		target      string
	}
	var retained []site
	remove := make([]bool, len(items))
	removed := 0
	for i := 0; i+1 < len(items); i++ {
		left, right, target, ok := redundantGuardAt(items, i)
		if !ok {
			continue
		}
		current := site{at: i, left: left, right: right, target: target}
		for _, prior := range retained {
			if prior.target != current.target || prior.left.Num != left.Num || prior.right.Num != right.Num ||
				prior.left.Class != left.Class || prior.right.Class != right.Class {
				continue
			}
			if !itemDominates(succ, prior.at, i) || !guardOperandsStable(items, succ, prior.at+2, i, left.Num, right.Num) ||
				!flagsDeadFrom(items, succ, i+2) {
				continue
			}
			remove[i], remove[i+1] = true, true
			removed++
			break
		}
		if !remove[i] {
			retained = append(retained, current)
		}
	}
	if removed == 0 {
		return items, 0
	}
	out := make([]asm.Item, 0, len(items)-2*removed)
	for i, item := range items {
		if !remove[i] {
			out = append(out, item)
		}
	}
	return out, removed
}

func redundantGuardAt(items []asm.Item, i int) (asm.Register, asm.Register, string, bool) {
	cmp, cmpOK := items[i].(asm.Instruction)
	branch, branchOK := items[i+1].(asm.Instruction)
	if !cmpOK || !branchOK || cmp.Mnemonic != "cmp" || cmp.Cond != "" || len(cmp.Operands) != 2 ||
		branch.Mnemonic != "b." || branch.Cond != "hs" || len(branch.Operands) != 1 {
		return asm.Register{}, asm.Register{}, "", false
	}
	left, leftOK := generalReg(cmp.Operands[0])
	right, rightOK := generalReg(cmp.Operands[1])
	target, targetOK := branch.Operands[0].(asm.Symbol)
	if !leftOK || !rightOK || left.Class != asm.ClassW || right.Class != asm.ClassW || left.Num == right.Num || !targetOK {
		return asm.Register{}, asm.Register{}, "", false
	}
	for at, item := range items {
		label, isLabel := item.(asm.Label)
		if !isLabel || label.Name != target.Name || at+1 >= len(items) {
			continue
		}
		trap, isTrap := items[at+1].(asm.Instruction)
		return left, right, target.Name, isTrap && trap.Mnemonic == "brk"
	}
	return asm.Register{}, asm.Register{}, "", false
}

// itemSuccessors constructs the conservative item-level CFG. An unresolved
// direct branch refuses the whole pass; indirect exits have no successor.
func itemSuccessors(items []asm.Item) ([][]int, bool) {
	labels := map[string]int{}
	for i, item := range items {
		if label, ok := item.(asm.Label); ok {
			labels[label.Name] = i
		}
	}
	succ := make([][]int, len(items))
	addFallthrough := func(i int) {
		if i+1 < len(items) {
			succ[i] = append(succ[i], i+1)
		}
	}
	for i, item := range items {
		ins, isIns := item.(asm.Instruction)
		if !isIns {
			addFallthrough(i)
			continue
		}
		target := branchTarget(ins)
		addTarget := func() bool {
			if target == "" {
				return false
			}
			at, found := labels[target]
			if !found {
				return false
			}
			succ[i] = append(succ[i], at)
			return true
		}
		switch ins.Mnemonic {
		case "b":
			if !addTarget() {
				return nil, false
			}
			if ins.Cond != "" {
				addFallthrough(i)
			}
		case "b.", "cbz", "cbnz", "tbz", "tbnz":
			if !addTarget() {
				return nil, false
			}
			addFallthrough(i)
		case "ret", "brk", "eret", "br", "svc":
		case "bl", "blr":
			addFallthrough(i)
		default:
			addFallthrough(i)
		}
	}
	return succ, true
}

func reachableItems(succ [][]int, start, avoid int) []bool {
	seen := make([]bool, len(succ))
	if start < 0 || start >= len(succ) || start == avoid {
		return seen
	}
	work := []int{start}
	for len(work) > 0 {
		i := work[len(work)-1]
		work = work[:len(work)-1]
		if i == avoid || seen[i] {
			continue
		}
		seen[i] = true
		for _, next := range succ[i] {
			if next != avoid && !seen[next] {
				work = append(work, next)
			}
		}
	}
	return seen
}

func itemDominates(succ [][]int, dominator, node int) bool {
	reachable := reachableItems(succ, 0, -1)
	if dominator < 0 || node < 0 || dominator >= len(succ) || node >= len(succ) || !reachable[dominator] || !reachable[node] {
		return false
	}
	return !reachableItems(succ, 0, dominator)[node]
}

func reverseReachable(succ [][]int, target int) []bool {
	reverse := make([][]int, len(succ))
	for from, nexts := range succ {
		for _, to := range nexts {
			reverse[to] = append(reverse[to], from)
		}
	}
	return reachableItems(reverse, target, -1)
}

func guardOperandsStable(items []asm.Item, succ [][]int, start, target, left, right int) bool {
	from := reachableItems(succ, start, -1)
	to := reverseReachable(succ, target)
	if target < 0 || target >= len(items) || !from[target] {
		return false
	}
	for i, item := range items {
		if i == target || !from[i] || !to[i] {
			continue
		}
		ins, isIns := item.(asm.Instruction)
		if !isIns {
			continue
		}
		if ins.Mnemonic == "bl" || ins.Mnemonic == "blr" || writesGeneral(ins, left) || writesGeneral(ins, right) {
			return false
		}
	}
	return true
}

func flagsDeadFrom(items []asm.Item, succ [][]int, start int) bool {
	seen := make([]bool, len(items))
	work := []int{start}
	for len(work) > 0 {
		i := work[len(work)-1]
		work = work[:len(work)-1]
		if i < 0 || i >= len(items) || seen[i] {
			continue
		}
		seen[i] = true
		if ins, isIns := items[i].(asm.Instruction); isIns {
			if asm.ReadsFlags(ins.Mnemonic) {
				return false
			}
			if asm.SetsFlags(ins.Mnemonic) || ins.Mnemonic == "bl" || ins.Mnemonic == "blr" {
				continue
			}
		}
		work = append(work, succ[i]...)
	}
	return true
}

// ElidedRedundantGuards reports how many repeated guard pairs a candidate
// removed. One site is one compare and conditional branch.
func ElidedRedundantGuards(fn *asm.Function) int { return redundantGuards[fn] }

var redundantGuards = map[*asm.Function]int{}
