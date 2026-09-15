package nativegen

import "github.com/SCKelemen/oak/asm"

// Bottom-tested loops (docs/spec/94-assembler.md §9 "Bottom-tested
// loops"): a pass over the emitted items after the loop-invariant pass. A
// loop in the generator's shape — the `loop_N` header, its exit tests to
// `done_M`, the body, the unconditional back edge — whose exit tests are a
// run of compares and conditional branches to the exit label (a
// conjunction of simple tests; no load, no guard, no setup) is rotated:
// the run is copied before the header as the entry test, moved to the
// tail with its last branch complemented and aimed at the header as the
// back edge, and the unconditional jump dropped — one branch an iteration
// where the top-tested loop paid its tests, an exit, and a jump. The
// verifier recognizes the shape (asm/loops.go tailLoopShape): the tail run
// is the entry run but for the last branch, and nothing else reaches the
// header.

// rotateLoops rotates every rotatable loop, innermost first; the items
// and the count.
func rotateLoops(items []asm.Item) ([]asm.Item, int) {
	rotated := 0
	done := map[string]bool{}
	for {
		var next *invariantLoop
		for _, loop := range findGeneratorLoops(items) {
			if !done[loop.name] {
				l := loop
				next = &l
				break
			}
		}
		if next == nil {
			return items, rotated
		}
		done[next.name] = true
		if out, ok := rotateLoop(items, *next); ok {
			items = out
			rotated++
		}
	}
}

// rotatedInverse complements a condition code for the tail's back edge.
var rotatedInverse = map[string]string{
	"eq": "ne", "ne": "eq", "hs": "lo", "cs": "cc", "lo": "hs", "cc": "cs", "mi": "pl", "pl": "mi",
	"vs": "vc", "vc": "vs", "hi": "ls", "ls": "hi", "ge": "lt", "lt": "ge", "gt": "le", "le": "gt",
}

// rotateLoop rotates one loop when its header tests are a plain run.
func rotateLoop(items []asm.Item, loop invariantLoop) ([]asm.Item, bool) {
	header, back := loop.header, loop.back
	labels := map[string]int{}
	for i, item := range items {
		if l, isLabel := item.(asm.Label); isLabel {
			labels[l.Name] = i
		}
	}
	// The run: compares and conditional branches to one exit label past
	// the back edge, ending in a branch.
	exit := ""
	run := header + 1
	lastBranch := -1
	for run < back {
		ins, isIns := items[run].(asm.Instruction)
		if !isIns {
			break
		}
		if ins.Mnemonic == "cmp" {
			run++
			continue
		}
		if ins.Mnemonic == "b." || ins.Mnemonic == "cbz" || ins.Mnemonic == "cbnz" {
			sym, isSym := ins.Operands[len(ins.Operands)-1].(asm.Symbol)
			target, isLabel := labels[sym.Name]
			if !isSym || !isLabel || target <= back || (exit != "" && sym.Name != exit) {
				break
			}
			exit = sym.Name
			lastBranch = run
			run++
			continue
		}
		break
	}
	if lastBranch < 0 {
		return nil, false // no test run
	}
	// The run ends at its last exit branch: a compare after it is the
	// body's (a guard's `cmp wI, #64; b.hs trap`, first in a body whose
	// invariants were hoisted).
	run = lastBranch + 1
	if run >= back {
		return nil, false // no body
	}
	// The run must be the whole exit test: a later branch to the exit
	// label is a test behind a setup instruction (`sub wT, wL, #4; cmp wI,
	// wT; b.hi done`), which the verifier's tail shape does not hold.
	for i := run; i < back; i++ {
		ins, isIns := items[i].(asm.Instruction)
		if !isIns || len(ins.Operands) == 0 {
			continue
		}
		if sym, isSym := ins.Operands[len(ins.Operands)-1].(asm.Symbol); isSym && sym.Name == exit {
			return nil, false
		}
	}
	// Nothing but the back edge reaches the header.
	for i, item := range items {
		ins, isIns := item.(asm.Instruction)
		if !isIns || i == back || len(ins.Operands) == 0 {
			continue
		}
		if sym, isSym := ins.Operands[len(ins.Operands)-1].(asm.Symbol); isSym && sym.Name == loop.name {
			return nil, false
		}
	}
	var out []asm.Item
	out = append(out, items[:header]...)
	out = append(out, items[header+1:run]...) // the entry test
	out = append(out, items[header])          // the header label
	out = append(out, items[run:back]...)     // the body
	for i := header + 1; i < run; i++ {       // the tail test
		ins := items[i].(asm.Instruction)
		if i == lastBranch {
			operands := append([]asm.Operand(nil), ins.Operands...)
			operands[len(operands)-1] = asm.Symbol{Name: loop.name}
			ins.Operands = operands
			switch ins.Mnemonic {
			case "b.":
				ins.Cond = rotatedInverse[ins.Cond]
			case "cbz":
				ins.Mnemonic = "cbnz"
			case "cbnz":
				ins.Mnemonic = "cbz"
			}
		}
		out = append(out, ins)
	}
	out = append(out, items[back+1:]...)
	return out, true
}
