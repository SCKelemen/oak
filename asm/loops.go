package asm

// Data-dependent loops (docs/spec/94-assembler.md §8, sixth increment).
//
// A loop whose trip count depends on the inputs cannot be unrolled into a
// term. Both executors instead summarize it as a LOOP EVENT — the values
// of the loop-carried variables at the header, fresh symbols standing for
// them on an arbitrary iteration, the continue condition over those
// symbols, and their values after one iteration — and continue past the
// loop on the fresh symbols (the exit sees the header values of the
// exiting iteration). Loops nest: an inner loop met while executing an
// outer body is summarized in place, so the events form a tree recorded
// in creation order with parent links. Verification then has two layers:
//
//   - WITNESSES: both sides are re-executed on concrete inputs, under which
//     every loop becomes counted and unrolls; a disagreement is a definite
//     mismatch with a concrete input.
//   - COUPLING (Oak.AssemblerSemantics.whileFuel_coupled): every event's
//     Oak variables are paired with registers through affine relations
//     that hold at the header; under invariants read off the Oak guards
//     the continue conditions must agree and one iteration must preserve
//     every pairing; then the results after the loops are compared. This
//     is the inductive proof, so the verdict is proven.

import (
	"fmt"
	"math/bits"
	"os"
	"reflect"
	"sort"
	"strconv"
	"strings"
	"sync/atomic"

	"github.com/SCKelemen/oak/ast"
)

// loopShape is a recognized asm loop: a header label, an exit test (`cmp`
// then `b.cond`, or a compare-and-branch), a body branching only forward
// within itself (or through recognized inner loops), and an unconditional
// back edge.
type loopShape struct {
	header, cmp, exit, exitLabel int // the first exit test: cmp is -1 for a compare-and-branch exit
	bodyStart, bodyEnd           int // body instructions are items [bodyStart, bodyEnd)
	// exits are the header's exit branches in order (the first is exit):
	// a conjunctive condition (`len >= 64 && off <= len - 64`, the vector
	// kernels' guard) lowers to several compare-and-branch tests with pure
	// setup instructions between them, every one leaving to exitLabel. The
	// loop continues when none of them is taken.
	exits []int
	// internal are the header's forward branches to labels inside the
	// header (a short-circuit's skip): they fork the header's paths.
	internal []int
	// The exit tests' item range, walked for the continue condition
	// (headerCondition): [header+1, bodyStart) for a top-tested loop; the
	// tail test [bodyEnd, back] for a bottom-tested one, whose body starts
	// right after the header label and whose back edge is the tail test's
	// conditional branch — taken to continue (tail).
	testStart, testEnd int
	tail               bool
	// The entry-only tests' item range [entryStart, entryEnd): compares
	// and branches to the exit label right before the header (before the
	// entry run of a bottom-tested loop) over registers the loop never
	// writes — an invariant conjunct the invariant pass peeled
	// (nativegen/licm.go), decided once. They are exits the executor may
	// meet the loop at, and conjuncts of the continue condition: a test
	// the loop cannot change decides every iteration as it decided the
	// first, so the summary over "entry tests and header tests" is the
	// machine's loop. Empty when entryEnd <= entryStart.
	entryStart, entryEnd int
}

// globalStateValue is a package cell's value in a symbolic state: a write on
// the path, or the declared entry value when the sparse state has no entry.
func globalStateValue(globals map[string]Global, state map[string]*term, name string) (*term, bool) {
	global, declared := globals[name]
	if !declared {
		return nil, false
	}
	if value, written := state[name]; written {
		return value, true
	}
	return cellEntry(name, global), true
}

// differingGlobalState reports the first declared package cell whose value
// differs between two sparse symbolic states. Names are sorted so a rejected
// proof has a deterministic reason.
func differingGlobalState(globals map[string]Global, before, after map[string]*term) (string, bool) {
	names := map[string]bool{}
	for name := range before {
		names[name] = true
	}
	for name := range after {
		names[name] = true
	}
	sorted := make([]string, 0, len(names))
	for name := range names {
		sorted = append(sorted, name)
	}
	sort.Strings(sorted)
	for _, name := range sorted {
		a, aKnown := globalStateValue(globals, before, name)
		b, bKnown := globalStateValue(globals, after, name)
		if !aKnown || !bKnown || !equalTerms(a, b) {
			return name, true
		}
	}
	return "", false
}

// invariantEntryTests finds the entry-only tests before end: the longest
// run of `cmp` and conditional branches to the exit label ending at end,
// beginning at a compare or a compare-and-branch, none reading a register
// written in [header, back]. It returns the run's start (end when none).
func invariantEntryTests(items []Item, labels map[string]int, end, exitLabel, header, back int) int {
	start := end
	for start > 0 {
		instr, isInstr := items[start-1].(Instruction)
		if !isInstr {
			break
		}
		if instr.Mnemonic == "cmp" {
			start--
			continue
		}
		if (instr.Mnemonic == "b." || instr.Mnemonic == "cbz" || instr.Mnemonic == "cbnz") && len(instr.Operands) > 0 {
			if sym, isSym := instr.Operands[len(instr.Operands)-1].(Symbol); isSym && labels[sym.Name] == exitLabel {
				start--
				continue
			}
		}
		break
	}
	// A leading `b.` reads flags the run did not set: it is not the run's.
	for start < end {
		if instr := items[start].(Instruction); instr.Mnemonic == "b." {
			start++
			continue
		}
		break
	}
	// The run ends in a branch (a trailing compare is the header's).
	for start < end {
		if instr := items[end-1].(Instruction); instr.Mnemonic == "cmp" {
			return end // the header's own compare follows: no run
		}
		break
	}
	for at := start; at < end; at++ {
		for _, operand := range items[at].(Instruction).Operands {
			reg, isReg := operand.(Register)
			if !isReg || reg.ZeroRegister() || reg.Class == ClassSP || reg.Class == ClassV {
				continue
			}
			if writesRegisterIn(items, header, back, reg.Num) {
				return end
			}
		}
	}
	return start
}

// writesRegisterIn reports whether an instruction in items [from, to]
// writes general register reg: a destination, a pair load's second, a
// writeback base, or a call's caller-saved clobber.
func writesRegisterIn(items []Item, from, to, reg int) bool {
	for i := from; i <= to && i < len(items); i++ {
		instr, isInstr := items[i].(Instruction)
		if !isInstr || len(instr.Operands) == 0 {
			continue
		}
		if instr.Mnemonic == "bl" || instr.Mnemonic == "blr" {
			if reg <= 18 {
				return true
			}
			continue
		}
		if mem, isMem := instr.Operands[len(instr.Operands)-1].(Memory); isMem && mem.Mode != MemOffset && mem.Base.Num == reg {
			return true
		}
		if instr.Mnemonic == "cmp" || instr.Mnemonic == "cmn" || instr.Mnemonic == "tst" || isConditionalBranch(instr.Mnemonic) || isUnconditionalJump(instr.Mnemonic) || isStoreMnemonic(instr.Mnemonic) {
			continue
		}
		n := 1
		if instr.Mnemonic == "ldp" || instr.Mnemonic == "ldpsw" {
			n = 2
		}
		for k := 0; k < n && k < len(instr.Operands); k++ {
			if dest, isReg := instr.Operands[k].(Register); isReg && dest.Class != ClassV && !dest.ZeroRegister() && dest.Num == reg {
				return true
			}
		}
	}
	return false
}

// findLoops recognizes loops by their back edges, keyed by the exit branch.
// Back edges are met in item order, so an inner loop is recognized before
// the outer body containing it is examined.
func findLoops(items []Item, labels map[string]int) map[int]loopShape {
	return findLoopsIn("", items, labels, nil)
}

// findLoopsIn is findLoops naming the function for the OAK_VERIFY_TRACE
// report of the back edges it does not recognize, and knowing the
// program's functions: a call to one of them, in a header or a body, is
// summarized in place (summarizeCall), so it is not a reason to refuse
// the loop; a call to anything else is.
func findLoopsIn(function string, items []Item, labels map[string]int, callees map[string]*ast.FunctionStatement) map[int]loopShape {
	summarizable := func(instr Instruction) bool {
		if (instr.Mnemonic != "bl" && instr.Mnemonic != "call") || len(instr.Operands) == 0 {
			return false
		}
		sym, isSym := instr.Operands[0].(Symbol)
		if !isSym {
			return false
		}
		if callees[sym.Name] != nil {
			return true
		}
		// A vector-contract callee is reached at its native entry, the Oak
		// name under the lane's suffix (summarizeCall reads it the same way).
		for _, arch := range []string{ArchArm64, ArchRV64} {
			if base, suffixed := strings.CutSuffix(sym.Name, VectorEntrySuffix(arch)); suffixed && callees[base] != nil {
				return true
			}
		}
		return false
	}
	loops := map[int]loopShape{}
	innerHeaders := map[int]int{} // header index -> back edge index of a recognized loop
	trace := os.Getenv("OAK_VERIFY_TRACE") != ""
	reject := func(back int, why string) {
		if trace {
			fmt.Fprintf(os.Stderr, "loop: %s: back edge at item %d not recognized: %s\n", function, back, why)
		}
	}
	for back, item := range items {
		branch, isBranch := item.(Instruction)
		if !isBranch {
			continue
		}
		if isConditionalBranch(branch.Mnemonic) && len(branch.Operands) > 0 {
			// A conditional back edge: a bottom-tested loop (the native
			// backend's rotated `while`), recognized by its shape.
			if sym, isSym := branch.Operands[len(branch.Operands)-1].(Symbol); isSym {
				if header, isLabel := labels[sym.Name]; isLabel && header < back {
					shape, why, ok := tailLoopShape(items, labels, innerHeaders, header, back, branch, summarizable)
					if !ok {
						reject(back, why)
						continue
					}
					for _, at := range shape.exits {
						loops[at] = shape // the executor summarizes at the first undecided entry branch
					}
					innerHeaders[header] = back
				}
			}
			continue
		}
		if !isUnconditionalJump(branch.Mnemonic) {
			continue
		}
		header, ok := labels[branch.Operands[0].(Symbol).Name]
		if !ok || header >= back || header+2 >= back {
			continue
		}
		// The header: every exit test from the label to the last branch
		// leaving the loop. An exit test is a run of pure register
		// instructions ending in a conditional branch to the exit label
		// (past the back edge); a conjunction (`len >= 64 && off <= len -
		// 64`) is several such tests; an element guard — a branch to the
		// trap block — and the guarded load an exit test reads (`while n >
		// 0 && digits[n-1] == 48`) are part of the header too; and a
		// short-circuit spelled with a forward branch to a label inside
		// the header (the RV64 lane's `&&`: `beqz t0, short; ...; short:
		// beqz t0, done`) forks the header's paths, which the summary
		// walks (headerCondition). The body starts after the last exit.
		var exits []int
		type forward struct{ at, target int }
		var forwards []forward    // forward branches to labels before the back edge
		pending := map[int]bool{} // labels forward branches target
		exitLabel, bodyStart := -1, -1
		wellFormed := true
		headerWhy := ""
		for scan := header + 1; scan < back; scan++ {
			if label, isLabel := items[scan].(Label); isLabel {
				if pending[labels[label.Name]] {
					delete(pending, labels[label.Name])
					continue
				}
				break // a label no header branch targets: the body has begun
			}
			instr, isInstr := items[scan].(Instruction)
			if !isInstr {
				break
			}
			if isGuardBranch(items, labels, instr) || isHeaderLoad(instr) || isFrameSpill(instr) {
				continue // a guard, a guarded load, or a temporary spilled around a call
			}
			if isConditionalBranch(instr.Mnemonic) {
				target, ok := labels[instr.Operands[len(instr.Operands)-1].(Symbol).Name]
				switch {
				case !ok:
					wellFormed = false
					headerWhy = "a branch to an unknown label"
				case target > back:
					if exitLabel < 0 {
						exitLabel = target
					}
					if target != exitLabel {
						wellFormed = false
						headerWhy = "exit tests leaving to two different labels (" + instr.Mnemonic + ")"
					}
					exits = append(exits, scan)
					bodyStart = scan + 1
				case target > scan:
					forwards = append(forwards, forward{at: scan, target: target})
					pending[target] = true
				default:
					wellFormed = false
					headerWhy = "a backward branch in the header (" + instr.Mnemonic + ")"
				}
				if !wellFormed {
					break
				}
				continue
			}
			if isUnconditionalJump(instr.Mnemonic) || isStoreMnemonic(instr.Mnemonic) || isLoad(instr.Mnemonic) || isFrameMemory(instr) || hasVectorOperand(instr) {
				if len(exits) == 0 {
					headerWhy = "no exit test before " + instr.Mnemonic
				}
				break
			}
			switch instr.Mnemonic {
			case "bl", "ret", "eret", "jal", "jalr", "auipc", "jr", "call":
				if summarizable(instr) {
					continue // a program function in an exit test: summarized
				}
				wellFormed = false
				headerWhy = "a call or return in the header (" + instr.Mnemonic + ")"
			}
			if !wellFormed {
				break
			}
		}
		if !wellFormed || len(exits) == 0 || bodyStart >= back {
			if headerWhy == "" {
				headerWhy = fmt.Sprintf("header (%d exits, body start %d)", len(exits), bodyStart)
			}
			reject(back, headerWhy)
			continue
		}
		// A forward branch before the last exit is a header path fork; its
		// label must lie inside the header too (a jump into the body past
		// an exit test is not a loop this recognizer knows). One after the
		// last exit is the body's own conditional.
		var internal []int
		for _, fwd := range forwards {
			if fwd.at >= bodyStart {
				continue
			}
			if fwd.target >= bodyStart {
				wellFormed = false
			}
			internal = append(internal, fwd.at)
		}
		if !wellFormed {
			reject(back, "a header branch into the body")
			continue
		}
		exitIndex := exits[0]
		cmpIndex := -1
		bodyWhy := ""
		for i := bodyStart; i < back; i++ {
			instr, isInstr := items[i].(Instruction)
			if !isInstr {
				continue // an inner label
			}
			switch instr.Mnemonic {
			case "bl", "ret", "eret", "jal", "jalr", "auipc", "jr", "call":
				if summarizable(instr) {
					continue // a program function in the body: summarized
				}
				wellFormed = false
				bodyWhy = "the body calls or returns (" + instr.Mnemonic + ")"
			case "b", "j", "b.", "cbz", "cbnz", "tbz", "tbnz", "beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz", "bnez", "bgez", "bltz", "blez", "bgtz":
				target, ok := labels[instr.Operands[len(instr.Operands)-1].(Symbol).Name]
				if !ok || target >= back {
					// A guard's branch to the trap block is not an exit: the
					// path it takes delivers no result (docs/spec/94-assembler.md §8).
					if !ok || !isTrapBlock(items, target) || isUnconditionalJump(instr.Mnemonic) {
						wellFormed = false
						bodyWhy = "the body leaves the loop (" + instr.Mnemonic + " past the back edge)"
					}
				} else if target <= i {
					// A backward branch inside the body: admitted only as
					// the back edge of a recognized inner loop lying inside.
					if innerBack, isInner := innerHeaders[target]; !isInner || innerBack != i || target <= header {
						wellFormed = false
						bodyWhy = "the body has a backward branch that is not a recognized inner loop"
					}
				}
			}
		}
		if !wellFormed {
			reject(back, bodyWhy)
			continue
		}
		shape := loopShape{header: header, cmp: cmpIndex, exit: exitIndex, exitLabel: exitLabel, bodyStart: bodyStart, bodyEnd: back, exits: exits, internal: internal, testStart: header + 1, testEnd: bodyStart}
		// The entry-only tests right before the header: exits too, met
		// first.
		shape.entryStart, shape.entryEnd = invariantEntryTests(items, labels, header, exitLabel, header, back), header
		var entryExits []int
		for at := shape.entryStart; at < shape.entryEnd; at++ {
			if instr, isInstr := items[at].(Instruction); isInstr && isConditionalBranch(instr.Mnemonic) {
				entryExits = append(entryExits, at)
			}
		}
		shape.exits = append(entryExits, exits...)
		for _, at := range shape.exits {
			loops[at] = shape // an undecided branch at any exit test summarizes the loop
		}
		for _, at := range internal {
			loops[at] = shape // an undecided short-circuit branch in the header too
		}
		innerHeaders[header] = back
	}
	return loops
}

// tailInverse pairs each condition code with its complement, for the
// peeled entry test of a bottom-tested loop.
var tailInverse = map[string]string{
	"eq": "ne", "ne": "eq", "hs": "lo", "cs": "cc", "lo": "hs", "cc": "cs", "mi": "pl", "pl": "mi",
	"vs": "vc", "vc": "vs", "hi": "ls", "ls": "hi", "ge": "lt", "lt": "ge", "gt": "le", "le": "gt",
}

// tailLoopShape recognizes a bottom-tested loop by its conditional back
// edge at back (docs/spec/94-assembler.md §9 "Bottom-tested loops"):
//
//	cmp wI, wL; b.hs exit; cbnz wB, exit     the entry test, leaving to exit
//	header:
//	  body
//	cmp wI, wL; b.hs exit; cbz wB, header    the tail test: the same run,
//	exit:                                     its last branch complemented
//
// The tail test is a run of compares and conditional branches — every
// branch but the last leaving to the exit label, the last the back edge —
// with no other instruction among them; the entry test right before the
// header label is the same run with its last branch to the exit label
// under the complementary condition; and nothing else branches to the
// header. The loop then iterates the body exactly as the top-tested loop
// with that test at its header would — the entry test is the first
// iteration's, the tail test every later one's — so the shape is the
// top-tested one with its test range at the tail (headerCondition walks
// it over the header state, the back edge taken as the continue
// condition) and its exit keyed at the entry branch, where the executor
// meets the loop with the entry state.
func tailLoopShape(items []Item, labels map[string]int, innerHeaders map[int]int, header, back int, branch Instruction, summarizable func(Instruction) bool) (loopShape, string, bool) {
	headerName := items[header].(Label).Name
	if branch.Mnemonic != "b." && branch.Mnemonic != "cbz" && branch.Mnemonic != "cbnz" {
		return loopShape{}, "a conditional back edge that is not b.cond, cbz, or cbnz", false
	}
	// The exit label: the entry test's target, every tail exit's target.
	if header < 1 {
		return loopShape{}, "a bottom-tested loop without an entry test", false
	}
	entryLast, isEntry := items[header-1].(Instruction)
	if !isEntry || !isConditionalBranch(entryLast.Mnemonic) || len(entryLast.Operands) == 0 {
		return loopShape{}, "a bottom-tested loop whose entry is not a conditional branch", false
	}
	exitSym, isSym := entryLast.Operands[len(entryLast.Operands)-1].(Symbol)
	exitLabel, isLabel := labels[exitSym.Name]
	if !isSym || !isLabel || exitLabel <= back {
		return loopShape{}, "a bottom-tested loop whose entry test does not leave past the back edge", false
	}
	// The tail run: back to the first instruction that is not a compare
	// or a branch to the exit label.
	tailStart := back
	for tailStart > header+1 {
		instr, isInstr := items[tailStart-1].(Instruction)
		if !isInstr {
			break
		}
		if instr.Mnemonic == "cmp" {
			tailStart--
			continue
		}
		if isConditionalBranch(instr.Mnemonic) && len(instr.Operands) > 0 {
			if sym, ok := instr.Operands[len(instr.Operands)-1].(Symbol); ok && sym.Name == exitSym.Name {
				tailStart--
				continue
			}
		}
		break
	}
	if branch.Mnemonic == "b." && (tailStart == back || items[back-1].(Instruction).Mnemonic != "cmp") {
		return loopShape{}, "a conditional back edge whose test is not a compare", false
	}
	if header+1 >= tailStart {
		return loopShape{}, "a bottom-tested loop without a body", false
	}
	// The entry run mirrors the tail run instruction for instruction, the
	// last branch complemented and leaving to the exit label.
	n := back + 1 - tailStart
	if header-n < 0 {
		return loopShape{}, "a bottom-tested loop whose entry test is shorter than its tail test", false
	}
	for k := 0; k < n; k++ {
		tail, isTail := items[tailStart+k].(Instruction)
		entry, isEntryInstr := items[header-n+k].(Instruction)
		if !isTail || !isEntryInstr {
			return loopShape{}, "a bottom-tested loop whose entry test holds a label", false
		}
		if k < n-1 {
			if tail.Mnemonic != entry.Mnemonic || tail.Cond != entry.Cond || describeOperands(tail.Operands) != describeOperands(entry.Operands) {
				return loopShape{}, "a bottom-tested loop whose entry test differs from its tail test", false
			}
			continue
		}
		// The last: the back edge against the entry's exit branch.
		switch tail.Mnemonic {
		case "b.":
			if entry.Mnemonic != "b." || tailInverse[tail.Cond] != entry.Cond {
				return loopShape{}, "a bottom-tested loop whose entry condition is not the tail condition's complement", false
			}
		default:
			opposite := map[string]string{"cbz": "cbnz", "cbnz": "cbz"}[tail.Mnemonic]
			if entry.Mnemonic != opposite || len(entry.Operands) != 2 || len(tail.Operands) != 2 || describeOperands(entry.Operands[:1]) != describeOperands(tail.Operands[:1]) {
				return loopShape{}, "a bottom-tested loop whose entry test is not the complement of its tail test", false
			}
		}
	}
	// Nothing but the back edge branches to the header.
	for i, item := range items {
		instr, isInstr := item.(Instruction)
		if !isInstr || i == back || len(instr.Operands) == 0 {
			continue
		}
		if sym, isSym := instr.Operands[len(instr.Operands)-1].(Symbol); isSym && sym.Name == headerName {
			return loopShape{}, "a bottom-tested loop whose header another branch reaches", false
		}
	}
	// The body: no call or return outside the program's functions, no
	// branch leaving the loop but a guard's to the trap block, no backward
	// branch but a recognized inner loop's back edge.
	for i := header + 1; i < tailStart; i++ {
		instr, isInstr := items[i].(Instruction)
		if !isInstr {
			continue
		}
		switch instr.Mnemonic {
		case "bl", "ret", "eret", "jal", "jalr", "auipc", "jr", "call":
			if summarizable(instr) {
				continue
			}
			return loopShape{}, "the body calls or returns (" + instr.Mnemonic + ")", false
		case "b", "j", "b.", "cbz", "cbnz", "tbz", "tbnz", "beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz", "bnez", "bgez", "bltz", "blez", "bgtz":
			target, ok := labels[instr.Operands[len(instr.Operands)-1].(Symbol).Name]
			if !ok || target >= tailStart {
				if !ok || !isTrapBlock(items, target) || isUnconditionalJump(instr.Mnemonic) {
					return loopShape{}, "the body leaves the loop (" + instr.Mnemonic + " past the tail test)", false
				}
			} else if target <= i {
				if innerBack, isInner := innerHeaders[target]; !isInner || innerBack != i || target <= header {
					return loopShape{}, "the body has a backward branch that is not a recognized inner loop", false
				}
			}
		}
	}
	cmpIndex := -1
	if branch.Mnemonic == "b." {
		cmpIndex = back - 1
	}
	// Every branch of the entry run is an exit the executor may meet
	// undecided first (an earlier one decided by a constant — a flag
	// cleared before the loop — falls through to the next), and so is
	// every branch of the tail run: when the whole entry test is decided
	// the executor runs the first iteration and meets the loop at its
	// tail, where the state before the back edge is the next header's, as
	// a top-tested loop's second header visit is.
	var exits []int
	for k := header - n; k < header; k++ {
		if instr, isInstr := items[k].(Instruction); isInstr && isConditionalBranch(instr.Mnemonic) {
			exits = append(exits, k)
		}
	}
	for k := tailStart; k <= back; k++ {
		if instr, isInstr := items[k].(Instruction); isInstr && isConditionalBranch(instr.Mnemonic) {
			exits = append(exits, k)
		}
	}
	// The entry-only tests before the entry run: exits too, met first.
	entryStart := invariantEntryTests(items, labels, header-n, exitLabel, header, back)
	var entryExits []int
	for at := entryStart; at < header-n; at++ {
		if instr, isInstr := items[at].(Instruction); isInstr && isConditionalBranch(instr.Mnemonic) {
			entryExits = append(entryExits, at)
		}
	}
	exits = append(entryExits, exits...)
	shape := loopShape{header: header, cmp: cmpIndex, exit: exits[0], exitLabel: exitLabel, bodyStart: header + 1, bodyEnd: tailStart, exits: exits, testStart: tailStart, testEnd: back + 1, tail: true, entryStart: entryStart, entryEnd: header - n}
	return shape, "", true
}

// isTrapBlock reports a label whose first instruction is `brk` (or
// `ebreak` on the RV64 lane): the trap a bounds guard, a zero divisor, or a
// failed assert branches to.
func isTrapBlock(items []Item, index int) bool {
	for i := index; i < len(items); i++ {
		if instr, isInstr := items[i].(Instruction); isInstr {
			return instr.Mnemonic == "brk" || instr.Mnemonic == "ebreak"
		}
	}
	return false
}

// isGuardBranch reports a conditional branch to the trap block: an
// element guard (`cmp wI, wL; b.hs trap`), a zero-divisor check. Its taken
// path delivers no result, so it is neither an exit nor a fork of the
// loop's paths.
func isGuardBranch(items []Item, labels map[string]int, instr Instruction) bool {
	if !isConditionalBranch(instr.Mnemonic) || len(instr.Operands) == 0 {
		return false
	}
	sym, isSym := instr.Operands[len(instr.Operands)-1].(Symbol)
	if !isSym {
		return false
	}
	target, ok := labels[sym.Name]
	return ok && isTrapBlock(items, target)
}

// isFrameSpill reports a scalar load or store of the frame (a temporary
// spilled around a call and reloaded), which a loop header may hold.
func isFrameSpill(instr Instruction) bool {
	if !isFrameMemory(instr) || hasVectorOperand(instr) {
		return false
	}
	return isLoad(instr.Mnemonic) || isStoreMnemonic(instr.Mnemonic) || rv64Loads[instr.Mnemonic] != 0 || rv64Stores[instr.Mnemonic] != 0
}

// isHeaderLoad reports a scalar load through a register base (a span or
// table element) that an exit test may read: not the frame, not a vector.
func isHeaderLoad(instr Instruction) bool {
	if !isLoad(instr.Mnemonic) || isFrameMemory(instr) || hasVectorOperand(instr) || len(instr.Operands) < 2 {
		return false
	}
	if _, isMem := instr.Operands[len(instr.Operands)-1].(Memory); !isMem {
		return false
	}
	if dest, isReg := instr.Operands[0].(Register); !isReg || dest.Class == ClassV {
		return false
	}
	return rv64Loads[instr.Mnemonic] != 0 || isPlainLoad(instr.Mnemonic)
}

// isRV64Setup reports an RV64 data-processing instruction that may precede
// a loop's exit branch as its comparison-operand setup: a register
// destination, no memory, no control transfer.
func isRV64Setup(instr Instruction) bool {
	base := rv64Base(instr)
	if len(base.Operands) < 2 || rv64Branches[base.Mnemonic] || base.Mnemonic == "jal" || base.Mnemonic == "jalr" || base.Mnemonic == "call" || base.Mnemonic == "auipc" {
		return false
	}
	if _, isReg := base.Operands[0].(Register); !isReg {
		return false
	}
	for _, operand := range base.Operands {
		if _, isMem := operand.(Memory); isMem {
			return false
		}
	}
	_, isALU := rv64ALU[base.Mnemonic]
	_, isALUImm := rv64ALUImm[base.Mnemonic]
	_, isALUW := rv64ALUW[base.Mnemonic]
	_, isALUImmW := rv64ALUImmW[base.Mnemonic]
	return isALU || isALUImm || isALUW || isALUImmW || base.Mnemonic == "lui" || instr.Mnemonic == "li" || base.Mnemonic == "slt" || base.Mnemonic == "sltu"
}

func isConditionalBranch(mnemonic string) bool {
	switch mnemonic {
	case "b.", "cbz", "cbnz", "tbz", "tbnz":
		return true
	}
	return rv64ConditionalBranches[mnemonic]
}

// isUnconditionalJump reports the plain jump of either lane (b, j).
func isUnconditionalJump(mnemonic string) bool { return mnemonic == "b" || mnemonic == "j" }

// loopEvent is one side's summary of a data-dependent loop.
type loopEvent struct {
	index  int              // creation order, 1-based; fresh symbols are loop<index>.<var>
	parent int              // the enclosing event's index, 0 at top level
	vars   []string         // loop-carried variables, in a stable order
	header map[string]*term // value at the header on entry
	fresh  map[string]*term // the symbol standing for the value on an iteration
	width  map[string]int
	cond   *term            // continue condition over the fresh symbols (1/0)
	next   map[string]*term // value after one iteration, over the fresh symbols
	// floats marks the Oak side's f32/f64 locals: only they pair with a
	// vector register half or an RV64 f register zero-extended.
	floats map[string]bool
	// writes: the stores one iteration makes through each span, over the
	// fresh symbols and the iteration's memory (the loop's marker), each
	// under the body path condition it happens on. The coupling proof
	// compares the two sides' stores pairwise (verifyLoops).
	writes map[string][]*spanWrite
	// oakDerived marks an event a call summary took from a callee's Oak
	// body (summarizeCall): its variables are the callee's locals, named
	// as the Oak side names them, not registers — the register-class
	// readings of a variable's name (`r9`, `v8.lo`, `f10`, `s-16:8`) do
	// not apply to it.
	oakDerived bool
	// entry: each marked span's write log at the loop's entry, over the
	// span's entry memory — what the marker replaced. The coupling proof
	// requires the two sides' entry memories equal (the induction's base;
	// without it a store before the loop that differs between the sides
	// would vanish under the markers).
	entry map[string][]*spanWrite
	// reached, on the machine side, is the path's condition at the loop's
	// entry (nil: every path): the summary holds on those inputs, and the
	// coupling proof's body premise assumes it — a loop under `ok ? {…}`
	// couples its counter's register on the inputs where ok holds, where
	// the register's header value is what the path made it.
	reached *term
	// oakPath, on the Oak side, is the lowering's path condition at the
	// loop (an arm the loop sits in): a call summary conjoins it with the
	// machine's path at the call as the callee loop's reached condition
	// (summarizeCall). The Oak side's own events leave reached nil.
	oakPath *term
	// at is the event's place in the layout: the loop header's item
	// index, or the call's for a callee's loops. Sibling events out of
	// layout order mean the paths ran the sides of a fork in another
	// order than the Oak body lowers them (loopsInLayoutOrder).
	at int
}

func (ev *loopEvent) freshName(v string) string { return fmt.Sprintf("loop%d.%s", ev.index, v) }

// entryCondition is the loop's continue condition at the header's entry
// values: the test that decides whether the loop runs at all. Fresh loop
// variables become their saved header values and reads from the iteration's
// unknown memories become reads from the exact entry memories. A loop that
// does not run leaves its memories alone, so the memory marker holds only
// under this condition. nil means the condition is constant true. The second
// result fails closed when an entry value or memory cannot be reconstructed.
func (ev *loopEvent) entryCondition() (*term, bool) {
	if ev.cond == nil {
		return nil, true
	}
	sigma := map[string]*term{}
	for name, fresh := range ev.fresh {
		header, known := ev.header[name]
		if !known || fresh == nil || header == nil {
			return nil, false
		}
		sigma[fresh.name] = header
	}
	entry := truncate(substitute(ev.cond, sigma), 1)
	valid := true
	entry = restoreLoopEntryMemories(entry, ev, map[*term]*term{}, &valid)
	if !valid {
		return nil, false
	}
	if entry.kind == termConst && entry.value&1 == 1 {
		return nil, true
	}
	return entry, true
}

// guardMarker conjoins cond onto the loop memory marker at the end of a
// span's write log, which appendMarker has just placed there.
func guardMarker(log []*spanWrite, cond *term) {
	if cond == nil || len(log) == 0 {
		return
	}
	marker := log[len(log)-1]
	if marker.memory == "" {
		return
	}
	if marker.guard != nil {
		marker.guard = binaryTerm("and", truncate(marker.guard, 1), cond)
		return
	}
	marker.guard = cond
}

// substituteAll rewrites every term of the event under sigma: the
// condition, the header and next values, and the stores. The memo is
// shared across the terms (and across events): a subterm is rewritten once.
func (ev *loopEvent) substituteAll(sigma map[string]*term, memo map[*term]*term) {
	ev.cond = substituteMemo(ev.cond, sigma, memo)
	if ev.reached != nil {
		ev.reached = substituteMemo(ev.reached, sigma, memo)
	}
	for name, t := range ev.header {
		ev.header[name] = substituteMemo(t, sigma, memo)
	}
	for name, t := range ev.next {
		ev.next[name] = substituteMemo(t, sigma, memo)
	}
	for _, log := range [2]map[string][]*spanWrite{ev.writes, ev.entry} {
		for _, writes := range log {
			for _, w := range writes {
				w.index = substituteMemo(w.index, sigma, memo)
				w.value = substituteMemo(w.value, sigma, memo)
				if w.guard != nil {
					w.guard = substituteMemo(w.guard, sigma, memo)
				}
			}
		}
	}
}

// descends reports whether inner was summarized inside outer's body: outer
// is on inner's chain of parents.
func (x *pathExecutor) descends(inner, outer *loopEvent) bool {
	for p := inner.parent; p != 0; p = x.loops[p-1].parent {
		if p == outer.index {
			return true
		}
	}
	return false
}

// loopEvent summarizes the top-level asm loop whose exit branch was just
// reached with an undecided condition, then continues past the exit.
func (x *pathExecutor) loopEvent(shape loopShape, exit Instruction, state *symbolicState) (*term, *pathEffects, string, bool) {
	post, reason, ok := x.summarizeLoop(shape, exit, state)
	if !ok {
		return nil, nil, reason, false
	}
	// The path continues past the exit: the loop's memory markers and
	// what the code after the loop stores are its effects.
	return x.run(shape.exitLabel, post)
}

// summarizeLoop records the loop event and returns the state past the
// exit: the loop-carried registers hold their fresh symbols, scratch
// registers are unbound.
func (x *pathExecutor) summarizeLoop(shape loopShape, exit Instruction, state *symbolicState) (*symbolicState, string, bool) {
	if x.concrete {
		return nil, "a loop that a witness run could not decide", false
	}
	// The loop's event: a new one at the next index, or — the loop head
	// reached again on another path — one taking the index and symbols of
	// the first, whose fields the two paths' summaries merge below.
	site := fmt.Sprintf("loop@%d", shape.header)
	var prior *loopEvent
	eventIndex := len(x.loops) + 1
	rec, seen := x.sites[site]
	if seen && rec.diverged(state.path) {
		eventIndex = rec.base + 1
		prior = x.loops[rec.base]
	} else if len(x.loops) >= loopEventBudget {
		if os.Getenv("OAK_VERIFY_TRACE") != "" {
			for _, ev := range x.loops {
				fmt.Fprintf(os.Stderr, "verify: asm loop event %d (parent %d, oak-derived %v): vars %v\n", ev.index, ev.parent, ev.oakDerived, ev.vars)
			}
		}
		return nil, "more data-dependent loops than the verifier's budget", false
	}
	// The loop-carried registers are those the body writes; each is a
	// fresh 32-bit symbol when the body only ever writes its w view and the
	// header value is already zero-extended from 32 bits, else 64-bit.
	written := map[int]bool{}
	allW := map[int]bool{}
	// The exit tests' temporaries (a compare operand's setup, a loaded
	// element, a short-circuit's flag) hold no loop-carried value: the
	// state at the branch has whichever were written before it, so they
	// are scratch here rather than paired, and unbound past the loop.
	headerWritten := map[int]bool{}
	resultRegs := []int{0, 1} // a summarized call's result chunks: temporaries too
	if x.arch == ArchRV64 {
		resultRegs = []int{10, 11}
	}
	for at := shape.header + 1; at < shape.bodyEnd; at++ {
		instr, isInstr := x.items[at].(Instruction)
		if !isInstr || instr.Mnemonic == "cmp" || instr.Mnemonic == "tst" || isConditionalBranch(instr.Mnemonic) || len(instr.Operands) == 0 {
			continue
		}
		if instr.Mnemonic == "bl" || instr.Mnemonic == "call" {
			for _, reg := range resultRegs {
				headerWritten[reg] = true
			}
			continue
		}
		if at >= shape.bodyStart {
			continue // a body write: loop-carried unless a header temporary
		}
		if dest, isReg := instr.Operands[0].(Register); isReg && !dest.ZeroRegister() && dest.Class != ClassV {
			headerWritten[dest.Num] = true
		}
	}
	// A register's own spill: `str xN, [sp, #off]` in the body, reloaded
	// by `ldr xN, [sp, #off]`. The reload restores the value the register
	// held, so it is no write of its own — in particular no 64-bit one: a
	// register the body otherwise writes as w stays a 32-bit variable
	// across a spill around a call, on every path alike.
	spills := map[string]bool{}
	for i := shape.bodyStart; i < shape.bodyEnd; i++ {
		instr, isInstr := x.items[i].(Instruction)
		if !isInstr || !isFrameSpill(instr) || !(isStoreMnemonic(instr.Mnemonic) || rv64Stores[instr.Mnemonic] != 0) || len(instr.Operands) < 2 {
			continue
		}
		if src, isReg := instr.Operands[0].(Register); isReg {
			if mem, isMem := instr.Operands[len(instr.Operands)-1].(Memory); isMem {
				spills[fmt.Sprintf("%d:%d", src.Num, mem.Offset)] = true
			}
		}
	}
	for i := shape.bodyStart; i < shape.bodyEnd; i++ {
		instr, isInstr := x.items[i].(Instruction)
		if !isInstr || instr.Mnemonic == "cmp" || instr.Mnemonic == "tst" || isConditionalBranch(instr.Mnemonic) || isUnconditionalJump(instr.Mnemonic) || isStoreMnemonic(instr.Mnemonic) || rv64Stores[instr.Mnemonic] != 0 || len(instr.Operands) == 0 {
			continue // no register written: compares, branches, stores
		}
		dest, isReg := instr.Operands[0].(Register)
		if !isReg || dest.ZeroRegister() || dest.Class == ClassV {
			continue // the vector file is carried separately below
		}
		if isFrameSpill(instr) && len(instr.Operands) >= 2 {
			if mem, isMem := instr.Operands[len(instr.Operands)-1].(Memory); isMem && spills[fmt.Sprintf("%d:%d", dest.Num, mem.Offset)] {
				continue // the register's own spill reloaded
			}
		}
		if !written[dest.Num] {
			allW[dest.Num] = true
		}
		written[dest.Num] = true
		if dest.Class != ClassW {
			allW[dest.Num] = false
		}
	}
	// The vector registers and the frame slots the body writes are
	// loop-carried too (asm/verify_vector.go): a vector local lives in a
	// v register or, spilled, in a sixteen-byte slot. Each is two 64-bit
	// symbols (its halves; a slot per eight bytes).
	writtenV := map[int]bool{}
	// The RV64 lane's floating-point registers the body writes: each one
	// symbol at the width of the pattern it holds at the header (the file
	// holds patterns at the width of the instruction that wrote them).
	writtenF := map[int]bool{}
	// writtenSlots: the frame slots the body stores, by address, with the
	// store's width (4 or 8 bytes: a spilled w register or an x one); a
	// slot stored at two widths, or two stores overlapping, is refused.
	writtenSlots := map[int64]int64{}
	for i := shape.bodyStart; i < shape.bodyEnd; i++ {
		instr, isInstr := x.items[i].(Instruction)
		if !isInstr || isConditionalBranch(instr.Mnemonic) || isUnconditionalJump(instr.Mnemonic) {
			continue
		}
		if isFrameMemory(instr) && (isStoreMnemonic(instr.Mnemonic) || rv64Stores[instr.Mnemonic] != 0 || rv64FloatStores[instr.Mnemonic] != 0) {
			mem := instr.Operands[len(instr.Operands)-1].(Memory)
			if mem.Mode != MemOffset {
				return nil, "a frame access moving sp in a loop body", false
			}
			addr := -state.disp + mem.Offset
			if addr < -state.disp+x.outgoingArea() {
				// The outgoing argument area at the bottom of the frame: a
				// store there is a call's argument, read by the call that
				// follows on the same path (summarizeCall), not a slot the
				// loop carries — two callees' layouts may well overlap in it.
				continue
			}
			for _, reg := range registerOperands(instr.Operands[:len(instr.Operands)-1]) {
				size := int64(rv64Stores[instr.Mnemonic])
				if size == 0 {
					size = int64(rv64FloatStores[instr.Mnemonic])
				}
				if size == 0 {
					size = memorySizeReg(instr.Mnemonic, reg)
					if isPairAccess(instr.Mnemonic) {
						size /= 2
					}
				}
				// A w register's spill is a 4-byte slot; an x register's,
				// a pair's, or a vector's a run of 8-byte slots.
				var pieces []int64
				switch {
				case size == 4 && addr%4 == 0:
					pieces = []int64{4}
				case size%8 == 0 && addr%8 == 0:
					for k := int64(0); k < size; k += 8 {
						pieces = append(pieces, 8)
					}
				default:
					return nil, "a frame slot written in a loop body at a width other than 4 or a multiple of 8 bytes, or unaligned", false
				}
				for _, piece := range pieces {
					for other, otherSize := range writtenSlots {
						if other < addr+piece && addr < other+otherSize && (other != addr || otherSize != piece) {
							return nil, "frame slots written at overlapping addresses in a loop body", false
						}
					}
					writtenSlots[addr] = piece
					addr += piece
				}
			}
			continue
		}
		if isStoreMnemonic(instr.Mnemonic) || rv64Stores[instr.Mnemonic] != 0 || rv64FloatStores[instr.Mnemonic] != 0 {
			continue
		}
		if dest, isReg := instr.Operands[0].(Register); isReg {
			switch dest.Class {
			case ClassV:
				writtenV[dest.Num] = true
			case ClassRV64F:
				writtenF[dest.Num] = true
			}
		}
	}
	ev := &loopEvent{index: eventIndex, header: map[string]*term{}, fresh: map[string]*term{}, width: map[string]int{}, next: map[string]*term{}, reached: state.pathCondition(), at: shape.header}
	if n := len(x.loopStack); n > 0 {
		ev.parent = x.loopStack[n-1]
	}
	if prior != nil {
		x.loops[eventIndex-1] = ev
	} else {
		if !seen {
			// The first reach names the site; a reach on the same path
			// (an unrolled outer iteration) is an instance of its own.
			if x.sites == nil {
				x.sites = map[string]loopSite{}
			}
			x.sites[site] = loopSite{base: len(x.loops), count: 1, paths: []*pathNode{state.path}}
		}
		x.loops = append(x.loops, ev)
	}
	regs := make([]int, 0, len(written))
	for reg := range written {
		regs = append(regs, reg)
	}
	sort.Ints(regs)
	freshState := state.clone()
	scratch := map[int]bool{}
	scratchV := map[int]bool{}
	scratchSlots := map[int64]bool{}
	vregs := make([]int, 0, len(writtenV))
	for reg := range writtenV {
		vregs = append(vregs, reg)
	}
	sort.Ints(vregs)
	for _, reg := range vregs {
		value, bound := state.readVec(reg)
		halves := []*term{nil, nil}
		for h, side := range []string{"lo", "hi"} {
			name := fmt.Sprintf("v%d.%s", reg, side)
			fresh := paramTerm(ev.freshName(name), 64)
			x.declared[fresh.name] = 64
			halves[h] = fresh
			if !bound {
				scratchV[reg] = true
				continue
			}
			ev.vars = append(ev.vars, name)
			ev.width[name] = 64
			ev.header[name] = value.halves()[h]
			ev.fresh[name] = fresh
		}
		freshState.writeVec(reg, vecOfLanes(halves, 64))
	}
	scratchF := map[int]bool{}
	fregs := make([]int, 0, len(writtenF))
	for reg := range writtenF {
		fregs = append(fregs, reg)
	}
	sort.Ints(fregs)
	for _, reg := range fregs {
		// A callee-saved register (fs0–fs11) read before any write carries
		// the caller's pattern (entry.fN), as state.read binds it.
		value, bound := state.read(Register{Class: ClassRV64F, Num: reg, Lane: -1})
		width := 64
		if bound {
			width = value.width
		}
		name := fmt.Sprintf("f%d", reg)
		fresh := paramTerm(ev.freshName(name), width)
		x.declared[fresh.name] = width
		freshState.write(Register{Class: ClassRV64F, Num: reg, Lane: -1}, fresh)
		if !bound {
			scratchF[reg] = true
			continue
		}
		ev.vars = append(ev.vars, name)
		ev.width[name] = width
		ev.header[name] = value
		ev.fresh[name] = fresh
	}
	for _, reg := range regs {
		name := fmt.Sprintf("r%d", reg)
		width := 64
		if allW[reg] {
			width = 32
		}
		fresh := paramTerm(ev.freshName(name), width)
		value, bound := state.regs[reg]
		if headerWritten[reg] {
			bound = false // an exit test's temporary: scratch, never paired
		}
		if !bound {
			// Written in the body but holding nothing at the header: a
			// scratch register. It takes a fresh value for the iteration and
			// is unbound after the loop (reading it there is outside the
			// subset — the executor loses the last iteration's value).
			scratch[reg] = true
			x.declared[fresh.name] = width
			freshState.regs[reg] = zeroExtend(fresh, 64)
			continue
		}
		if width == 32 && !upperClear(value, x.declared) {
			if os.Getenv("OAK_VERIFY_TRACE") != "" {
				fmt.Fprintf(os.Stderr, "verify %s: loop %d: %s written as w only but its header value is not known zero-extended: %s\n", x.fn.Name, ev.index, name, value)
			}
			width = 64
			fresh = paramTerm(ev.freshName(name), width)
		}
		ev.vars = append(ev.vars, name)
		ev.width[name] = width
		ev.header[name] = truncate(value, width)
		ev.fresh[name] = fresh
		// The fresh symbol is declared at its width: an inner loop's header
		// value built from it is then known to be zero-extended.
		x.declared[fresh.name] = width
		freshState.regs[reg] = zeroExtend(fresh, 64)
	}
	// A store through a frame address register at a data-dependent index
	// (`strb wV, [xB, wI, uxtw]`, the tail copy) reaches slots no syntactic
	// scan names: the body runs once on the fresh register state, before
	// the slots' symbols exist, and every slot it changes or creates joins
	// the loop-carried slots at its width (a body with inner loops or
	// calls is not probed: the probe would summarize them a second time).
	if x.hasIndexedFrameStore(shape) && !x.hasInnerLoopOrCall(shape) {
		probe := freshState.clone()
		if ends, _, ok := x.runBody(shape, probe); ok {
			for _, end := range ends {
				for addr, slot := range end.state.frame {
					before, held := state.frame[addr]
					if held && before.width == slot.width && before.value == slot.value {
						continue
					}
					if _, known := writtenSlots[addr]; known {
						continue
					}
					if !held {
						continue // a scratch piece the body created; not carried
					}
					writtenSlots[addr] = int64(slot.width)
				}
			}
		}
	}
	slots := make([]int64, 0, len(writtenSlots))
	for addr := range writtenSlots {
		slots = append(slots, addr)
	}
	sort.Slice(slots, func(i, j int) bool { return slots[i] < slots[j] })
	if freshState.frame == nil {
		freshState.frame = map[int64]frameSlot{}
	}
	for _, addr := range slots {
		size := writtenSlots[addr]
		name := fmt.Sprintf("s%d:%d", addr, size)
		fresh := paramTerm(ev.freshName(name), int(size)*8)
		x.declared[fresh.name] = int(size) * 8
		value, bound := state.loadSlot(addr, size)
		freshState.storeSlot(addr, fresh, size)
		if !bound {
			scratchSlots[addr] = true
			continue
		}
		ev.vars = append(ev.vars, name)
		ev.width[name] = int(size) * 8
		ev.header[name] = value
		ev.fresh[name] = fresh
	}
	// The package cells the body stores (`st = u8(4)` inside `while un {
	// … }`, the OS pilot's flag idiom) are loop-carried too: each a fresh
	// symbol at the cell's width, its header value the cell as this path
	// holds it, paired with the Oak side's cell local like a register.
	carriedCells := map[string]bool{}
	for _, name := range x.cellsStoredIn(shape) {
		global := x.globals[name]
		varName := "global:" + name
		width := cellWidth(global)
		fresh := paramTerm(ev.freshName(varName), width)
		x.declared[fresh.name] = width
		value, _ := globalStateValue(x.globals, state.globals, name)
		if freshState.globals == nil {
			freshState.globals = map[string]*term{}
		}
		freshState.globals[name] = fresh
		carriedCells[name] = true
		ev.vars = append(ev.vars, varName)
		ev.width[varName] = width
		ev.header[varName] = truncate(value, width)
		ev.fresh[varName] = fresh
	}
	// The continue condition: no exit test taken along the header's paths,
	// each test evaluated on the fresh state after the header instructions
	// before it (headerCondition).
	cond, fallThroughStates, reason, ok := x.headerCondition(shape, freshState)
	if !ok {
		return nil, reason, false
	}
	ev.cond = cond
	// A header temporary the body reads — the exit test's operand setup,
	// such as the zero-extended index `slli z, i, 32; srli z, z, 32; bgeu
	// z, norm` whose z the RV64 lane's elided element access then scales
	// (docs/spec/94-assembler.md §9, "Check elision on the RV64 lane") —
	// holds at the body's first instruction the value the header gave it,
	// not a fresh one: when the header falls through on one path, the
	// body starts from that path's register values for the registers the
	// header wrote (the memory markers below are added to the fresh state
	// first; only registers are carried over).
	var headerValues map[int]*term
	if len(fallThroughStates) == 1 {
		headerValues = map[int]*term{}
		for reg := range headerWritten {
			if value, written := fallThroughStates[0].regs[reg]; written {
				headerValues[reg] = value
			}
		}
	}
	if os.Getenv("OAK_VERIFY_TRACE") != "" {
		fmt.Fprintf(os.Stderr, "verify %s: loop %d header paths %d, header-written %v, carried %d\n", x.fn.Name, ev.index, len(fallThroughStates), headerWritten, len(headerValues))
		for reg, value := range headerValues {
			fmt.Fprintf(os.Stderr, "verify %s:   r%d = %s\n", x.fn.Name, reg, value.String())
		}
	}
	_ = exit
	// The writable span parameters (`[*]T`, the only spans a body can
	// store through) take the loop's memory marker before the iteration
	// runs, so the body's reads see the iteration's unknown memory and its
	// stores layer on it; the Oak side marks the same parameters from the
	// same signature (loopEvent).
	storedSpans := map[string]bool{}
	writtenSpans := writableSpanMemories(x.fn, x.spans, x.recordSpans)
	for _, span := range writtenSpans {
		storedSpans[span] = true
	}
	ev.entry = map[string][]*spanWrite{}
	for _, span := range writtenSpans {
		ev.entry[span] = freshState.writes[span]
		freshState.writes = appendMarker(freshState.writes, span, ev.index)
	}
	entryCond, entryKnown := ev.entryCondition()
	if !entryKnown {
		return nil, "the loop's entry condition could not be reconstructed", false
	}
	for _, span := range writtenSpans {
		guardMarker(freshState.writes[span], entryCond)
	}
	// One iteration of the body on the fresh state: its paths (a branch
	// inside the body forks on its condition; an inner loop is summarized
	// in place) all reach the back edge and merge register by register
	// into selects on the path conditions.
	x.loopStack = append(x.loopStack, ev.index)
	bodyStart := freshState.clone()
	for reg, value := range headerValues {
		bodyStart.regs[reg] = value
	}
	ends, reason, ok := x.runBody(shape, bodyStart)
	x.loopStack = x.loopStack[:len(x.loopStack)-1]
	if !ok {
		return nil, reason + " (in a loop body)", false
	}
	// A cell the body stores is a loop variable (carriedCells, above); a
	// cell changed some other way — a callee's write the summary let
	// through — remains outside the theorem and fails closed.
	for _, end := range ends {
		before, after := map[string]*term{}, map[string]*term{}
		for name, value := range freshState.globals {
			if !carriedCells[name] {
				before[name] = value
			}
		}
		for name, value := range end.state.globals {
			if !carriedCells[name] {
				after[name] = value
			}
		}
		if name, differs := differingGlobalState(x.globals, before, after); differs {
			return nil, fmt.Sprintf("a store to package global %s in a loop body", name), false
		}
	}
	// The iteration's stores, each path's under its condition, in path
	// order; the state past the loop keeps the marker alone (the loop's
	// memory is the iteration's unknown memory, which the coupling proof
	// identifies with the Oak side's).
	// The memories the iteration may store into: a scalar span's own, a
	// span of records' per-leaf memories (`s.pages`, `s.free_count`) — the
	// Oak side's loopEvent marks and collects the same names.
	var storedMemories []string
	for _, span := range writtenSpans {
		if arg, isRecord := x.recordSpans[span]; isRecord {
			for _, memory := range arg.memories(span) {
				storedSpans[memory] = true
				storedMemories = append(storedMemories, memory)
			}
			continue
		}
		storedMemories = append(storedMemories, span)
	}
	for _, span := range storedMemories {
		before := len(freshState.writes[span])
		var stores []*spanWrite
		for _, end := range ends {
			log := end.state.writes[span]
			if len(log) > before {
				stores = append(stores, guardWrites(log[before:], end.cond)...)
			}
		}
		if len(stores) == 0 {
			// The complete symbolic iteration wrote no element of this
			// exact memory on any path.  A record span is split into leaf
			// memories, so a store through s.words does not make s.count
			// loop-carried.  Restore the entry log: retaining the marker
			// would invent a change to an untouched sibling field, and a
			// peeled loop would guard that invented change differently.
			// The entry record stays until the pass below, which restores
			// untouched memories once more and drops their markers: an
			// entry deleted here read as empty there, and the pass deleted
			// the whole log — the store before the loop with it (the OS
			// pilot's alloc_table: `free_count - 1` before its zeroing
			// loop vanished, and the memory after the loop was unproven).
			if len(ev.entry[span]) == 0 {
				delete(freshState.writes, span)
			} else {
				freshState.writes[span] = ev.entry[span]
			}
			continue
		}
		if ev.writes == nil {
			ev.writes = map[string][]*spanWrite{}
		}
		ev.writes[span] = stores
	}
	for _, end := range ends {
		for span, log := range end.state.writes {
			if !storedSpans[span] && len(log) > len(freshState.writes[span]) {
				return nil, "a store through a span that is not a writable parameter (in a loop body)", false
			}
		}
	}
	// A memory no path of the iteration stores to is unchanged by the loop,
	// so its marker stands for nothing and is dropped for the entry memory
	// it replaced. It matters because a record span marks one memory per
	// leaf: a loop writing one field marked every field, and the memory
	// past the loop then became an unknown function of the entry memory
	// that the Oak side's own marker had to match under the same path
	// conditions. Where the asm tests loop entry before the loop and the
	// Oak model does not, those conditions differ, and a leaf nothing
	// writes was the one thing left unproven (the os pilot's page-zeroing
	// loop, compiler/e2e_native_licm_test.go). The two sides prune the
	// same way, and a divergence fails closed in coupledEntryMemories.
	for _, span := range writtenSpans {
		if len(ev.writes[span]) > 0 {
			continue
		}
		if len(ev.entry[span]) == 0 {
			delete(freshState.writes, span)
		} else {
			freshState.writes[span] = ev.entry[span]
		}
		delete(ev.writes, span)
		delete(ev.entry, span)
	}
	for _, name := range ev.vars {
		merged := ends[len(ends)-1].valueOfVar(name, freshState)
		for i := len(ends) - 2; i >= 0; i-- {
			value := ends[i].valueOfVar(name, freshState)
			if equalTerms(value, merged) {
				continue // the same value on both paths: no select
			}
			merged = iteTerm(ends[i].cond, value, merged)
		}
		ev.next[name] = truncate(merged, ev.width[name])
	}
	// A variable the body writes but leaves, after one iteration, at the
	// value it held at the header — a spill reloaded, a copy of itself, a
	// value re-materialized from the loop's invariants — is not
	// loop-carried: its symbol stands for the header value in the
	// condition, in the other variables' next values, and in the state
	// past the loop. So an outer loop's counter that an inner body only
	// spills stays the outer loop's variable, not the inner loop's.
	invariant := map[string]*term{}
	carried := make([]string, 0, len(ev.vars))
	for _, name := range ev.vars {
		fresh := ev.fresh[name]
		if equalTerms(ev.next[name], truncate(fresh, ev.width[name])) || equalTerms(ev.next[name], truncate(ev.header[name], ev.width[name])) {
			invariant[fresh.name] = ev.header[name]
			delete(ev.next, name)
			delete(ev.fresh, name)
			delete(ev.width, name)
			delete(ev.header, name)
			continue
		}
		carried = append(carried, name)
	}
	if len(invariant) > 0 {
		ev.vars = carried
		// The symbols stood in the body's every term: this event's, and
		// those of the loops and calls summarized inside the body — its
		// descendants by the parent links, not every later event (the
		// executor summarizes the loops of other paths meanwhile) — which
		// read the header value through them. One memo across the terms:
		// the events share their subterms.
		memo := map[*term]*term{}
		for _, inner := range x.loops[ev.index-1:] {
			if inner == ev || x.descends(inner, ev) {
				inner.substituteAll(invariant, memo)
			}
		}
		for reg, value := range freshState.regs {
			freshState.regs[reg] = substitute(value, invariant)
		}
		for reg, value := range freshState.vregs {
			lanes := make([]*term, len(value.lanes))
			for k, lane := range value.lanes {
				lanes[k] = substitute(lane, invariant)
			}
			freshState.vregs[reg] = vecValue{bits: value.bits, lanes: lanes}
		}
		for reg, value := range freshState.fregs {
			freshState.fregs[reg] = substitute(value, invariant)
		}
		for name, value := range freshState.globals {
			freshState.globals[name] = substitute(value, invariant)
		}
		for addr, slot := range freshState.frame {
			freshState.frame[addr] = frameSlot{value: substitute(slot.value, invariant), width: slot.width}
		}
	}
	// A body that stored into a frame array at a data-dependent index
	// forgot the region on its paths; the state past the loop forgets it too.
	for _, end := range ends {
		if end.state.unknownFrom != nil {
			freshState.forgetFrameFrom(*end.state.unknownFrom)
		}
	}
	for reg := range scratch {
		delete(freshState.regs, reg)
	}
	for reg := range scratchV {
		delete(freshState.vregs, reg)
	}
	for reg := range scratchF {
		delete(freshState.fregs, reg)
	}
	for addr := range scratchSlots {
		delete(freshState.frame, addr)
	}
	freshState.flags = nil
	if prior != nil {
		// A register carried on one path and scratch on the other — it
		// held a value at one path's header and nothing at the other's —
		// whose header value the body never reads (a temporary the body
		// rewrites before reading: its symbol appears in no condition,
		// other variable's next value, or store) is scratch on both:
		// dropped from the summary that carried it, unbound past the
		// loop on this path. The two summaries then have one shape.
		demote := func(owner *loopEvent, name string) bool {
			if !strings.HasPrefix(name, "r") || owner.mentionsElsewhere(name) {
				return false
			}
			reg, err := strconv.Atoi(name[1:])
			if err != nil {
				return false
			}
			kept := owner.vars[:0:0]
			for _, v := range owner.vars {
				if v != name {
					kept = append(kept, v)
				}
			}
			owner.vars = kept
			delete(owner.next, name)
			delete(owner.header, name)
			delete(owner.fresh, name)
			delete(owner.width, name)
			if owner == ev {
				delete(freshState.regs, reg)
			}
			return true
		}
		has := func(owner *loopEvent, name string) bool {
			for _, v := range owner.vars {
				if v == name {
					return true
				}
			}
			return false
		}
		for _, name := range append([]string(nil), ev.vars...) {
			if !has(prior, name) {
				demote(ev, name)
			}
		}
		for _, name := range append([]string(nil), prior.vars...) {
			if !has(ev, name) {
				demote(prior, name)
			}
		}
		merged, reason, ok := mergeLoopEvents(state.pathCondition(), ev, prior)
		if !ok {
			return nil, reason, false
		}
		x.loops[eventIndex-1] = merged
		rec.paths = append(rec.paths, state.path)
		x.sites[site] = rec
	}
	return freshState, "", true
}

// exitReadSymbols reports, for the loop symbols of a side's events, the
// ones some other event's terms or the result term read: the variables
// whose value at the loop's exit flows on.
func exitReadSymbols(events []*loopEvent, result *term) map[string]bool {
	count := map[string]int{}
	own := make([]map[string]bool, len(events))
	for k, ev := range events {
		mentioned := map[string]bool{}
		collectParams(ev.cond, mentioned)
		collectParams(ev.reached, mentioned)
		for _, t := range ev.header {
			collectParams(t, mentioned)
		}
		for _, t := range ev.next {
			collectParams(t, mentioned)
		}
		for _, stores := range ev.writes {
			for _, store := range stores {
				collectParams(store.index, mentioned)
				collectParams(store.value, mentioned)
				collectParams(store.guard, mentioned)
			}
		}
		own[k] = mentioned
		for name := range mentioned {
			count[name]++
		}
	}
	if result != nil {
		mentioned := map[string]bool{}
		collectParams(result, mentioned)
		for name := range mentioned {
			count[name]++
		}
	}
	read := map[string]bool{}
	for k, ev := range events {
		for _, name := range ev.vars {
			symbol := ev.freshName(name)
			n := count[symbol]
			if own[k][symbol] {
				n--
			}
			read[symbol] = n > 0
		}
	}
	return read
}

// loopsInLayoutOrder reports whether sibling events (one parent) were
// created in layout order. The paths run a fork's sides one after the
// other; without a join the first side runs on past the fork's meeting
// point and summarizes the loops there before the other side's loops,
// where the Oak body lowers the sides then what follows — the events'
// numbering, which the coupling pairs by, then disagrees. A run merging
// at the joins restores the order (executeBodyChunk).
func (x *pathExecutor) loopsInLayoutOrder() bool {
	last := map[int]int{}
	for _, ev := range x.loops {
		if prev, seen := last[ev.parent]; seen && ev.at < prev {
			return false
		}
		last[ev.parent] = ev.at
	}
	return true
}

// loopSite is the range of loop event indices a site created — base is
// the index before the first (events base+1 .. base+count) — and the
// paths that summarized it, pairwise exclusive.
type loopSite struct {
	base, count int
	paths       []*pathNode
}

// diverged reports whether path is exclusive with every path that
// summarized the site: a reach from another side of some fork, whose
// summary merges with the site's events. A path that is a prefix of one
// of them, or extends one, is the same path reaching the site again.
func (site loopSite) diverged(path *pathNode) bool {
	for _, prior := range site.paths {
		if !path.exclusive(prior) {
			return false
		}
	}
	return true
}

// mentionsElsewhere reports whether the variable's fresh symbol is read
// by the event's other fields: its continue condition, the other
// variables' next values, its stores — a symbol read nowhere but its own
// next value is a temporary the body rewrites before reading.
func (ev *loopEvent) mentionsElsewhere(name string) bool {
	symbol := ev.fresh[name]
	if symbol == nil {
		return false
	}
	seen := map[*term]bool{}
	var walk func(t *term) bool
	walk = func(t *term) bool {
		if t == nil || seen[t] {
			return false
		}
		seen[t] = true
		if t.kind == termParam && t.name == symbol.name {
			return true
		}
		return walk(t.cond) || walk(t.left) || walk(t.right)
	}
	if walk(ev.cond) {
		return true
	}
	for other, next := range ev.next {
		if other != name && walk(next) {
			return true
		}
	}
	for _, stores := range ev.writes {
		for _, store := range stores {
			if walk(store.index) || walk(store.value) || walk(store.guard) {
				return true
			}
		}
	}
	return false
}

// mergeLoopEvents joins the summaries two paths made of one loop site:
// the path with condition cond summarized it as fresh, an earlier path
// as prior. The loop's shape — its variables, their widths and symbols,
// its nesting — must agree (the same instructions, or the same callee
// body, summarized twice), and each field over the inputs selects the
// summary of the path taken: the header values, the continue condition,
// the next values, the entry memories, and the iteration's stores. The
// paths are exclusive, so the select is exact on both and the later
// merges compose (a third path selects over the merged pair).
func mergeLoopEvents(cond *term, fresh, prior *loopEvent) (*loopEvent, string, bool) {
	if cond == nil {
		return nil, "a loop summarized twice on one path", false
	}
	trace := os.Getenv("OAK_VERIFY_TRACE") != ""
	if fresh.index != prior.index || fresh.parent != prior.parent || fresh.oakDerived != prior.oakDerived || len(fresh.vars) != len(prior.vars) {
		if trace {
			fmt.Fprintf(os.Stderr, "verify: loop merge: shape differs — fresh index %d parent %d oak-derived %v vars %v; prior index %d parent %d oak-derived %v vars %v\n", fresh.index, fresh.parent, fresh.oakDerived, fresh.vars, prior.index, prior.parent, prior.oakDerived, prior.vars)
			for _, ev := range []*loopEvent{fresh, prior} {
				for _, name := range ev.vars {
					fmt.Fprintf(os.Stderr, "  event %p %s: header %s, next %s, symbol read elsewhere %v\n", ev, name, ev.header[name], ev.next[name], ev.mentionsElsewhere(name))
				}
			}
		}
		return nil, "a loop whose shape differs between two paths", false
	}
	for k, name := range fresh.vars {
		if prior.vars[k] != name || fresh.width[name] != prior.width[name] || fresh.floats[name] != prior.floats[name] {
			if trace {
				fmt.Fprintf(os.Stderr, "verify: loop merge: variables differ at %d — fresh %v (width %d, header %s) prior %v (width %d, header %s)\n", k, fresh.vars, fresh.width[name], fresh.header[name], prior.vars, prior.width[prior.vars[k]], prior.header[prior.vars[k]])
			}
			return nil, "a loop whose loop-carried variables differ between two paths", false
		}
		if f, p := fresh.fresh[name], prior.fresh[name]; f == nil || p == nil || f.name != p.name || f.width != p.width {
			return nil, "a loop whose loop-carried symbols differ between two paths", false
		}
	}
	cond = truncate(cond, 1)
	select_ := func(a, b *term) *term {
		if a == nil || b == nil || equalTerms(a, b) {
			return a
		}
		return iteTerm(cond, a, b)
	}
	merged := &loopEvent{index: fresh.index, parent: fresh.parent, vars: fresh.vars, header: map[string]*term{}, fresh: fresh.fresh, width: fresh.width, next: map[string]*term{}, floats: fresh.floats, oakDerived: fresh.oakDerived, at: prior.at}
	for _, name := range fresh.vars {
		merged.header[name] = select_(fresh.header[name], prior.header[name])
		merged.next[name] = select_(fresh.next[name], prior.next[name])
	}
	merged.cond = select_(fresh.cond, prior.cond)
	merged.writes = mergeWrites(cond, fresh.writes, prior.writes)
	merged.entry = mergeWrites(cond, fresh.entry, prior.entry)
	if fresh.reached != nil && prior.reached != nil {
		merged.reached = binaryTerm("or", truncate(fresh.reached, 1), truncate(prior.reached, 1))
	}
	return merged, "", true
}

// writableSpanParams names the function's writable span parameters (`[*]T`)
// that the executor knows as scalar or record spans, sorted.
func writableSpanParams(fn *Function, spans map[string]int64, recordSpans map[string]recordSpanArg) []string {
	var out []string
	if fn == nil || fn.Signature == nil {
		return out
	}
	for _, param := range fn.Signature.Parameters {
		if param == nil || param.Name == nil || !isWritableSpan(param.Type) {
			continue
		}
		_, scalar := spans[param.Name.Value]
		_, record := recordSpans[param.Name.Value]
		if scalar || record {
			out = append(out, param.Name.Value)
		}
	}
	sort.Strings(out)
	return out
}

// writableSpanMemories flattens writable parameters to the memory names the
// executor logs: a scalar span is one memory, while a record span has one
// memory per scalar leaf or array field.
func writableSpanMemories(fn *Function, spans map[string]int64, recordSpans map[string]recordSpanArg) []string {
	var out []string
	for _, span := range writableSpanParams(fn, spans, recordSpans) {
		if arg, record := recordSpans[span]; record {
			out = append(out, arg.memories(span)...)
			continue
		}
		out = append(out, span)
	}
	sort.Strings(out)
	return out
}

// cellsStoredIn names the package cells a loop body stores: the body
// materializes a cell's address as `adrp xA, G; add xA, xA, :lo12:G` and
// stores through `[xA]` (nativegen globalAddress; the checker admits no
// other access), so the scan follows the symbol into the register it
// names and the store through it. Sorted; an aggregate global or one the
// function does not declare is left to the executor's refusal.
func (x *pathExecutor) cellsStoredIn(shape loopShape) []string {
	named := map[int]string{}
	stored := map[string]bool{}
	for i := shape.bodyStart; i < shape.bodyEnd; i++ {
		instr, isInstr := x.items[i].(Instruction)
		if !isInstr || len(instr.Operands) == 0 {
			continue
		}
		if isStoreMnemonic(instr.Mnemonic) && len(instr.Operands) == 2 {
			if mem, isMem := instr.Operands[1].(Memory); isMem && mem.Index == nil && mem.Offset == 0 {
				if name, isCell := named[mem.Base.Num]; isCell && mem.Base.Class == ClassX {
					if global, declared := x.globals[name]; declared && !global.Aggregate {
						stored[name] = true
					}
				}
			}
			continue
		}
		dest, isReg := instr.Operands[0].(Register)
		if !isReg || dest.Class == ClassV {
			continue
		}
		delete(named, dest.Num)
		if sym, isSym := instr.Operands[len(instr.Operands)-1].(Symbol); isSym && (instr.Mnemonic == "adrp" || instr.Mnemonic == "add") {
			named[dest.Num] = sym.Name
		}
	}
	out := make([]string, 0, len(stored))
	for name := range stored {
		out = append(out, name)
	}
	sort.Strings(out)
	return out
}

// summarizeCallInLoop is summarizeCall inside a loop's header or body: the
// callee's result is a term over the iteration's fresh symbols; a callee
// with memory effects (stores through spans, package cells) is refused,
// since the loop summary carries registers and frame slots, not memories.
func (x *pathExecutor) summarizeCallInLoop(instr Instruction, st *symbolicState) (string, bool) {
	cellsBefore := st.clone().globals
	reason, ok := x.summarizeCall(instr, st)
	if !ok {
		return reason, false
	}
	// A callee's stores through the caller's spans join the iteration's
	// write log (the loop's memory); a callee writing package cells is
	// refused, since the loop summary carries no cells.
	if name, differs := differingGlobalState(x.globals, cellsBefore, st.globals); differs {
		return fmt.Sprintf("a call writing package global %s in a loop", name), false
	}
	return "", true
}

// headerPathBudget bounds the paths a loop header's short-circuit
// branches may fork into.
const headerPathBudget = 16

// headerCondition is the loop's continue condition over the fresh state:
// the disjunction, over the header's paths, of "this path is taken and no
// exit test on it is taken". A guard's branch is skipped (its taken path
// traps, as the Oak side's element read does), an exit branch narrows the
// path to its fall-through, a forward branch to a label inside the header
// forks, a load reads the span as the executor does.
func (x *pathExecutor) headerCondition(shape loopShape, fresh *symbolicState) (*term, []*symbolicState, string, bool) {
	type headerPath struct {
		pc    int
		seg   int // the segment pc lies in
		cond  *term
		state *symbolicState
	}
	// The test ranges walked in order: the entry-only tests (invariant,
	// decided once before the header — the same on every iteration), then
	// the header's or the tail's tests.
	segments := [][2]int{{shape.testStart, shape.testEnd}}
	if shape.entryEnd > shape.entryStart {
		segments = [][2]int{{shape.entryStart, shape.entryEnd}, {shape.testStart, shape.testEnd}}
	}
	last := len(segments) - 1
	work := []headerPath{{pc: segments[0][0], seg: 0, cond: constTerm(1, 1), state: fresh.clone()}}
	var cont *term
	var fallThroughStates []*symbolicState
	paths := 0
	for len(work) > 0 {
		cur := work[len(work)-1]
		work = work[:len(work)-1]
		pc, seg, cond, st := cur.pc, cur.seg, cur.cond, cur.state
		for {
			if pc >= segments[seg][1] {
				if seg < last {
					seg++
					pc = segments[seg][0]
					continue
				}
				break
			}
			instr, isInstr := x.items[pc].(Instruction)
			if !isInstr {
				pc++
				continue
			}
			if isGuardBranch(x.items, x.labels, instr) {
				pc++
				continue
			}
			if isConditionalBranch(instr.Mnemonic) {
				taken, reason, ok := branchCondition(instr, st)
				if !ok {
					return nil, nil, reason, false
				}
				taken = truncate(taken, 1)
				target := x.labels[instr.Operands[len(instr.Operands)-1].(Symbol).Name]
				if shape.tail && target == shape.header {
					// The tail test's back edge: taken is the continue.
					cond = binaryTerm("and", cond, taken)
					pc++
					continue
				}
				if target < shape.bodyStart {
					if paths+len(work)+1 > headerPathBudget {
						return nil, nil, "more header paths than the verifier's budget", false
					}
					fork := &forkMark{pc: pc}
					takenState := st.clone()
					takenState.assume(taken, fork, true)
					work = append(work, headerPath{pc: target, seg: last, cond: binaryTerm("and", cond, taken), state: takenState})
					st.assume(binaryTerm("xor", taken, constTerm(1, 1)), fork, false)
				}
				cond = binaryTerm("and", cond, binaryTerm("xor", taken, constTerm(1, 1)))
				pc++
				continue
			}
			var reason string
			var ok bool
			switch {
			case instr.Mnemonic == "bl" || instr.Mnemonic == "call":
				reason, ok = x.summarizeCallInLoop(instr, st)
			case x.arch == ArchRV64:
				reason, ok = x.stepRV64(instr, st)
			case isFrameMemory(instr):
				reason, ok = x.frameAccess(instr, st)
			case isHeaderLoad(instr):
				reason, ok = x.load(instr, st)
			default:
				reason, ok = step(instr, st)
			}
			if !ok {
				return nil, nil, reason, false
			}
			pc++
		}
		paths++
		fallThroughStates = append(fallThroughStates, st)
		if cont == nil {
			cont = cond
		} else {
			cont = binaryTerm("or", cont, cond)
		}
	}
	if cont == nil {
		return constTerm(0, 1), fallThroughStates, "", true
	}
	return cont, fallThroughStates, "", true
}

// loopEventBudget bounds the data-dependent loops one body may hold.
const loopEventBudget = 32

// witnessWorkBudget bounds the work a loop proof's witness runs take in
// all — the machine's steps, and the Oak lowering's loop iterations at
// witnessIterationCost steps each: a cheap body runs every input
// loopWitnessInputs offers, one whose callees unroll their loops on each
// input runs a few.
const (
	witnessWorkBudget    = 1 << 21
	witnessIterationCost = 256
)

// bodyEnd is one path through a loop body: the condition under which the
// path is taken and the state it reaches the back edge with.
type bodyEnd struct {
	cond  *term
	state *symbolicState
}

// valueOf is a register's value at the end of the path; a register the
// path never wrote keeps its header symbol.
func (e bodyEnd) valueOf(reg int, header *symbolicState) *term {
	if value, written := e.state.regs[reg]; written {
		return value
	}
	return header.regs[reg]
}

// valueOfVar is a loop-carried variable's value at the end of the path:
// a general register (`r9`), a half of a vector register (`v8.lo`,
// `v8.hi`), an RV64 floating-point register (`f8`), or a frame slot with
// its width in bytes (`s-144:8`, `s-100:4`).
func (e bodyEnd) valueOfVar(name string, header *symbolicState) *term {
	var reg int
	var side string
	var addr int64
	switch {
	case len(name) > 1 && name[0] == 'r':
		fmt.Sscanf(name, "r%d", &reg)
		return e.valueOf(reg, header)
	case len(name) > 1 && name[0] == 'f':
		fmt.Sscanf(name, "f%d", &reg)
		if value, written := e.state.fregs[reg]; written {
			return value
		}
		return header.fregs[reg]
	case strings.HasPrefix(name, "global:"):
		cell := strings.TrimPrefix(name, "global:")
		if value, written := e.state.globals[cell]; written {
			return value
		}
		return header.globals[cell]
	case len(name) > 1 && name[0] == 'v':
		fmt.Sscanf(name, "v%d.%s", &reg, &side)
		value, bound := e.state.vregs[reg]
		if !bound {
			value = header.vregs[reg]
		}
		if side == "hi" {
			return value.halves()[1]
		}
		return value.halves()[0]
	default:
		size := int64(8)
		fmt.Sscanf(name, "s%d:%d", &addr, &size)
		if value, ok := e.state.loadSlot(addr, size); ok {
			return value
		}
		value, _ := header.loadSlot(addr, size)
		return value
	}
}

// hasIndexedFrameStore reports a store in the body through an x register
// with a register index (a frame array element at a data-dependent index;
// registerFrameMemory decides at run time whether the base is a frame
// address).
func (x *pathExecutor) hasIndexedFrameStore(shape loopShape) bool {
	for i := shape.bodyStart; i < shape.bodyEnd; i++ {
		instr, isInstr := x.items[i].(Instruction)
		if !isInstr || !isStoreMnemonic(instr.Mnemonic) || len(instr.Operands) == 0 {
			continue
		}
		if mem, isMem := instr.Operands[len(instr.Operands)-1].(Memory); isMem && mem.Base.Class == ClassX && mem.Index != nil {
			return true
		}
	}
	return false
}

// hasInnerLoopOrCall reports a recognized inner loop exit or a call inside
// the body.
func (x *pathExecutor) hasInnerLoopOrCall(shape loopShape) bool {
	for i := shape.bodyStart; i < shape.bodyEnd; i++ {
		if _, isExit := x.loopExits[i]; isExit {
			return true
		}
		if instr, isInstr := x.items[i].(Instruction); isInstr && (instr.Mnemonic == "bl" || instr.Mnemonic == "call") {
			return true
		}
	}
	return false
}

// flattenSelects rewrites, in every value the merged state holds, a
// select whose one arm is a select with the same other arm as one select
// on the conjunction (or disjunction) of the conditions: a fork nested in
// a fork's side and merged first, `c1 ? (c2 ? x : y) : y`, is the Oak
// side's `c1 && c2 ? x : y` — one conditional over one condition, which
// the coupling proof's arm rule (impliesEqualByArms) then compares
// condition to condition, where the nested select's outer condition
// alone matches nothing. Machine-side only: the Oak lowering's spelling
// stays the Lean transliteration's.
func flattenSelects(s *symbolicState) {
	for reg, value := range s.regs {
		s.regs[reg] = flattenSelect(value)
	}
	for addr, slot := range s.frame {
		s.frame[addr] = frameSlot{value: flattenSelect(slot.value), width: slot.width}
	}
	for reg, value := range s.vregs {
		lanes := make([]*term, len(value.lanes))
		for k, lane := range value.lanes {
			lanes[k] = flattenSelect(lane)
		}
		s.vregs[reg] = vecValue{bits: value.bits, lanes: lanes}
	}
	for reg, value := range s.fregs {
		s.fregs[reg] = flattenSelect(value)
	}
}

// flattenSelect is flattenSelects on one term: `c1 ? (c2 ? x : y) : y` to
// `c1 ∧ c2 ? x : y`, and `c1 ? x : (c2 ? x : y)` to `c1 ∨ c2 ? x : y`,
// repeated while a shape matches.
func flattenSelect(t *term) *term {
	if t == nil {
		return nil
	}
	for t.kind == termIte {
		switch {
		case t.left.kind == termIte && equalTerms(t.left.right, t.right):
			t = iteTerm(binaryTerm("and", truncate(t.cond, 1), truncate(t.left.cond, 1)), t.left.left, t.right)
		case t.right.kind == termIte && equalTerms(t.right.left, t.left):
			t = iteTerm(binaryTerm("or", truncate(t.cond, 1), truncate(t.right.cond, 1)), t.left, t.right.right)
		default:
			return t
		}
	}
	return t
}

// bodyJoins is the function's join points (joinPoints) for the loop
// bodies' forks, computed once; the executor's own joins (x.joins) are
// set only on its second run past the path budget, and this leaves that
// choice to it.
func (x *pathExecutor) bodyJoins() map[int]int {
	if x.bodyJoinsMemo == nil {
		joins := joinPoints(x.items, x.labels)
		if joins == nil {
			joins = map[int]int{}
		}
		x.bodyJoinsMemo = joins
	}
	return x.bodyJoinsMemo
}

// outgoingArea is the size of the function's outgoing argument area — the
// largest stack area any call in the body passes its arguments through
// (asm.LayoutArguments over the callee's signature, as the backend sizes
// it) — at the bottom of the frame, from the moved sp. Zero when no call
// passes arguments on the stack. Memoized.
func (x *pathExecutor) outgoingArea() int64 {
	if x.outgoingMemo != nil {
		return *x.outgoingMemo
	}
	most := int64(0)
	if x.fn != nil && x.arch != ArchRV64 {
		for _, item := range x.items {
			instr, isInstr := item.(Instruction)
			if !isInstr || (instr.Mnemonic != "bl" && instr.Mnemonic != "call") || len(instr.Operands) == 0 {
				continue
			}
			sym, isSym := instr.Operands[0].(Symbol)
			if !isSym {
				continue
			}
			callee := x.fn.Callees[sym.Name]
			if callee == nil {
				if base, suffixed := strings.CutSuffix(sym.Name, VectorEntrySuffix(x.arch)); suffixed {
					callee = x.fn.Callees[base]
				}
			}
			if callee == nil {
				continue
			}
			var classes []ArgClass
			for _, arg := range classifyArguments(callee.Parameters, x.fn.Composites) {
				if arg.problem == "" {
					classes = append(classes, arg.class)
				}
			}
			if _, bytes := LayoutArguments(classes, x.fn.PackedStackArgs); bytes > most {
				most = bytes
			}
		}
	}
	x.outgoingMemo = &most
	return most
}

// loopsInside reports a loop inside the shape's body: an inner loop's
// exit, or a call to a function whose Oak body holds a loop (a call to a
// loop-free callee does not count, so the two sides agree whether the
// callee was expanded in place or called: bodyHasLoop is the Oak side's
// reading of the same body). Memoized per shape.
func (x *pathExecutor) loopsInside(shape loopShape) bool {
	if known, seen := x.loopsInsideMemo[shape.bodyStart]; seen {
		return known
	}
	inside := false
	for i := shape.bodyStart; i < shape.bodyEnd && !inside; i++ {
		if _, isExit := x.loopExits[i]; isExit {
			inside = true
			break
		}
		instr, isInstr := x.items[i].(Instruction)
		if !isInstr || (instr.Mnemonic != "bl" && instr.Mnemonic != "call") || len(instr.Operands) == 0 || x.fn == nil {
			continue
		}
		sym, isSym := instr.Operands[0].(Symbol)
		if !isSym {
			continue
		}
		callee := x.fn.Callees[sym.Name]
		if callee == nil {
			if base, suffixed := strings.CutSuffix(sym.Name, VectorEntrySuffix(x.arch)); suffixed {
				callee = x.fn.Callees[base]
			}
		}
		if callee != nil && callee.Body != nil && bodyHasLoop(callee.Body, x.fn.Callees) {
			inside = true
		}
	}
	if x.loopsInsideMemo == nil {
		x.loopsInsideMemo = map[int]bool{}
	}
	x.loopsInsideMemo[shape.bodyStart] = inside
	return inside
}

// bodyHasLoop reports a loop under the node: a while statement, or a call
// to one of the functions whose body has one (transitively).
func bodyHasLoop(node ast.Node, functions map[string]*ast.FunctionStatement) bool {
	return bodyHasLoopSeen(node, functions, map[*ast.FunctionStatement]bool{})
}

func bodyHasLoopSeen(node ast.Node, functions map[string]*ast.FunctionStatement, seen map[*ast.FunctionStatement]bool) bool {
	found := false
	var walk func(v reflect.Value)
	walk = func(v reflect.Value) {
		if found {
			return
		}
		switch v.Kind() {
		case reflect.Interface, reflect.Pointer:
			if v.IsNil() {
				return
			}
			switch n := v.Interface().(type) {
			case *ast.WhileStatement:
				found = true
				return
			case *ast.InvocationExpression:
				if ident, isIdent := n.Function.(*ast.Identifier); isIdent {
					if callee, known := functions[ident.Value]; known && callee != nil && callee.Body != nil && !seen[callee] {
						seen[callee] = true
						if bodyHasLoopSeen(callee.Body, functions, seen) {
							found = true
							return
						}
					}
				}
			}
			walk(v.Elem())
		case reflect.Struct:
			for i := 0; i < v.NumField() && !found; i++ {
				if v.Type().Field(i).IsExported() {
					walk(v.Field(i))
				}
			}
		case reflect.Slice:
			for i := 0; i < v.Len() && !found; i++ {
				walk(v.Index(i))
			}
		}
	}
	walk(reflect.ValueOf(node))
	return found
}

// trapAhead reports whether taking the branch at instr to target reaches
// the trap block through labels, unconditional jumps, and conditional
// branches the taking decides (bindZeroTest), with no other instruction
// in between — the shape an `assert(a && b)` lowers to.
func (x *pathExecutor) trapAhead(target int, state *symbolicState, instr Instruction) bool {
	st := state.clone()
	bindZeroTest(instr, st, true)
	pc := target
	for hops := 0; pc < len(x.items) && hops < 8; hops++ {
		next, isInstr := x.items[pc].(Instruction)
		if !isInstr {
			pc++
			hops--
			continue
		}
		switch next.Mnemonic {
		case "brk", "ebreak":
			return true
		case "b", "j":
			label, known := x.labels[next.Operands[0].(Symbol).Name]
			if !known {
				return false
			}
			pc = label
		default:
			if !isConditionalBranch(next.Mnemonic) || len(next.Operands) == 0 {
				return false
			}
			cond, _, ok := branchCondition(next, st)
			if !ok || cond.kind != termConst {
				return false
			}
			if cond.value == 0 {
				pc++
				continue
			}
			sym, isSym := next.Operands[len(next.Operands)-1].(Symbol)
			if !isSym {
				return false
			}
			label, known := x.labels[sym.Name]
			if !known {
				return false
			}
			if isTrapBlock(x.items, label) {
				return true
			}
			bindZeroTest(next, st, true)
			pc = label
		}
	}
	return false
}

// bodyPathBudget bounds the paths one loop body may fork into.
const bodyPathBudget = 64

// runBody executes a loop body from its first instruction to the back edge
// along every path.
func (x *pathExecutor) runBody(shape loopShape, state *symbolicState) ([]bodyEnd, string, bool) {
	// A fork whose two sides meet again inside the body (their immediate
	// post-dominator, joinPoints) runs each side to the join, where the
	// paths park; the parked states merge into one continuation (the
	// executor's mergeStates: each register, slot, and vector a select on
	// the path condition) — linear in the forks where running each side
	// to the back edge is exponential (a body testing four vectors for
	// any set lane before four conditional calls: eighty-one paths).
	type joinGroup struct {
		join    int
		pending int // sides still running toward the join
		parked  []*symbolicState
		conds   []*term
		takens  []bool
		parent  *pathNode  // the path before the fork
		outer   *joinGroup // the enclosing join, if any
	}
	type frontier struct {
		pc    int
		cond  *term
		state *symbolicState
		group *joinGroup // the join this path runs toward, nil for the back edge
		taken bool       // the fork's taken side (the select's first arm at the merge)
	}
	work := []frontier{{pc: shape.bodyStart, cond: constTerm(1, 1), state: state}}
	var ends []bodyEnd
	// arrived settles a path of a join group: parked at the join, or gone
	// (a trap); when every side has arrived, the group merges and its
	// continuation joins the work.
	arrived := func(g *joinGroup) {
		g.pending--
		if g.pending > 0 {
			return
		}
		if len(g.parked) == 0 {
			return
		}
		// The merge selects on each side's condition relative to the fork
		// (conditionBelow: the path above it is shared), the fall-through
		// side the select's first arm — the backend lays a conditional's
		// first arm on the fall-through and branches to the other, so
		// `c ? then : else` reads `ite(c, fallthrough, taken)`, the shape
		// the Oak side spells and the coupling proof matches term for
		// term (the ends of an unjoined body merged in the same order).
		// The taken sides stand, the fall-through ones select over them.
		order := make([]int, 0, len(g.parked))
		for i := range g.parked {
			if !g.takens[i] {
				order = append(order, i)
			}
		}
		for i := range g.parked {
			if g.takens[i] {
				order = append(order, i)
			}
		}
		acc := g.parked[order[len(order)-1]]
		cond := g.conds[order[len(order)-1]]
		var below *term
		if rel := acc.path.conditionBelow(g.parent); rel != nil {
			below = rel
		}
		mergeable := true
		for k := len(order) - 2; k >= 0; k-- {
			i := order[k]
			side := g.parked[i]
			rel := side.path.conditionBelow(g.parent)
			if rel == nil {
				rel = constTerm(1, 1)
			}
			merged, ok := x.mergeTwo(rel, side, acc)
			if !ok {
				mergeable = false
				break
			}
			flattenSelects(merged)
			acc = merged
			cond = binaryTerm("or", g.conds[i], cond)
			if below != nil {
				below = binaryTerm("or", rel, below)
			}
		}
		if !mergeable {
			for i, parkedState := range g.parked {
				work = append(work, frontier{pc: g.join, cond: g.conds[i], state: parkedState, group: g.outer})
			}
			return
		}
		if below == nil {
			below = constTerm(1, 1)
		}
		acc.path = &pathNode{parent: g.parent, cond: below}
		work = append(work, frontier{pc: g.join, cond: cond, state: acc, group: g.outer})
	}
	for len(work) > 0 {
		cur := work[len(work)-1]
		work = work[:len(work)-1]
		pc, cond, st := cur.pc, cur.cond, cur.state
		parked := false
		// A jump out of the body's range: to the trap block (a decided
		// guard, an assert's failing side), which delivers no iteration
		// and is dropped — left as an end it would hold the counter at its
		// header value, a spurious arm in the summary; anywhere else is
		// outside the subset.
		dropped := false
		leaves := func(target int) (outside bool, reason string) {
			if target >= shape.bodyStart && target < shape.bodyEnd {
				return false, ""
			}
			if isTrapBlock(x.items, target) {
				dropped = true
				return true, ""
			}
			return true, "a branch out of a loop body"
		}
		for pc < shape.bodyEnd && !dropped && !parked {
			if cur.group != nil && pc == cur.group.join {
				// This side reached the join: parked for the merge.
				cur.group.parked = append(cur.group.parked, st)
				cur.group.conds = append(cur.group.conds, cond)
				cur.group.takens = append(cur.group.takens, cur.taken)
				parked = true
				break
			}
			instr, isInstr := x.items[pc].(Instruction)
			if !isInstr {
				pc++
				continue
			}
			x.steps++
			if x.steps > stepBudget {
				return nil, "more instructions than the verifier's unrolling budget", false
			}
			switch instr.Mnemonic {
			case "b", "j":
				target := x.labels[instr.Operands[0].(Symbol).Name]
				if outside, reason := leaves(target); outside {
					if reason != "" {
						return nil, reason, false
					}
					break
				}
				pc = target
				continue
			case "b.", "cbz", "cbnz", "tbz", "tbnz", "beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz", "bnez", "bgez", "bltz", "blez", "bgtz":
				branch, reason, ok := branchCondition(instr, st)
				if !ok {
					return nil, reason, false
				}
				target := x.labels[instr.Operands[len(instr.Operands)-1].(Symbol).Name]
				inner, isLoopExit := x.loopExits[pc]
				if branch.kind == termConst && !(isLoopExit && branch.value == 0 && x.summarizeCounted(inner, instr, st)) {
					if branch.value != 0 {
						if outside, reason := leaves(target); outside {
							if reason != "" {
								return nil, reason, false
							}
							break
						}
						pc = target
					} else {
						pc++
					}
					continue
				}
				// An undecided exit of an inner recognized loop (or the
				// decided one of a counted loop over a loop, as in the
				// executor's branch handling): summarize it and continue
				// past its exit, still inside this body.
				if isLoopExit {
					post, reason, ok := x.summarizeLoop(inner, instr, st)
					if !ok {
						return nil, reason, false
					}
					st = post
					pc = inner.exitLabel
					continue
				}
				if isTrapBlock(x.items, target) || x.trapAhead(target, st, instr) {
					// The trap arm delivers no result; the body continues on
					// the fall-through path, outside the trapping inputs —
					// under the index bound the guard establishes. The same
					// when the taken side reaches the trap through branches
					// the taking decides (`assert(a && b)`: the `cbz` that
					// skips the second test lands on the `cbz` to the trap
					// with the same register, zero): a fork there would
					// leave the first test in the path condition, and so
					// in the iteration's store guards, which the Oak side
					// (its assert a no-op) does not carry.
					st.noteTrapGuard(instr)
					pc++
					continue
				}
				if len(ends)+len(work) >= bodyPathBudget {
					return nil, "more paths in a loop body than the verifier's budget", false
				}
				taken := truncate(branch, 1)
				notTaken := binaryTerm("xor", taken, constTerm(1, 1))
				fork := &forkMark{pc: pc}
				parent := st.path
				takenState := st.clone()
				takenState.assume(taken, fork, true)
				bindZeroTest(instr, takenState, true)
				bindZeroTest(instr, st, false)
				st.assume(notTaken, fork, false)
				if join, hasJoin := x.bodyJoins()[pc]; hasJoin && target > pc && join > pc && join < shape.bodyEnd && (cur.group == nil || join <= cur.group.join) {
					// Both sides run to the join and park there.
					g := &joinGroup{join: join, pending: 2, parent: parent, outer: cur.group}
					work = append(work, frontier{pc: target, cond: binaryTerm("and", cond, taken), state: takenState, group: g, taken: true})
					work = append(work, frontier{pc: pc + 1, cond: binaryTerm("and", cond, notTaken), state: st, group: g})
					parked = true // this frontier continues as the group's sides
					break
				}
				work = append(work, frontier{pc: target, cond: binaryTerm("and", cond, taken), state: takenState, group: cur.group, taken: cur.taken})
				if cur.group != nil {
					cur.group.pending++ // a side more toward the enclosing join
				}
				cond = binaryTerm("and", cond, notTaken)
				pc++
				continue
			case "bl", "call":
				// A program function in the body: summarized on the path's
				// state, its result a term over the fresh symbols.
				x.callAt = pc
				if reason, ok := x.summarizeCallInLoop(instr, st); !ok {
					return nil, reason, false
				}
				pc++
				continue
			case "ldr", "ldrb", "ldrh", "str", "strb", "strh", "ldp", "stp":
				if isFrameMemory(instr) {
					// A spill or a reload: the frame slots are loop-carried
					// state (summarizeLoop), so the frame model follows them.
					if reason, ok := x.frameAccess(instr, st); !ok {
						return nil, reason, false
					}
					pc++
					continue
				}
				if mem, base, isFrame := registerFrameMemory(instr, st); isFrame {
					// An element of a frame array through its address register;
					// at a data-dependent index the store forgets the region.
					if reason, ok := x.registerFrameAccess(instr, st, mem, base); !ok {
						return nil, reason, false
					}
					pc++
					continue
				}
				if instr.Mnemonic == "ldp" {
					// A pair load off a span element address: two loads
					// (nativegen/pair_loads.go).
					if reason, ok := x.loadPair(instr, st); !ok {
						return nil, reason, false
					}
					pc++
					continue
				}
				if !isLoad(instr.Mnemonic) {
					// A store to a package cell: the loop-carried cell's new
					// value on this path (summarizeLoop pairs it with the
					// Oak side's cell local).
					if handled, reason, ok := x.globalStore(instr, st); handled {
						if !ok {
							return nil, reason, false
						}
						pc++
						continue
					}
					// A store through a span: into the iteration's memory
					// (the loop's marker), recorded for the coupling proof.
					if handled, reason, ok := x.spanStore(instr, st); handled {
						if !ok {
							return nil, reason, false
						}
						pc++
						continue
					}
					return nil, "a store in a loop body", false
				}
				if dest, isReg := instr.Operands[0].(Register); isReg && dest.Class == ClassV {
					if reason, ok := x.loadVector(instr, st); !ok {
						return nil, reason, false
					}
					pc++
					continue
				}
				if reason, ok := x.load(instr, st); !ok {
					return nil, reason, false
				}
			case "adrl":
				// A constant table's address inside the body (the CRC table
				// of a byte loop): the base of the span its Oak name
				// denotes, as on a straight path.
				dest := instr.Operands[0].(Register)
				sym, isSym := instr.Operands[1].(Symbol)
				if !isSym || x.fn == nil {
					return nil, "adrl without a constant table", false
				}
				if _, known := x.fn.Tables[sym.Name]; !known {
					return nil, "adrl of a symbol that is not a constant table", false
				}
				st.write(dest, paramTerm(spanBaseName(TableName(sym.Name)), 64))
				pc++
				continue
			default:
				if x.arch == ArchRV64 {
					// The RV64 lane: its own semantics; frame memory and
					// stores stay outside a summarized body as on AArch64.
					base := rv64Base(instr)
					if len(base.Operands) == 2 {
						if mem, isMem := base.Operands[1].(Memory); isMem && mem.Base.Class != ClassSP && rv64FloatStores[base.Mnemonic] != 0 {
							return nil, "a floating-point store in a loop body", false
						}
					}
					if reason, ok := x.stepRV64(instr, st); !ok {
						return nil, reason, false
					}
					pc++
					continue
				}
				if hasVectorOperand(instr) {
					if reason, ok := x.stepVector(instr, st); !ok {
						return nil, reason, false
					}
					pc++
					continue
				}
				if reason, ok := step(instr, st); !ok {
					return nil, reason, false
				}
			}
			pc++
		}
		if parked {
			if cur.group != nil && pc == cur.group.join {
				arrived(cur.group)
			}
			continue
		}
		if dropped {
			if cur.group != nil {
				arrived(cur.group) // a side gone into the trap arrives with nothing
			}
			continue
		}
		if cur.group != nil {
			// A side reaching the back edge before its join (a join past
			// the body's range would not have been taken): an end.
			arrived(cur.group)
		}
		ends = append(ends, bodyEnd{cond: cond, state: st})
	}
	return ends, "", true
}

// upperClear reports whether a 64-bit term is provably zero in its upper
// 32 bits: a small constant, a 32-bit-declared parameter, a mask by at
// most 32 bits, a select of a 32-bit element, a 1/0 comparison, or a
// select between such terms.
func upperClear(t *term, declared map[string]int) bool {
	switch t.kind {
	case termConst:
		return t.value <= mask(32)
	case termParam:
		if w, known := declared[t.name]; known {
			return w <= 32
		}
		return strings.HasPrefix(t.name, "loop") && t.width <= 32
	case termCmp:
		return true
	case termSelect, termFloat, termQuant:
		return t.width <= 32
	case termIte:
		return upperClear(t.left, declared) && upperClear(t.right, declared)
	case termBinary:
		if t.op == "and" {
			if t.right.kind == termConst && t.right.value <= mask(32) {
				return true
			}
			if t.left.kind == termConst && t.left.value <= mask(32) {
				return true
			}
		}
		return t.width <= 32
	}
	return false
}

// recordSpanAtRoot finds the record-span shape currently in scope for a
// caller-rooted span. In an inlined callee the shape is keyed by the callee's
// parameter while writes and loop memory are keyed by spanRoot(parameter).
// Multiple aliases of one root must agree on the shape; otherwise lowering
// fails closed instead of choosing one by map iteration order.
func (lo *oakLowering) recordSpanAtRoot(root string) (recordSpanArg, string, bool) {
	var found recordSpanArg
	has := false
	for name, arg := range lo.recordSpans {
		if lo.spanRoot(name) != root {
			continue
		}
		if has && !reflect.DeepEqual(found, arg) {
			return recordSpanArg{}, fmt.Sprintf("incompatible record-span aliases of %s", root), false
		}
		found, has = arg, true
	}
	return found, "", has
}

// loopEvent summarizes the Oak `while` whose condition did not fold, then
// leaves the locals at their fresh symbols for the code after the loop.
func (lo *oakLowering) loopEvent(loop *ast.WhileStatement) (string, bool) {
	if lo.concrete != nil {
		return "a loop that a witness run could not decide", false
	}
	if len(lo.loops) >= loopEventBudget {
		if os.Getenv("OAK_VERIFY_TRACE") != "" {
			for _, ev := range lo.loops {
				fmt.Fprintf(os.Stderr, "verify: oak loop event %d (parent %d): vars %v\n", ev.index, ev.parent, ev.vars)
			}
		}
		return "more data-dependent loops than the verifier's budget", false
	}
	// The loop-carried locals are those the body assigns and that exist
	// before the loop; a local declared inside the body is the body's own.
	// An aggregate local (a vector, an owned array) is carried leaf by
	// leaf: each lane or element is its own variable (`error[3]`).
	assigned := map[string]bool{}
	assignedLocals(loop.Body, assigned)
	declared := map[string]bool{}
	declaredLocals(loop.Body, declared)
	// The Oak path condition at the loop (an arm the loop sits in): a call
	// summary's callee loops carry it as their reaching condition, with the
	// machine's path at the call (summarizeCall).
	ev := &loopEvent{index: lo.loopBase + len(lo.loops) + 1, header: map[string]*term{}, fresh: map[string]*term{}, width: map[string]int{}, next: map[string]*term{}, oakPath: lo.path}
	if n := len(lo.loopStack); n > 0 {
		ev.parent = lo.loopStack[n-1]
	}
	var carried []string
	for name := range assigned {
		if !declared[name] {
			carried = append(carried, name)
		}
	}
	sort.Strings(carried)
	aggregates := map[string]bool{}
	for _, name := range carried {
		if view, isView := lo.views[name]; isView {
			// A store through a view: its owner is the carried aggregate.
			if aggregates[view.owner] {
				continue
			}
			name = view.owner
		}
		local, isLocal := lo.locals[name]
		if !isLocal {
			if _, isSpan := lo.spans[name]; isSpan {
				continue // a store through a span: the loop's memory, below
			}
			if _, isRecordSpan := lo.recordSpans[name]; isRecordSpan {
				continue // a store through a record span: its leaf memories, below
			}
			return fmt.Sprintf("an assignment to %s (not a local)", name), false
		}
		if local.agg != nil {
			aggregates[name] = true
			leaves := map[string]*oakValue{}
			leafRefs(local.agg, name, leaves)
			paths := make([]string, 0, len(leaves))
			for path := range leaves {
				paths = append(paths, path)
			}
			sort.Strings(paths)
			for _, path := range paths {
				leaf := leaves[path]
				ev.vars = append(ev.vars, path)
				ev.width[path] = leaf.typ.width
				ev.header[path] = leaf.scalar
				fresh := paramTerm(ev.freshName(path), leaf.typ.width)
				lo.fresh[fresh.name] = leaf.typ.width
				ev.fresh[path] = fresh
				leaf.scalar = fresh
			}
			continue
		}
		ev.vars = append(ev.vars, name)
		ev.width[name] = local.width
		ev.header[name] = local.value
		if _, isFloat := lo.floats[name]; isFloat {
			if ev.floats == nil {
				ev.floats = map[string]bool{}
			}
			ev.floats[name] = true
		}
		fresh := paramTerm(ev.freshName(name), local.width)
		lo.fresh[fresh.name] = local.width
		ev.fresh[name] = fresh
		local.value = fresh
	}
	// The spans the body stores through take the loop's memory marker
	// (asm/effects.go): the body reads the iteration's unknown memory and
	// its stores layer on it; the asm side places the same marker.
	// The writable spans are the caller-rooted ones (writableSpans, the
	// function's `[*]T` parameters): inside an inlined or summarized
	// callee the names in scope are aliases of them, so the marker is
	// keyed by the root, as the write logs are.
	storedSpans := make([]string, 0, len(lo.writableSpans))
	contracts := map[string]spanContract{}
	for span := range lo.writableSpans {
		arg, reason, isRecord := lo.recordSpanAtRoot(span)
		if reason != "" {
			return reason, false
		}
		if isRecord {
			// A span of records: one marker per leaf memory, at the leaf's width.
			for memory, width := range arg.memoryWidths(span) {
				contracts[memory] = spanContract{elemWidth: width}
				storedSpans = append(storedSpans, memory)
			}
			continue
		}
		if contract, isSpan := lo.spans[span]; isSpan {
			contracts[span] = contract
		} else if contract, isRoot := lo.rootContracts[span]; isRoot {
			contracts[span] = contract
		} else {
			continue
		}
		storedSpans = append(storedSpans, span)
	}
	sort.Strings(storedSpans)
	before := map[string]int{}
	ev.entry = map[string][]*spanWrite{}
	for _, span := range storedSpans {
		ev.entry[span] = lo.writes[span]
		lo.writes = appendMarker(lo.writes, span, ev.index)
		if lo.path != nil {
			// A loop inside a conditional's arm: past the conditional the
			// memory is the loop's on the paths that ran it and the entry
			// memory on the others — the guard the asm side's join gives
			// its marker (mergeWrites).
			log := lo.writes[span]
			log[len(log)-1].guard = lo.path
		}
		lo.spans[loopMemoryName(ev.index, span)] = contracts[span] // the unknown memory's element width
		before[span] = len(lo.writes[span])
	}
	cond, reason, ok := lo.lowerCondition(loop.Condition)
	if !ok {
		return reason, false
	}
	ev.cond = truncate(cond, 1)
	entryCond, entryKnown := ev.entryCondition()
	if !entryKnown {
		return "the loop's entry condition could not be reconstructed", false
	}
	if os.Getenv("OAK_VERIFY_TRACE") != "" {
		fmt.Fprintf(os.Stderr, "verify oak loop %d: cond %s\n", ev.index, ev.cond)
		for _, name := range ev.vars {
			fmt.Fprintf(os.Stderr, "verify oak loop %d:   %s header %s\n", ev.index, name, ev.header[name])
		}
	}
	// A `while` whose condition is already false touches no memory, so the
	// marker holds only where the loop is entered (entryCondition), on top
	// of the enclosing arm's condition when the loop is inside one.
	if entryCond != nil {
		for _, span := range storedSpans {
			guardMarker(lo.writes[span][:before[span]], entryCond)
		}
	}
	lo.loops = append(lo.loops, ev)
	lo.loopStack = append(lo.loopStack, ev.index)
	reason, ok = lo.lowerLoopBody(loop.Body)
	lo.loopStack = lo.loopStack[:len(lo.loopStack)-1]
	if !ok {
		return reason, false
	}
	// The iteration's stores, for the coupling proof; past the loop the
	// span's contents are the marker's unknown memory.
	for _, span := range storedSpans {
		log := lo.writes[span]
		stores := append([]*spanWrite{}, log[before[span]:]...)
		if len(stores) == 0 {
			// Successful lowering of the whole iteration found no write
			// to this exact memory.  The pass below frames an untouched
			// record leaf across the loop — the entry memory restored,
			// the marker dropped — instead of replacing it with an
			// unconstrained loop memory; it needs the entry, which stays
			// recorded until then (an inner loop that dropped its entry
			// here left the pass deleting the whole log, the enclosing
			// loop's marker with it). Unknown stores never reach here:
			// lowering them fails closed before an event is accepted.
			continue
		}
		if ev.writes == nil {
			ev.writes = map[string][]*spanWrite{}
		}
		ev.writes[span] = stores
		lo.writes[span] = log[:before[span]:before[span]]
	}
	// The marker of a memory the iteration never stores to is dropped for
	// the entry memory, as the asm side drops it (summarizeLoop): a record
	// span marks one memory per leaf, and a loop writing one field left
	// every other field an unknown memory that nothing had written.
	for _, span := range storedSpans {
		if len(ev.writes[span]) > 0 {
			continue
		}
		if len(ev.entry[span]) == 0 {
			delete(lo.writes, span)
		} else {
			lo.writes[span] = ev.entry[span]
		}
		delete(ev.writes, span)
		delete(ev.entry, span)
	}
	for _, name := range ev.vars {
		if local, isLocal := lo.locals[name]; isLocal && local.agg == nil {
			ev.next[name] = local.value
			local.value = ev.fresh[name]
		}
	}
	for name := range aggregates {
		// The body may have replaced the aggregate's leaves (an assignment
		// copies), so the leaves are found again by path.
		leaves := map[string]*oakValue{}
		leafRefs(lo.locals[name].agg, name, leaves)
		for path, leaf := range leaves {
			if _, carried := ev.fresh[path]; !carried {
				return fmt.Sprintf("the aggregate %s changed shape across the loop", name), false
			}
			ev.next[path] = leaf.scalar
			leaf.scalar = ev.fresh[path]
		}
	}
	return "", true
}

// leafRefs lists an aggregate's scalar leaves by access path, as leafTerms
// names them, with the values themselves so a leaf can be rebound.
func leafRefs(v *oakValue, prefix string, into map[string]*oakValue) {
	if v.scalar != nil {
		into[prefix] = v
		return
	}
	for name, field := range v.fields {
		leafRefs(field, prefix+"."+name, into)
	}
	for k, elem := range v.elems {
		leafRefs(elem, fmt.Sprintf("%s[%d]", prefix, k), into)
	}
}

func assignedLocals(body *ast.BlockStatement, into map[string]bool) {
	if body == nil {
		return
	}
	for _, stmt := range body.Statements {
		switch s := stmt.(type) {
		case *ast.AssignmentStatement:
			into[s.Name.Value] = true
		case *ast.IndexAssignmentStatement:
			// An element or field write: the aggregate it lands in is carried.
			if root := indexRootIdent(s.Target); root != "" {
				into[root] = true
			}
		case *ast.WhileStatement:
			assignedLocals(s.Body, into)
		case *ast.ExpressionStatement:
			// A statement-level conditional assigns in its arms.
			if match, isMatch := s.Expression.(*ast.MatchExpression); isMatch {
				for _, arm := range match.Arms {
					if block, isBlock := arm.Body.(*ast.BlockExpression); isBlock {
						assignedLocals(block.Block, into)
					}
				}
			}
		}
	}
}

// indexRootIdent is the local an index chain `a[i].f[j]` starts from.
func indexRootIdent(e ast.Expression) string {
	for e != nil {
		switch n := e.(type) {
		case *ast.Identifier:
			return n.Value
		case *ast.IndexExpression:
			e = n.Left
		default:
			return ""
		}
	}
	return ""
}

// declaredLocals collects the locals a loop body declares — at its top
// level, in nested loops, and in the arms of statement-level conditionals
// (a local declared in an arm and assigned in a loop nested there is the
// body's own, not loop-carried), mirroring assignedLocals.
func declaredLocals(body *ast.BlockStatement, into map[string]bool) {
	if body == nil {
		return
	}
	for _, stmt := range body.Statements {
		switch s := stmt.(type) {
		case *ast.VariableDeclaration:
			into[s.Name.Value] = true
		case *ast.WhileStatement:
			declaredLocals(s.Body, into)
		case *ast.ExpressionStatement:
			if match, isMatch := s.Expression.(*ast.MatchExpression); isMatch {
				for _, arm := range match.Arms {
					if block, isBlock := arm.Body.(*ast.BlockExpression); isBlock {
						declaredLocals(block.Block, into)
					}
				}
			}
		}
	}
}

// loopWitnessInputs are small concrete inputs: under them the loops
// unroll within budget. Scalars and span lengths vary; elements come from
// the fixed memory.
func loopWitnessInputs(fn *Function, sig *ast.FunctionStatement) []map[string]uint64 {
	var names []string
	// A vector parameter is its lane leaves (vectorParamValue): on a
	// witness every lane is zero but one, so a body that loops over the
	// set lanes (a block's candidates) runs one inner loop, not sixteen.
	type vectorParam struct {
		name  string
		lanes int
		width int
	}
	var vectors []vectorParam
	for _, param := range sig.Parameters {
		if _, _, isSpan := spanShape(param.Type); isSpan {
			names = append(names, spanLenName(param.Name.Value))
			continue
		}
		if shape, isVector := vectorShape(param.Type); isVector && !shape.Float {
			vectors = append(vectors, vectorParam{name: param.Name.Value, lanes: shape.Lanes, width: laneWidth(shape)})
			continue
		}
		if comp, isComposite := fn.Composites[typeText(param.Type)]; isComposite && len(comp.Fields) > 0 {
			continue // its leaves are appended below
		}
		names = append(names, param.Name.Value)
	}
	names = append(names, compositeParamLeaves(fn, sig)...)
	// A Bool parameter holds 0 or 1 (the C enum): its witness values are
	// masked to the bit, an input outside being ill-typed on both sides.
	bools := map[string]bool{}
	for _, param := range sig.Parameters {
		if param != nil && param.Name != nil && typeText(param.Type) == "Bool" {
			bools[param.Name.Value] = true
		}
	}
	maskBools := func(env map[string]uint64) map[string]uint64 {
		for name := range bools {
			if value, bound := env[name]; bound {
				env[name] = value & 1
			}
		}
		return env
	}
	withVectors := func(env map[string]uint64, a, b uint64) map[string]uint64 {
		for i, v := range vectors {
			set := int((a + uint64(i)) % uint64(v.lanes))
			for k := 0; k < v.lanes; k++ {
				env[spanElemName(v.name, int64(k))] = 0
			}
			env[spanElemName(v.name, int64(set))] = (b*37 + 11) & mask(v.width)
		}
		return env
	}
	// The larger values clear the bounds checks of a body that reads a
	// table of several 16-byte vectors before its loops (a UTF-8 kernel
	// reads 64 bytes of tables): under the small ones alone every input
	// traps there and no witness decides anything.
	small := []uint64{0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 33, 63, 64, 65, 80, 81}
	var inputs []map[string]uint64
	if len(names) == 0 {
		if len(vectors) == 0 {
			return []map[string]uint64{{}}
		}
		for _, a := range small {
			inputs = append(inputs, withVectors(map[string]uint64{}, a, a))
		}
		return inputs
	}
	for _, a := range small {
		if len(names) == 1 {
			inputs = append(inputs, maskBools(withVectors(map[string]uint64{names[0]: a}, a, a)))
			continue
		}
		for _, b := range small {
			env := map[string]uint64{names[0]: a, names[1]: b}
			for i, extra := range names[2:] {
				env[extra] = (a*7 + b*3 + uint64(i)) % 19
			}
			inputs = append(inputs, maskBools(withVectors(env, a, b)))
		}
	}
	// A body that indexes its spans by its scalar parameters (a literal's
	// bounds at `starts[j + 1]`, a byte at `base + l`) traps on every input
	// above, where the lengths and the scalars are drawn from one small
	// set; a second family holds every span long and varies the scalars
	// alone, below the length.
	var lens, scalars []string
	for _, name := range names {
		if strings.HasPrefix(name, "len(") {
			lens = append(lens, name)
		} else {
			scalars = append(scalars, name)
		}
	}
	if len(lens) > 0 && len(scalars) > 0 {
		const long = 40
		few := []uint64{0, 1, 3, 5, 8, 13, 17}
		for _, a := range few {
			for _, b := range few {
				env := map[string]uint64{}
				for _, name := range lens {
					env[name] = long
				}
				env[scalars[0]] = a
				if len(scalars) > 1 {
					env[scalars[1]] = b
				}
				for i, extra := range scalars[min(2, len(scalars)):] {
					env[extra] = (a*7 + b*3 + uint64(i)) % 19
				}
				inputs = append(inputs, maskBools(withVectors(env, a, b)))
				if len(scalars) == 1 {
					break
				}
			}
		}
	}
	return inputs
}

// coupling is one Oak loop variable paired with a register: r = a*x + b.
type coupling struct {
	event int // event index
	local string
	reg   string
	a     int
	b     *term
	ext   string // "" (same width), "zext" or "sext": a 64-bit register carrying a widened 32-bit variable
}

// show spells the coupling for the verdict (built only for the couplings
// chosen: a candidate's offset term may be large).
func (c coupling) show() string {
	switch {
	case c.a == 1 && c.b.kind == termConst && c.b.value == 0:
		return c.local + "↔" + c.reg
	case c.a == 1:
		return fmt.Sprintf("%s = %s + %s", c.reg, c.local, c.b)
	default:
		return fmt.Sprintf("%s = %s - %s", c.reg, c.b, c.local)
	}
}

// widen applies a coupling's widening to a 32-bit term.
func widen(t *term, ext string, width int) *term {
	switch ext {
	case "zext":
		return zeroExtend(t, width)
	case "sext":
		return extendTerm(zeroExtend(t, width), 32, width, true)
	}
	return t
}

// loopSlot is a coupling slot: one Oak loop variable, or the lanes of an
// aggregate local that fill one 64-bit machine symbol.
type loopSlot struct {
	event  int
	key    string   // event and locals, the identity of the slot
	name   string   // as shown: `acc` or `acc[0..7]`
	locals []string // the lanes in order, lane k at bits k*lane
	lane   int      // a lane's width; the variable's for a single local
}

func (s loopSlot) width() int { return s.lane * len(s.locals) }

// pack is the slot's value under a valuation of its locals: the local's
// value, or the lanes packed (asm/verify_vector.go packLanes).
func (s loopSlot) pack(values map[string]*term) *term {
	if len(s.locals) == 1 {
		return values[s.locals[0]]
	}
	lanes := make([]*term, len(s.locals))
	for k, local := range s.locals {
		lanes[k] = adaptWidth(values[local], s.lane)
	}
	return packLanes(lanes, s.lane)[0]
}

// laneSlots groups each event's variables into slots. The lanes
// `root[0]`..`root[n-1]` of one aggregate, all of width w dividing 64 and
// numbered without gaps, form groups of 64/w consecutive lanes when they
// fill whole groups; any other variable is a slot of its own.
func laneSlots(events []*loopEvent, machine []*loopEvent) []loopSlot {
	var slots []loopSlot
	for k, ev := range events {
		// The lanes stay single when the machine event holds symbols at the
		// lane's width — a byte array in one-byte frame slots — and are
		// packed when it holds them only as wider words (vector halves).
		singles := func(w, lanes int) bool {
			count := 0
			for _, name := range machine[k].vars {
				if machine[k].width[name] == w {
					count++
				}
			}
			return count >= lanes
		}
		type lane struct {
			index int
			local string
		}
		byRoot := map[string][]lane{}
		var roots []string
		var scalars []string
		for _, local := range ev.vars {
			open := strings.LastIndex(local, "[")
			if open < 0 || !strings.HasSuffix(local, "]") {
				scalars = append(scalars, local)
				continue
			}
			index, err := strconv.Atoi(local[open+1 : len(local)-1])
			if err != nil {
				scalars = append(scalars, local)
				continue
			}
			root := local[:open]
			if _, seen := byRoot[root]; !seen {
				roots = append(roots, root)
			}
			byRoot[root] = append(byRoot[root], lane{index: index, local: local})
		}
		single := func(local string) loopSlot {
			return loopSlot{event: k, key: fmt.Sprintf("%d:%s", k, local), name: local, locals: []string{local}, lane: ev.width[local]}
		}
		for _, local := range scalars {
			slots = append(slots, single(local))
		}
		for _, root := range roots {
			lanes := byRoot[root]
			sort.Slice(lanes, func(i, j int) bool { return lanes[i].index < lanes[j].index })
			w := ev.width[lanes[0].local]
			per := 0
			if w > 0 && 64%w == 0 {
				per = 64 / w
			}
			grouped := per > 1 && len(lanes)%per == 0 && !singles(w, len(lanes))
			for i, l := range lanes {
				if l.index != i || ev.width[l.local] != w {
					grouped = false
				}
			}
			if !grouped {
				for _, l := range lanes {
					slots = append(slots, single(l.local))
				}
				continue
			}
			for start := 0; start < len(lanes); start += per {
				var locals []string
				for _, l := range lanes[start : start+per] {
					locals = append(locals, l.local)
				}
				name := fmt.Sprintf("%s[%d..%d]", root, start, start+per-1)
				if per == 1 {
					name = locals[0]
				}
				slots = append(slots, loopSlot{event: k, key: fmt.Sprintf("%d:%s", k, name), name: name, locals: locals, lane: w})
			}
		}
	}
	return slots
}

// verifyLoops is the loop-mode verdict: witnesses, then the coupling proof.
func verifyLoops(fn *Function, sig *ast.FunctionStatement, oakBody ast.Expression, exec *pathExecutor, lowering *oakLowering, asmTerm, oakTerm *term, width int) Verdict {
	trusted := func(reason string) Verdict {
		return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (%s) — trusted per docs/spec/94-assembler.md §5", fn.Name, reason)}
	}
	asmLoops, oakLoops := exec.loops, lowering.loops
	switch {
	case len(asmLoops) == 0:
		return trusted("the Oak body has a data-dependent loop but the asm body does not")
	case len(oakLoops) == 0:
		if os.Getenv("OAK_VERIFY_TRACE") != "" {
			for _, ev := range asmLoops {
				fmt.Fprintf(os.Stderr, "verify %s: asm loop event %d (parent %d, oak-derived %v): vars %v, cond %s\n", fn.Name, ev.index, ev.parent, ev.oakDerived, ev.vars, ev.cond)
			}
		}
		return trusted("the asm body has a data-dependent loop but the Oak body does not")
	case len(asmLoops) != len(oakLoops):
		if os.Getenv("OAK_VERIFY_TRACE") != "" {
			for _, ev := range asmLoops {
				fmt.Fprintf(os.Stderr, "verify %s: asm loop event %d (parent %d, oak-derived %v): vars %v, cond %s\n", fn.Name, ev.index, ev.parent, ev.oakDerived, ev.vars, ev.cond)
			}
			for _, ev := range oakLoops {
				fmt.Fprintf(os.Stderr, "verify %s: oak loop event %d (parent %d): vars %v, cond %s\n", fn.Name, ev.index, ev.parent, ev.vars, ev.cond)
			}
		}
		return trusted(fmt.Sprintf("the asm body has %d data-dependent loops, the Oak body %d", len(asmLoops), len(oakLoops)))
	}
	if len(asmLoops) > loopEventBudget {
		// The events of several summarized calls add up past what one
		// body may hold (loopEventBudget bounds each summary, not their
		// sum): the coupling search over twenty-one events ran for an
		// hour in `add_bits` and decided nothing.
		return trusted(fmt.Sprintf("more data-dependent loops than the verifier's budget (%d, with the callees' summarized)", len(asmLoops)))
	}
	for k := range asmLoops {
		if asmLoops[k].parent != oakLoops[k].parent {
			if os.Getenv("OAK_VERIFY_TRACE") != "" {
				for _, ev := range asmLoops {
					fmt.Fprintf(os.Stderr, "verify %s: asm loop event %d (parent %d, oak-derived %v): vars %v\n", fn.Name, ev.index, ev.parent, ev.oakDerived, ev.vars)
				}
				for _, ev := range oakLoops {
					fmt.Fprintf(os.Stderr, "verify %s: oak loop event %d (parent %d): vars %v\n", fn.Name, ev.index, ev.parent, ev.vars)
				}
			}
			return trusted("the data-dependent loops nest differently on the two sides")
		}
	}
	// Witnesses: concrete inputs decide every loop. A unit function (no
	// result term: the span memories are the comparison) has none here;
	// its proof is the coupling alone.
	checked := 0
	work := 0
	for _, env := range loopWitnessInputs(fn, sig) {
		if !lowering.inDomain(env) {
			continue // a union tag outside its variants: not a well-typed input
		}
		// The pass is bounded by the work its machine runs did, not by
		// their number: a body whose callees unroll their loops on every
		// input (add_bits spent three minutes here) stops after a few,
		// a cheap body runs every input.
		if work > witnessWorkBudget {
			break
		}
		asmValue, asmRun, reasonA, okA := executeBodyChunk(fn, sig, env, 0, exec.resultChunk)
		if asmRun != nil {
			work += asmRun.steps
		}
		concrete := prepareLowering(fn, sig, env)
		concrete.resultChunk = exec.resultChunk
		var oakValue *term
		var reasonO string
		var okO bool
		if asmTerm != nil {
			oakValue, _, reasonO, okO = concrete.resultTerm(fn, sig, oakBody)
		} else {
			// A unit function: the concrete run's memories are the comparison.
			reasonO, okO = concrete.lowerUnitBody(oakBody)
		}
		work += witnessIterationCost * concrete.work
		if os.Getenv("OAK_VERIFY_TRACE") != "" {
			fmt.Fprintf(os.Stderr, "witness %s %v: asm ok=%v %q trap=%v; oak ok=%v %q\n", fn.Name, env, okA, reasonA, asmValue == trapPath, okO, reasonO)
		}
		names := make([]string, 0, len(env))
		for name := range env {
			names = append(names, name)
		}
		sort.Strings(names)
		if okA && asmValue == trapPath && okO && !concrete.witnessTrapped {
			// The machine traps on this input and the Oak body yields a
			// value (its own traps are noted in a witness run): the
			// trapping inputs are not the same on the two sides.
			return Verdict{Kind: VerdictMismatch, Message: fmt.Sprintf("asm unit %s disagrees with its Oak body at %s (fixed element contents): the machine traps where Oak yields a value", fn.Name, describeEnv(names, env))}
		}
		if !okA || !okO || asmValue == trapPath || concrete.witnessTrapped {
			// Beyond the unrolling budget on this input, or an input on
			// which both bodies trap (an element read past a length the
			// input set to zero): no value to compare.
			continue
		}
		if asmTerm != nil {
			got, want := truncate(maskResult(fn, sig, asmValue, exec.resultChunk), width).eval(env), oakValue.eval(env)
			if got != want {
				return Verdict{Kind: VerdictMismatch, Message: fmt.Sprintf("asm unit %s disagrees with its Oak body at %s (fixed element contents): asm yields %d, Oak yields %d", fn.Name, describeEnv(names, env), got, want)}
			}
		}
		// The memories the concrete runs leave: every store's index is a
		// constant on a concrete input, so the two logs are compared at
		// every index either side stored (elsewhere both hold the fixed
		// memory) — a wrong store in a loop body is refuted here.
		if span, index, got, want, differ := concreteMemoriesDiffer(asmRun.writes, concrete.writes, lowering, env); differ {
			return Verdict{Kind: VerdictMismatch, Message: fmt.Sprintf("asm unit %s disagrees with its Oak body at %s (fixed element contents) in the span %s at index %d: asm leaves %d, Oak leaves %d", fn.Name, describeEnv(names, env), span, index, got, want)}
		}
		if cell, got, want, differ := concreteCellsDiffer(asmRun, concrete, env); differ {
			return Verdict{Kind: VerdictMismatch, Message: fmt.Sprintf("asm unit %s disagrees with its Oak body at %s (fixed element contents) in package global %s: asm leaves %d, Oak leaves %d", fn.Name, describeEnv(names, env), cell, got, want)}
		}
		checked++
	}
	// No concrete input deciding the loops within budget (a callee's loop
	// over a count the memory holds) leaves the witnesses empty; the
	// coupling below is an induction that needs none, so the decision
	// proceeds and the verdict says how many inputs agreed.
	evidence := func(reason string) Verdict {
		return Verdict{Kind: VerdictWitnessed, Message: fmt.Sprintf("asm unit %s: agrees with its Oak body on %d concrete inputs (evidence, not proof: %s)", fn.Name, checked, reason)}
	}
	widthOfName := func(name string) int {
		var k int
		var reg string
		if n, _ := fmt.Sscanf(name, "loop%d.%s", &k, &reg); n == 2 && k >= 1 && k <= len(asmLoops) {
			if w, isReg := asmLoops[k-1].width[reg]; isReg {
				return w
			}
		}
		return lowering.declaredWidth(name)
	}
	// Every implication of this proof spends from one budget, each
	// bounded by what is left, and an undecided one costs its whole
	// diagram: a search that keeps failing near the per-decision budget
	// ends as evidence in a few tries. The budgets are the same with and
	// without witnesses: the search bound used to be eight times larger
	// for a body with them, when only the bodies whose inputs never
	// trapped had any, and once the witnesses reached the bodies indexing
	// their spans by their scalars, the ones whose coupling has no
	// solution spent minutes under the larger bound — the prover's
	// `tuple_type_acc`, 5 s to 165 s. The bound is measured: the deepest
	// proof on the prover and the kernels needs 291 nodes (`valid_with`),
	// and the seven bodies past 512 all end as evidence.
	proofNodes, searchBudget := loopProofNodeBudget, couplingSearchBudget
	budget := &nodeBudget{remaining: proofNodes}
	implies := func(premise, a, b *term) (bool, bool) {
		return impliesEqualWithin(premise, a, b, widthOfName, budget)
	}

	// The coupling search substitutes into and walks the events' terms for
	// every candidate; terms past the size budget (a body of summarized
	// calls to large functions) leave the loop as evidence rather than
	// minutes of search.
	if nodes := loopTermNodes(asmLoops, oakLoops); nodes > loopTermNodeBudget {
		return evidence(fmt.Sprintf("the loops' terms hold %d nodes, past the coupling's budget of %d", nodes, loopTermNodeBudget))
	}
	// Coupling. A candidate pairs an Oak loop variable x of event k with a
	// register r of the same width of the matching asm event through an
	// affine relation r = a*x + b, a ∈ {+1, -1}, with b read off the header
	// values under the substitution chosen so far (an inner loop's header
	// mentions the outer loop's symbols) and required to mention no symbol
	// of the event itself. Equality is a = +1, b = 0. The search runs over
	// every variable of every event; at the leaf, each event's condition
	// agreement and preservation are bit-level implications from its
	// premise — its invariant and guard, its ancestors' invariants and
	// guards, and its children's exit premises (invariant and negated
	// guard), since an outer body's successors mention the inner loops'
	// exit symbols.
	// A slot is one Oak loop variable — or, for the lanes of a vector or
	// byte-array local (`acc[0]`..`acc[7]`), the group of lanes that fills
	// one 64-bit machine symbol: a vector register half or a frame slot
	// holds the lanes packed, lane k at bits k*w, so the coupling pairs the
	// pack of the group with the symbol (asm/verify_vector.go packLanes).
	slots := laneSlots(oakLoops, asmLoops)
	// exitRead marks the loop symbols read past their own event: by an
	// enclosing event's next values, a later event's header, a store, or
	// the result — the variables whose value after the loop matters. A
	// variable the body reads after the loop pairs with a register read
	// after the loop; an accumulator's spill slot, reloaded past the loop,
	// rather than the register that held it inside the body, which the
	// header values (both zero) cannot tell apart.
	exitReadAsm := exitReadSymbols(asmLoops, asmTerm)
	exitReadOak := exitReadSymbols(oakLoops, oakTerm)
	// Slots whose one-iteration value mentions fewer of the event's own
	// variables come first: their register's value after one iteration then
	// mentions only coupled symbols as soon as they are paired, so a wrong
	// pairing is refuted at once instead of after every completion below it
	// (an accumulator that folds the other variables in is paired last).
	dependencies := func(s loopSlot) int {
		mentioned := map[string]bool{}
		collectParams(s.pack(oakLoops[s.event].next), mentioned)
		own := fmt.Sprintf("loop%d.", oakLoops[s.event].index)
		count := 0
		for name := range mentioned {
			if strings.HasPrefix(name, own) {
				count++
			}
		}
		return count
	}
	sort.SliceStable(slots, func(i, j int) bool {
		if slots[i].event != slots[j].event {
			return slots[i].event < slots[j].event
		}
		return dependencies(slots[i]) < dependencies(slots[j])
	})
	// Invariant candidates per event: the guard weakened to its closure
	// (`x < e` gives `x ≤ e`) when it holds at the header and one iteration
	// preserves it under the guard; else the trivial invariant.
	invariants := make([]*term, len(oakLoops))
	for k, ev := range oakLoops {
		invariants[k] = constTerm(1, 1)
		guard := ev.cond
		if guard.kind != termCmp {
			continue
		}
		weakened := map[string]string{"lo": "ls", "ls": "ls", "hi": "hs", "hs": "hs", "lt": "le", "le": "le", "gt": "ge", "ge": "ge"}
		code, ok := weakened[guard.op]
		if !ok {
			continue
		}
		inv := cmpTerm(code, guard.left, guard.right)
		atHeader := map[string]*term{}
		afterBody := map[string]*term{}
		for _, local := range ev.vars {
			atHeader[ev.freshName(local)] = ev.header[local]
			afterBody[ev.freshName(local)] = ev.next[local]
		}
		holds, decidedEntry := implies(constTerm(1, 1), substitute(inv, atHeader), constTerm(1, 1))
		preserved, decidedStep := implies(binaryTerm("and", truncate(inv, 1), truncate(guard, 1)), substitute(inv, afterBody), constTerm(1, 1))
		if decidedEntry && holds && decidedStep && preserved {
			invariants[k] = truncate(inv, 1)
		}
	}
	children := map[int][]int{}
	for k, ev := range oakLoops {
		children[ev.parent-1] = append(children[ev.parent-1], k)
	}
	// notRunPins of event k: a loop that never ran leaves its variables at
	// their header values — the scalar counterpart of "loops that never
	// ran keep the entry memory" (spanEqualSplitting). The loop runs where
	// its guard holds at the header and the machine's path reached it;
	// otherwise each loop symbol is its header value. Without the fact, a
	// machine that skips a loop under a hoisted guard (`len(a) < 4` around
	// a vector main loop) carries the header value into the next loop
	// where the Oak side carries the loop symbol, and the two are not
	// provably one. Only the symbols the terms at hand mention are pinned,
	// and only scalars whose header value is a constant or a symbol (a
	// vector kernel's sixteen lane variables, each pinned to a lane of the
	// loop before, blast past the node budget for nothing); nil when none
	// is.
	notRunPins := func(k int, sigma map[string]*term, mentioned map[string]bool) *term {
		ev := oakLoops[k]
		pins := constTerm(1, 1)
		pinned := false
		for _, v := range ev.vars {
			fresh, header := ev.fresh[v], ev.header[v]
			if fresh == nil || header == nil || fresh.width != header.width || fresh.width > 64 || !mentioned[fresh.name] {
				continue
			}
			if strings.Contains(v, "[") || (header.kind != termConst && header.kind != termParam) {
				continue
			}
			pins = binaryTerm("and", pins, truncate(cmpTerm("eq", fresh, header), 1))
			pinned = true
		}
		if !pinned {
			return nil
		}
		headerSigma := map[string]*term{}
		for v, fresh := range ev.fresh {
			if header, ok := ev.header[v]; ok {
				headerSigma[fresh.name] = header
			}
		}
		runs := truncate(substitute(ev.cond, headerSigma), 1)
		if k < len(asmLoops) && asmLoops[k] != nil {
			if reached := asmLoops[k].reached; reached != nil {
				runs = binaryTerm("and", runs, truncate(substitute(reached, sigma), 1))
			}
		}
		return binaryTerm("or", runs, pins)
	}
	// exitPremise of event k: its invariant and negated guard, and its
	// children's exit premises.
	var exitPremise func(k int, sigma map[string]*term) *term
	exitPremise = func(k int, sigma map[string]*term) *term {
		ev := oakLoops[k]
		premise := binaryTerm("and", substitute(invariants[k], sigma), binaryTerm("xor", truncate(substitute(ev.cond, sigma), 1), constTerm(1, 1)))
		for _, child := range children[k] {
			premise = binaryTerm("and", premise, exitPremise(child, sigma))
		}
		return premise
	}
	// bodyPremise of event k: its invariant — and its guard only when
	// checking one iteration, never when checking that the guards agree
	// (assuming the Oak guard would make any asm guard it implies look
	// equal) — the invariants and guards of its ancestors, and its
	// children's exit premises.
	bodyPremise := func(k int, sigma map[string]*term, underGuard bool) *term {
		premise := substitute(invariants[k], sigma)
		if underGuard {
			premise = binaryTerm("and", premise, truncate(substitute(oakLoops[k].cond, sigma), 1))
		}
		if reached := asmLoops[k].reached; reached != nil {
			// The machine's summary holds where the path reached the loop.
			premise = binaryTerm("and", premise, truncate(substitute(reached, sigma), 1))
		}
		// The loops before this one at the same level ran or left their
		// symbols at their header values: this loop's header values and
		// continue condition may read them (under the coupling, an asm
		// register's header value spells the earlier loop's symbol).
		if earlier := earlierSiblings(k, oakLoops); len(earlier) > 0 {
			mentioned := map[string]bool{}
			for _, v := range oakLoops[k].vars {
				collectParams(oakLoops[k].header[v], mentioned)
			}
			if asmEv := asmLoops[k]; asmEv != nil {
				for _, v := range asmEv.vars {
					collectParams(substitute(asmEv.header[v], sigma), mentioned)
				}
				collectParams(substitute(asmEv.cond, sigma), mentioned)
			}
			for _, j := range earlier {
				if pins := notRunPins(j, sigma, mentioned); pins != nil {
					premise = binaryTerm("and", premise, pins)
				}
			}
		}
		for at := oakLoops[k].parent - 1; at >= 0; at = oakLoops[at].parent - 1 {
			premise = binaryTerm("and", premise, binaryTerm("and", substitute(invariants[at], sigma), truncate(substitute(oakLoops[at].cond, sigma), 1)))
			if reached := asmLoops[at].reached; reached != nil {
				premise = binaryTerm("and", premise, truncate(substitute(reached, sigma), 1))
			}
		}
		for _, child := range children[k] {
			premise = binaryTerm("and", premise, exitPremise(child, sigma))
		}
		return premise
	}
	chosen := map[string]coupling{}
	used := map[string]bool{} // asm fresh symbol names already paired
	sigma := map[string]*term{}
	var failure string
	// candidatesFor lists the pairings open to a slot; taken names the
	// symbols other slots hold, which a conflict-directed search charges to
	// the depths that took them when no candidate is left.
	candidatesFor := func(s loopSlot) (out []coupling, taken []string) {
		oakEv, asmEv := oakLoops[s.event], asmLoops[s.event]
		hx := s.pack(oakEv.header)
		for _, reg := range asmEv.vars {
			if asmEv.oakDerived && reg != s.name {
				// A callee's loop taken from its Oak body on both sides: the
				// variables are the same locals under the same names, and
				// the pairing is the identity — no search over the others.
				continue
			}
			if used[asmEv.freshName(reg)] {
				taken = append(taken, asmEv.freshName(reg))
				continue
			}
			// A 64-bit register may carry a 32-bit Oak variable widened (the
			// RV64 lane has no 32-bit register view): zero-extended by a
			// 64-bit increment kept below 2^32 by the loop's premise, or
			// sign-extended by the W-forms (addw, Oak.RiscV.addw_eq). Each
			// widening is a candidate image; the coupling is r = ext(x) + b at
			// 64 bits and one iteration must preserve it. A lane group is
			// paired at its packed width, as r = pack(x) + b only.
			if !asmEv.oakDerived && strings.HasPrefix(reg, "f") && !oakEv.floats[s.name] {
				continue // the RV64 float file holds float locals only
			}
			var widenings []string
			signs := []int{1, -1}
			switch {
			case asmEv.width[reg] == s.width():
				widenings = []string{""}
			case len(s.locals) == 1 && asmEv.width[reg] == 64 && s.width() == 32 && strings.HasPrefix(reg, "r"):
				widenings = []string{"zext", "sext"}
			case len(s.locals) == 1 && s.width() == 1 && (asmEv.width[reg] == 32 || asmEv.width[reg] == 64) && strings.HasPrefix(reg, "r"):
				// A Bool local: 0 or 1 in a general register, zero-extended
				// (the C enum's word, `cset`, `sltu`).
				widenings = []string{"zext"}
			case len(s.locals) == 1 && (s.width() == 16 || s.width() == 8) && (asmEv.width[reg] == 32 || asmEv.width[reg] == 64) && strings.HasPrefix(reg, "r"):
				// A u16/u8 (i16/i8) counter in a general register: the
				// lane keeps it zero-extended (`and #0xFFFF`, `uxth`) or
				// sign-extended (`sxth`) after each step — the OS pilot's
				// `i: u16` over max_pages in reset. Each widening is a
				// candidate image; one iteration must preserve it.
				widenings = []string{"zext", "sext"}
			case len(s.locals) == 1 && oakEv.floats[s.name] && asmEv.width[reg] == 64 && s.width() == 32 && (strings.HasPrefix(reg, "v") || strings.HasPrefix(reg, "f")):
				// An f32 local in the low lane of a v register (a scalar
				// write zeroes the rest) or in an RV64 f register (the file's
				// low-bits convention): zero-extended only.
				widenings = []string{"zext"}
			default:
				continue
			}
			if len(s.locals) > 1 || asmEv.oakDerived || s.width() == 1 {
				signs = []int{1} // a lane group, a callee's own local, or a Bool: never negated
			}
			// A register the iteration leaves as it found it cannot be an
			// affine image of a variable the iteration changes, nor a
			// changing register of an unchanging variable: neither pairing
			// is ever preserved, and each would cost a decision over the
			// body's terms (an inner loop carrying the outer counters).
			if regFixed, varFixed := isFreshSymbol(asmEv.next[reg], asmEv.fresh[reg]), slotUnchanged(s, oakEv); regFixed != varFixed {
				continue
			}
			for _, ext := range widenings {
				hx := widen(hx, ext, asmEv.width[reg])
				hr := substitute(asmEv.header[reg], sigma)
				if s.width() == 1 && maxValueDeclared(hr, widthOfName) > 1 && !isUncoupledLoopSymbol(hr, sigma) {
					// A Bool variable pairs with a register holding a 0/1
					// value at the header, not with an address or a count
					// offset by the flag: those pairings are never preserved
					// and each costs a decision. A header that is an outer
					// loop's register not yet coupled (the viability pass, an
					// outer slot still open) is unknown and stays a candidate;
					// once coupled it is the outer Oak variable's symbol, and
					// its declared width decides.
					continue
				}
				for _, a := range signs {
					var b *term
					switch {
					case a == 1 && equalTerms(hr, hx):
						b = constTerm(0, hr.width) // equality: the header values are one term
					case a == 1:
						// The offset in its canonical spelling: the two
						// headers may be one value spelled apart (`start
						// > n ? n : start` read at 32 bits through a
						// 64-bit mask on the machine side), whose
						// difference canonicalizes to zero.
						b = canonical(binaryTerm("sub", hr, hx))
					default:
						b = canonical(binaryTerm("add", hr, hx))
					}
					if lf := b.linearAt(b.width); lf != nil && len(lf.coeffs) == 0 {
						// The header values differ by a constant once
						// normalized (`16 * g` against `g * 16`, `x + 1 - 1`):
						// the offset is that constant, and an equality when
						// zero — a candidate the search then spells and
						// decides as one, not as a difference of two terms
						// through every obligation's diagram.
						b = constTerm(lf.constant, b.width)
					}
					mentioned := map[string]bool{}
					collectParams(b, mentioned)
					own := fmt.Sprintf("loop%d.", oakEv.index)
					invariant := true
					for name := range mentioned {
						if strings.HasPrefix(name, own) || strings.HasPrefix(name, fmt.Sprintf("loop%d.r", asmEv.index)) {
							invariant = false
						}
					}
					if !invariant {
						continue
					}
					out = append(out, coupling{event: s.event, local: s.name, reg: reg, a: a, b: b, ext: ext})
				}
			}
		}
		// The likely pairings first: a register the event's continue
		// condition reads (the counter the exit test compares — an
		// unpaired one leaves the condition undecidable), then an equality
		// before an affine image with an offset (an address temporary
		// `base + i` is an image of the counter too, but the counter's own
		// register is the one the loop turns on).
		if os.Getenv("OAK_VERIFY_TRACE") != "" {
			var regs []string
			for _, c := range out {
				regs = append(regs, c.show())
			}
			fmt.Fprintf(os.Stderr, "verify %s: candidates for %s of loop %d: %v (asm vars %v)\n", fn.Name, s.name, s.event+1, regs, asmEv.vars)
		}
		inCond := map[string]bool{}
		collectParams(asmEv.cond, inCond)
		oakRead := false
		for _, local := range s.locals {
			if exitReadOak[oakEv.freshName(local)] {
				oakRead = true
			}
		}
		rank := func(c coupling) int {
			r := 0
			if exitReadAsm[asmEv.freshName(c.reg)] != oakRead {
				r += 4
			}
			if !inCond[asmEv.freshName(c.reg)] {
				r += 2
			}
			if c.a != 1 || c.b.kind != termConst || c.b.value != 0 {
				r++
			}
			return r
		}
		sort.SliceStable(out, func(i, j int) bool { return rank(out[i]) < rank(out[j]) })
		return out, taken
	}
	trace := os.Getenv("OAK_VERIFY_TRACE") != ""
	// resolved: the term mentions no asm loop symbol still to be coupled.
	resolved := func(t *term) bool {
		mentioned := map[string]bool{}
		collectParams(t, mentioned)
		for name := range mentioned {
			var k int
			var reg string
			if n, _ := fmt.Sscanf(name, "loop%d.%s", &k, &reg); n == 2 && k >= 1 && k <= len(asmLoops) {
				if _, isAsm := asmLoops[k-1].width[reg]; isAsm && sigma[name] == nil {
					return false
				}
			}
		}
		return true
	}
	// verified: the slots whose one-iteration obligation a valuation pass
	// has already checked under the current choices (pendingRefuted).
	verified := map[string]bool{}
	// depthOf: the search depth at which each asm symbol was paired, for
	// the conflict sets of conflict-directed backjumping.
	depthOf := map[string]int{}
	// conflictOf is the set of depths whose choices an obligation depends
	// on: the slots owning the asm symbols its asm side mentions.
	// An asm loop symbol the obligation mentions that no slot has paired
	// (a register that mirrors a variable, chosen for it while the loop's
	// own register went unpaired) could be taken by a slot at any depth:
	// such a failure depends on every depth, so the search backtracks to
	// each of them rather than passing the failure up.
	conflictOf := func(terms ...*term) map[int]bool {
		mentioned := map[string]bool{}
		for _, t := range terms {
			collectParams(t, mentioned)
		}
		set := map[int]bool{}
		unpairedEvents := map[int]bool{}
		for name := range mentioned {
			if depth, paired := depthOf[name]; paired {
				set[depth] = true
				continue
			}
			var k int
			var reg string
			if n, _ := fmt.Sscanf(name, "loop%d.%s", &k, &reg); n == 2 && k >= 1 && k <= len(asmLoops) {
				if _, isVar := asmLoops[k-1].width[reg]; isVar {
					unpairedEvents[k-1] = true
				}
			}
		}
		if len(unpairedEvents) > 0 {
			// The slots of the same event could have taken the symbol.
			for _, depth := range depthOf {
				if depth < len(slots) && unpairedEvents[slots[depth].event] {
					set[depth] = true
				}
			}
		}
		return set
	}
	// preservation is slot s's one-iteration obligation under coupling c
	// and the current substitution: (premise, Oak side, asm side, whether
	// the asm side mentions only coupled symbols).
	preservation := func(s loopSlot, c coupling) (premise, next, asmNext *term, isResolved bool) {
		oakEv, asmEv := oakLoops[s.event], asmLoops[s.event]
		asmNext = substitute(asmEv.next[c.reg], sigma)
		next = widen(substitute(s.pack(oakEv.next), sigma), c.ext, asmEv.width[c.reg])
		if c.a == 1 {
			next = binaryTerm("add", next, c.b)
		} else {
			next = binaryTerm("sub", c.b, next)
		}
		return bodyPremise(s.event, sigma, true), next, asmNext, resolved(asmNext)
	}
	// pendingRefuted prunes the search: the one-iteration obligation of a
	// chosen slot, and an event's continue-condition agreement, are checked
	// on valuations as soon as their asm side mentions only coupled symbols
	// (the leaf would find the same refutation after every completion
	// below). Slots verified here are remembered until their choice is
	// undone. A refutation names the depths it depends on.
	pendingRefuted := func() (conflict map[int]bool, newly []string) {
		for _, s := range slots {
			c, isChosen := chosen[s.key]
			if !isChosen || verified[s.key] {
				continue
			}
			premise, next, asmNext, isResolved := preservation(s, c)
			if !isResolved {
				continue
			}
			if refutedByCoupling(premise, next, asmNext, widthOfName) {
				if trace {
					fmt.Fprintf(os.Stderr, "verify %s: a valuation refutes one iteration preserving %s\n  premise %s\n  oak-next %s\n  asm-next %s\n", fn.Name, c.show(), premise.String(), next.String(), asmNext.String())
				}
				conflict = conflictOf(asmLoops[s.event].next[c.reg])
				conflict[depthOf[asmLoops[s.event].freshName(c.reg)]] = true
				return conflict, newly
			}
			verified[s.key] = true
			newly = append(newly, s.key)
		}
		for k := range oakLoops {
			asmCond := substitute(asmLoops[k].cond, sigma)
			if resolved(asmCond) && refutedByCoupling(bodyPremise(k, sigma, false), substitute(oakLoops[k].cond, sigma), asmCond, widthOfName) {
				if trace {
					fmt.Fprintf(os.Stderr, "verify %s: a valuation refutes loop %d's continue conditions agreeing\n  premise %s\n  oak-cond %s\n  asm-cond %s\n  sigma %v\n", fn.Name, k+1, bodyPremise(k, sigma, false).String(), substitute(oakLoops[k].cond, sigma).String(), asmCond.String(), sigmaShow(sigma))
				}
				return conflictOf(asmLoops[k].cond), newly
			}
		}
		return nil, newly
	}
	// Viability first: a slot none of whose candidates survives its own
	// obligation — no symbol of its width in the event, or every pairing
	// refuted by a valuation on its own (the register's one-iteration value
	// mentioning no other loop symbol) — fails the coupling before any
	// search, since no choice elsewhere could rescue it.
	for _, s := range slots {
		viable := false
		var last string
		candidates, _ := candidatesFor(s)
		if trace {
			shows := make([]string, 0, len(candidates))
			for _, c := range candidates {
				shows = append(shows, c.show())
			}
			fmt.Fprintf(os.Stderr, "verify %s: slot %s of loop %d (asm vars %v): candidates %v\n", fn.Name, s.name, s.event+1, asmLoops[s.event].vars, shows)
		}
		for _, c := range candidates {
			asmName := asmLoops[s.event].freshName(c.reg)
			sigma[asmName] = widen(s.pack(oakLoops[s.event].fresh), c.ext, asmLoops[s.event].width[c.reg])
			if c.a == 1 {
				sigma[asmName] = binaryTerm("add", sigma[asmName], c.b)
			} else {
				sigma[asmName] = binaryTerm("sub", c.b, sigma[asmName])
			}
			premise, next, asmNext, isResolved := preservation(s, c)
			delete(sigma, asmName)
			if !isResolved || !refutedByCoupling(premise, next, asmNext, widthOfName) {
				viable = true
				break
			}
			last = c.show()
		}
		if !viable {
			if last == "" {
				return evidence(fmt.Sprintf("no register is an affine image of the loop variable %s of loop %d at its header", s.name, s.event+1))
			}
			return evidence(fmt.Sprintf("one iteration of loop %d was not proven to preserve %s (a valuation refutes it, as every other pairing of %s)", s.event+1, last, s.name))
		}
	}
	visited := 0
	// The search is conflict-directed: a failure below returns the depths
	// its refutation depended on, and a level whose choice is not among
	// them passes the failure up without trying its other candidates (the
	// sixteen slots of a byte array between an accumulator and the register
	// it was wrongly paired with are never re-enumerated).
	var search func(i int) (bool, map[int]bool)
	search = func(i int) (bool, map[int]bool) {
		visited++
		if visited > searchBudget {
			failure = "the coupling search exceeded its budget"
			return false, nil
		}
		if i == len(slots) {
			for k := range oakLoops {
				oakEv, asmEv := oakLoops[k], asmLoops[k]
				if equal, decided := implies(bodyPremise(k, sigma, false), substitute(oakEv.cond, sigma), substitute(asmEv.cond, sigma)); !decided || !equal {
					failure = fmt.Sprintf("loop %d's continue conditions were not proven equal", k+1)
					if trace {
						fmt.Fprintf(os.Stderr, "verify %s: %s (decided=%v)\n  oak: %s\n  asm: %s\n  premise: %s\n", fn.Name, failure, decided, substitute(oakEv.cond, sigma), substitute(asmEv.cond, sigma), bodyPremise(k, sigma, false))
					}
					if !decided {
						// Beyond the node budget under this pairing; another
						// pairing may decide (the proof's own budget,
						// nodeBudget, bounds the search).
						failure += " (the bit-level decision exceeded its node budget)"
					}
					return false, conflictOf(asmEv.cond)
				}
				premise := bodyPremise(k, sigma, true)
				for _, s := range slots {
					if s.event != k {
						continue
					}
					c := chosen[s.key]
					// r' = a*x' + b must hold after one iteration.
					next := substitute(s.pack(oakEv.next), sigma)
					next = widen(next, c.ext, asmEv.width[c.reg])
					if c.a == 1 {
						next = binaryTerm("add", next, c.b)
					} else {
						next = binaryTerm("sub", c.b, next)
					}
					if equal, decided := implies(premise, next, substitute(asmEv.next[c.reg], sigma)); !decided || !equal {
						failure = fmt.Sprintf("one iteration of loop %d was not proven to preserve %s", k+1, c.show())
						if trace {
							fmt.Fprintf(os.Stderr, "verify %s: %s (decided=%v)\n  oak next: %s\n  asm next: %s\n", fn.Name, failure, decided, next, substitute(asmEv.next[c.reg], sigma))
						}
						if !decided {
							failure += " (the bit-level decision exceeded its node budget)"
						}
						conflict := conflictOf(asmEv.next[c.reg])
						conflict[depthOf[asmEv.freshName(c.reg)]] = true
						return false, conflict
					}
				}
			}
			return true, nil
		}
		s := slots[i]
		total := map[int]bool{}
		candidates, taken := candidatesFor(s)
		// The symbols other slots hold would have been candidates here:
		// their depths are part of any failure of this slot.
		for _, name := range taken {
			total[depthOf[name]] = true
		}
		for _, c := range candidates {
			asmName := asmLoops[s.event].freshName(c.reg)
			if trace {
				fmt.Fprintf(os.Stderr, "verify %s: search depth %d: %s\n", fn.Name, i, c.show())
			}
			used[asmName] = true
			chosen[s.key] = c
			depthOf[asmName] = i
			// r = a*x + b: the register's fresh symbol expressed for x (the
			// pack of the lanes' symbols for a group).
			x := widen(s.pack(oakLoops[s.event].fresh), c.ext, asmLoops[s.event].width[c.reg])
			if c.a == 1 {
				sigma[asmName] = binaryTerm("add", x, c.b)
			} else {
				sigma[asmName] = binaryTerm("sub", c.b, x)
			}
			conflict, newly := pendingRefuted()
			if conflict == nil {
				var ok bool
				if ok, conflict = search(i + 1); ok {
					return true, nil
				}
			}
			for _, key := range newly {
				delete(verified, key)
			}
			delete(used, asmName)
			delete(chosen, s.key)
			delete(sigma, asmName)
			delete(depthOf, asmName)
			if visited > searchBudget {
				return false, nil
			}
			if !conflict[i] {
				// This level's choice played no part: no other candidate here
				// can change the outcome, so the conflict passes up.
				return false, conflict
			}
			for depth := range conflict {
				if depth != i {
					total[depth] = true
				}
			}
		}
		if failure == "" {
			failure = fmt.Sprintf("no register is an affine image of the loop variable %s of loop %d at its header", s.name, s.event+1)
		}
		if budget.remaining <= 0 {
			failure = "the loop proof's diagram budget ran out in the coupling search"
		}
		return false, total
	}
	if ok, _ := search(0); !ok {
		return evidence(failure)
	}
	var pairs []string
	for _, s := range slots {
		pairs = append(pairs, chosen[s.key].show())
	}
	// The iterations' stores: each event's two sides store through the
	// same spans, the same number of times, at indices and values proven
	// equal under the coupling and the body's premise, under equal guards;
	// an inner loop's marker matches its counterpart by name.
	for k, oakEv := range oakLoops {
		asmEv := asmLoops[k]
		// The induction's base: the memories at the loop's entry agree —
		// each span's stores before the loop over its entry memory, at a
		// fresh index, the asm side under the coupling; under the parent
		// loop's body premise when nested.
		entryPremise := constTerm(1, 1)
		if oakEv.parent > 0 {
			entryPremise = bodyPremise(oakEv.parent-1, sigma, true)
		}
		if reached := asmEv.reached; reached != nil {
			// The machine reached the loop on this path's condition, and
			// its stores before the loop are unguarded there; the Oak
			// side's carry the arm's condition as their guard (`ok ? {
			// s[dom].free_count = …; while … }`), so the entry memories
			// agree only under it.
			entryPremise = binaryTerm("and", entryPremise, truncate(substitute(reached, sigma), 1))
		}
		if reason, ok := coupledEntryMemories(k, oakEv, asmEv, sigma, entryPremise, lowering, implies, splitsFor(earlierSiblings(k, oakLoops), oakLoops, asmLoops, sigma)); !ok {
			return evidence(reason)
		}
		if reason, ok := coupledWrites(k, oakEv, asmEv, sigma, bodyPremise(k, sigma, true), lowering, implies); !ok {
			// The stores did not pair one for one; the memories they leave
			// may still be one memory (stores in another order, a guarded
			// store against a split path): the iteration's memories are
			// compared whole at a fresh index.
			if memReason, memOk := coupledIterationMemories(k, oakEv, asmEv, sigma, bodyPremise(k, sigma, true), lowering, implies, splitsFor(children[k], oakLoops, asmLoops, sigma)); !memOk {
				return evidence(reason + "; " + memReason)
			}
		}
	}
	// The exit comparison, under every top-level loop's exit premise. A
	// result reading a loop-carried register no Oak variable is coupled to
	// is beyond the method. Symbolic disagreement here is never reported as
	// a mismatch — the states may be unreachable — only the concrete layer
	// refutes.
	mentioned := map[string]bool{}
	collectParams(asmTerm, mentioned)
	for name := range mentioned {
		var k int
		var reg string
		if n, _ := fmt.Sscanf(name, "loop%d.%s", &k, &reg); n == 2 && sigma[name] == nil && !strings.Contains(reg, "[") {
			// The asm result mentions only asm symbols: a register, a vector
			// register half or a frame slot of a loop. An element of a
			// loop's unknown memory (`loop1.v[0]`) is spelled the same on
			// both sides and needs no coupling.
			return evidence(fmt.Sprintf("the result reads loop-carried %s of loop %d, which no Oak variable is coupled to", reg, k))
		}
	}
	premise := constTerm(1, 1)
	var topLevel []int
	for k, ev := range oakLoops {
		if ev.parent == 0 {
			premise = binaryTerm("and", premise, exitPremise(k, sigma))
			topLevel = append(topLevel, k)
		}
	}
	// A result reading a loop's symbols after a path that skipped the loop
	// reads their header values on the machine side: the symbols the two
	// results mention are pinned where their loop never ran.
	if asmTerm != nil {
		resultMentions := map[string]bool{}
		collectParams(oakTerm, resultMentions)
		collectParams(substitute(truncate(asmTerm, width), sigma), resultMentions)
		for _, k := range topLevel {
			if pins := notRunPins(k, sigma, resultMentions); pins != nil {
				premise = binaryTerm("and", premise, pins)
			}
		}
	}
	// The loops whose markers the memories after the loops may carry
	// conditionally on the machine side (spanEqualSplitting).
	topSplits := splitsFor(topLevel, oakLoops, asmLoops, sigma)
	if asmTerm != nil {
		equal, decided := implies(premise, oakTerm, substitute(truncate(asmTerm, width), sigma))
		if !decided || !equal {
			if trace {
				fmt.Fprintf(os.Stderr, "verify %s: results not proven equal (decided=%v)\n  oak: %s\n  asm: %s\n  premise: %s\n", fn.Name, decided, oakTerm, substitute(truncate(asmTerm, width), sigma), premise)
			}
			return evidence("the results after the loops were not proven equal")
		}
	}
	// The package cells after the loops, under the coupling and the exit
	// premise, as decideEffects compares them in a body without loops: a
	// cell written before or after a loop (`st = u8(0)` around the
	// table-zeroing loop of the OS pilot's reset) meets its entry value or
	// the other side's write; a cell the body writes inside a loop the
	// coupling has not modeled leaves the comparison undecided — evidence.
	oakCells := lowering.writtenCells()
	cellSet := map[string]bool{}
	for name := range exec.cells {
		cellSet[name] = true
	}
	for name := range oakCells {
		cellSet[name] = true
	}
	writtenCells := make([]string, 0, len(cellSet))
	for name := range cellSet {
		writtenCells = append(writtenCells, name)
	}
	sort.Strings(writtenCells)
	for _, name := range writtenCells {
		global, declared := exec.globals[name]
		if !declared {
			return trusted(fmt.Sprintf("a store through undeclared package global %s", name))
		}
		cellBits := cellWidth(global)
		asmCell, asmWritten := exec.cells[name]
		if !asmWritten {
			asmCell = cellEntry(name, global)
		}
		oakCell, oakWritten := oakCells[name]
		if !oakWritten {
			oakCell = cellEntry(name, global)
		}
		asmCell = substitute(truncate(asmCell, cellBits), sigma)
		oakCell = truncate(oakCell, cellBits)
		if equal, decided := implies(premise, oakCell, asmCell); !decided || !equal {
			if trace {
				fmt.Fprintf(os.Stderr, "verify %s: cell %s after the loops (decided=%v)\n  oak: %s\n  asm: %s\n", fn.Name, name, decided, oakCell, asmCell)
			}
			return evidence(fmt.Sprintf("the package global %s after the loops was not proven equal", name))
		}
	}
	// The span memories after the loops: the final element at a fresh
	// index over the entry memory, as decideSpans compares them, here under
	// the coupling and the exit premise.
	spanNames := map[string]bool{}
	for name := range exec.writes {
		spanNames[name] = true
	}
	for name := range lowering.writes {
		spanNames[name] = true
	}
	writtenSpans := make([]string, 0, len(spanNames))
	for name := range spanNames {
		writtenSpans = append(writtenSpans, name)
	}
	sort.Strings(writtenSpans)
	for _, name := range writtenSpans {
		elemWidth, isSpan := lowering.spanMemoryWidth(name)
		if !isSpan {
			return trusted(fmt.Sprintf("a store through %s, which the Oak signature does not declare as a span", name))
		}
		lowering.fresh[spanIndexName(name)] = 32
		at := paramTerm(spanIndexName(name), 32)
		entry := selectTerm(name, at, elemWidth)
		asmMemory := substitute(memoryAt(exec.writes[name], at, entry), sigma)
		oakMemory := memoryAt(lowering.writes[name], at, entry)
		if equal, decided := spanEqualSplitting(premise, name, elemWidth, oakMemory, asmMemory, topSplits, implies); !decided || !equal {
			if trace {
				fmt.Fprintf(os.Stderr, "verify %s: span %s after the loops (decided=%v)\n  oak: %s\n  asm: %s\n  premise: %s\n", fn.Name, name, decided, oakMemory, asmMemory, premise)
			}
			return evidence(fmt.Sprintf("the memory of the span %s after the loops was not proven equal", name))
		}
	}
	// One note for both kinds of memory, cells before spans: it was built
	// twice and interpolated twice, so every proven loop verdict said
	// "and the package state it writes" two times over.
	memoryNote := ""
	if len(writtenCells) > 0 {
		memoryNote += " and the package state it writes (" + strings.Join(writtenCells, ", ") + ")"
	}
	if len(writtenSpans) > 0 {
		memoryNote += " and the span memory it writes (" + strings.Join(writtenSpans, ", ") + ")"
	}
	var notes []string
	for k, inv := range invariants {
		if inv.kind != termConst {
			notes = append(notes, fmt.Sprintf("loop %d under the invariant %s", k+1, inv))
		}
	}
	invariantNote := ""
	if len(notes) > 0 {
		invariantNote = " (" + strings.Join(notes, "; ") + ")"
	}
	loopsNote := "data-dependent loop coupled inductively"
	if len(oakLoops) > 1 {
		shape := "data-dependent loops"
		for _, ev := range oakLoops {
			if ev.parent != 0 {
				shape = "nested data-dependent loops"
				break
			}
		}
		loopsNote = fmt.Sprintf("%d %s coupled inductively", len(oakLoops), shape)
	}
	witnessNote := fmt.Sprintf(", %d concrete inputs agree", checked)
	if asmTerm == nil {
		witnessNote = ""
	}
	return Verdict{Kind: VerdictProven, Message: fmt.Sprintf("asm unit %s: proven equal to its Oak body at the bit level — %s (%s)%s%s%s", fn.Name, loopsNote, strings.Join(pairs, ", "), invariantNote, memoryNote, witnessNote)}
}

// coupledWrites checks that one iteration of loop k stores alike on both
// sides: through the same spans, the same number of times, each store's
// index and value proven equal under the coupling and the body premise
// and its guard likewise (a missing guard is "always"); a marker of an
// inner loop's memory matches its counterpart by name.
func coupledWrites(k int, oakEv, asmEv *loopEvent, sigma map[string]*term, premise *term, lowering *oakLowering, implies func(premise, a, b *term) (bool, bool)) (string, bool) {
	spans := map[string]bool{}
	for span := range oakEv.writes {
		spans[span] = true
	}
	for span := range asmEv.writes {
		spans[span] = true
	}
	names := make([]string, 0, len(spans))
	for span := range spans {
		names = append(names, span)
	}
	sort.Strings(names)
	always := constTerm(1, 1)
	for _, span := range names {
		oakWrites, asmWrites := oakEv.writes[span], asmEv.writes[span]
		if len(oakWrites) != len(asmWrites) {
			return fmt.Sprintf("one iteration of loop %d stores through %s %d times on the Oak side and %d on the asm side", k+1, span, len(oakWrites), len(asmWrites)), false
		}
		elemWidth, isSpan := lowering.spanMemoryWidth(span)
		if !isSpan {
			return fmt.Sprintf("loop %d stores through %s, which the signature does not declare as a span", k+1, span), false
		}
		for i := range oakWrites {
			o, a := oakWrites[i], asmWrites[i]
			if o.memory != "" || a.memory != "" {
				if o.memory != a.memory {
					return fmt.Sprintf("store %d of loop %d through %s: an inner loop's memory on one side only", i+1, k+1, span), false
				}
			} else {
				if equal, decided := implies(premise, truncate(o.index, 32), substitute(truncate(a.index, 32), sigma)); !decided || !equal {
					return fmt.Sprintf("store %d of loop %d through %s: the indices were not proven equal", i+1, k+1, span), false
				}
				if equal, decided := implies(premise, truncate(o.value, elemWidth), substitute(truncate(a.value, elemWidth), sigma)); !decided || !equal {
					return fmt.Sprintf("store %d of loop %d through %s: the values were not proven equal", i+1, k+1, span), false
				}
			}
			og, ag := o.guard, a.guard
			if og == nil {
				og = always
			}
			if ag == nil {
				ag = always
			}
			if equal, decided := implies(premise, truncate(og, 1), substitute(truncate(ag, 1), sigma)); !decided || !equal {
				return fmt.Sprintf("store %d of loop %d through %s: the conditions were not proven equal", i+1, k+1, span), false
			}
		}
	}
	return "", true
}

// coupledEntryMemories requires the two sides' memories at loop k's
// entry equal, span by span: the stores before the loop over the span's
// entry memory, at a fresh index, the asm side under the coupling. This
// is the induction's base; the iteration's stores are its step.
func coupledEntryMemories(k int, oakEv, asmEv *loopEvent, sigma map[string]*term, premise *term, lowering *oakLowering, implies func(premise, a, b *term) (bool, bool), splits []loopSplit) (string, bool) {
	spans := map[string]bool{}
	for span := range oakEv.entry {
		spans[span] = true
	}
	for span := range asmEv.entry {
		spans[span] = true
	}
	names := make([]string, 0, len(spans))
	for span := range spans {
		names = append(names, span)
	}
	sort.Strings(names)
	for _, span := range names {
		oakLog, oakHas := oakEv.entry[span]
		asmLog, asmHas := asmEv.entry[span]
		if !oakHas || !asmHas {
			return fmt.Sprintf("loop %d marks the memory of %s on one side only", k+1, span), false
		}
		if len(oakLog) == 0 && len(asmLog) == 0 {
			continue // both the entry memory itself
		}
		elemWidth, isSpan := lowering.spanMemoryWidth(span)
		if !isSpan {
			return fmt.Sprintf("loop %d marks %s, which the signature does not declare as a span", k+1, span), false
		}
		lowering.fresh[spanIndexName(span)] = 32
		at := paramTerm(spanIndexName(span), 32)
		entry := selectTerm(span, at, elemWidth)
		oakMemory := memoryAt(oakLog, at, entry)
		asmMemory := substitute(memoryAt(asmLog, at, entry), sigma)
		if equal, decided := spanEqualSplitting(premise, span, elemWidth, oakMemory, asmMemory, splits, implies); !decided || !equal {
			reason := fmt.Sprintf("the memory of %s at loop %d's entry was not proven equal", span, k+1)
			if !decided {
				reason += " (the bit-level decision exceeded its node budget)"
			}
			return reason, false
		}
	}
	return "", true
}

// coupledIterationMemories compares the memories one iteration of loop k
// leaves, span by span, as memories rather than store by store: the
// iteration's stores over the loop's unknown memory, at a fresh index,
// the asm side under the coupling and the body premise.
func coupledIterationMemories(k int, oakEv, asmEv *loopEvent, sigma map[string]*term, premise *term, lowering *oakLowering, implies func(premise, a, b *term) (bool, bool), splits []loopSplit) (string, bool) {
	spans := map[string]bool{}
	for span := range oakEv.writes {
		spans[span] = true
	}
	for span := range asmEv.writes {
		spans[span] = true
	}
	names := make([]string, 0, len(spans))
	for span := range spans {
		names = append(names, span)
	}
	sort.Strings(names)
	for _, span := range names {
		elemWidth, isSpan := lowering.spanMemoryWidth(span)
		if !isSpan {
			return fmt.Sprintf("loop %d stores through %s, which the signature does not declare as a span", k+1, span), false
		}
		lowering.fresh[spanIndexName(span)] = 32
		at := paramTerm(spanIndexName(span), 32)
		unknown := selectTerm(loopMemoryName(oakEv.index, span), at, elemWidth)
		oakMemory := memoryAt(oakEv.writes[span], at, unknown)
		asmMemory := substitute(memoryAt(asmEv.writes[span], at, unknown), sigma)
		if equal, decided := spanEqualSplitting(premise, span, elemWidth, oakMemory, asmMemory, splits, implies); !decided || !equal {
			reason := fmt.Sprintf("one iteration of loop %d was not proven to leave the memory of %s equal", k+1, span)
			if !decided {
				reason += " (the bit-level decision exceeded its node budget)"
			}
			return reason, false
		}
	}
	return "", true
}

// concreteMemoriesDiffer compares two write logs of a concrete run as
// memories: at every index either side stored (a constant on a concrete
// input), the values left must agree; elsewhere both hold the fixed
// memory. Reports the first difference.
func concreteMemoriesDiffer(asmLogs, oakLogs map[string][]*spanWrite, lowering *oakLowering, env map[string]uint64) (span string, index uint64, got, want uint64, differ bool) {
	spans := map[string]bool{}
	for name := range asmLogs {
		spans[name] = true
	}
	for name := range oakLogs {
		spans[name] = true
	}
	names := make([]string, 0, len(spans))
	for name := range spans {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		elemWidth, isSpan := lowering.spanMemoryWidth(name)
		if !isSpan {
			continue
		}
		indices := map[uint64]bool{}
		for _, log := range [][]*spanWrite{asmLogs[name], oakLogs[name]} {
			for _, w := range log {
				if w.memory != "" || w.index.kind != termConst {
					return "", 0, 0, 0, false // not a concrete run's log
				}
				indices[w.index.value&mask(32)] = true
			}
		}
		sorted := make([]uint64, 0, len(indices))
		for k := range indices {
			sorted = append(sorted, k)
		}
		sort.Slice(sorted, func(i, j int) bool { return sorted[i] < sorted[j] })
		for _, k := range sorted {
			at := constTerm(k, 32)
			entry := constTerm(elementValue(name, k, elemWidth), elemWidth)
			a := memoryAt(asmLogs[name], at, entry).eval(env)
			o := memoryAt(oakLogs[name], at, entry).eval(env)
			if a != o {
				return name, k, a, o, true
			}
		}
	}
	return "", 0, 0, 0, false
}

// concreteCellsDiffer is the concrete witness counterpart of the final cell
// proof: every package cell either has its path's final write or its entry
// value, and both are evaluated on the witness environment.
func concreteCellsDiffer(exec *pathExecutor, lowering *oakLowering, env map[string]uint64) (cell string, got, want uint64, differ bool) {
	oakCells := lowering.writtenCells()
	names := map[string]bool{}
	for name := range exec.cells {
		names[name] = true
	}
	for name := range oakCells {
		names[name] = true
	}
	sorted := make([]string, 0, len(names))
	for name := range names {
		sorted = append(sorted, name)
	}
	sort.Strings(sorted)
	for _, name := range sorted {
		global, declared := exec.globals[name]
		if !declared {
			return name, 0, 0, true
		}
		asmCell, asmWritten := exec.cells[name]
		if !asmWritten {
			asmCell = cellEntry(name, global)
		}
		oakCell, oakWritten := oakCells[name]
		if !oakWritten {
			oakCell = cellEntry(name, global)
		}
		a, o := asmCell.eval(env), oakCell.eval(env)
		if a != o {
			return name, a, o, true
		}
	}
	return "", 0, 0, false
}

// substitute replaces parameters by terms (the asm loop symbols by their
// expression in the Oak variables' symbols).
func substitute(t *term, sigma map[string]*term) *term {
	return substituteMemo(t, sigma, map[*term]*term{})
}

func restoreLoopEntryMemories(t *term, ev *loopEvent, memo map[*term]*term, valid *bool) *term {
	if t == nil {
		return nil
	}
	if done, seen := memo[t]; seen {
		return done
	}
	if t.kind == termSelect {
		at := restoreLoopEntryMemories(t.left, ev, memo, valid)
		prefix := fmt.Sprintf("loop%d.", ev.index)
		if strings.HasPrefix(t.name, prefix) {
			span := strings.TrimPrefix(t.name, prefix)
			if entry, marked := ev.entry[span]; marked {
				restored := memoryAt(entry, at, selectTerm(span, at, t.width))
				memo[t] = restored
				return restored
			}
			*valid = false
		}
	}
	if t.kind == termParam {
		// A select at a constant index is represented as a parameter:
		// loop1[3].tables.count.  Match it against the event's exact
		// memory names and rebuild the corresponding entry-memory read.
		var restored *term
		for span, entry := range ev.entry {
			memory := loopMemoryName(ev.index, span)
			dot := strings.IndexByte(memory, '.')
			if dot < 0 {
				continue
			}
			prefix, suffix := memory[:dot]+"[", memory[dot:]
			if !strings.HasPrefix(t.name, prefix) {
				continue
			}
			close := strings.IndexByte(t.name[len(prefix):], ']')
			if close < 0 {
				continue
			}
			close += len(prefix)
			if t.name[close+1:] != suffix {
				continue
			}
			index, err := strconv.ParseUint(t.name[len(prefix):close], 10, 32)
			if err != nil || restored != nil {
				*valid = false
				return t
			}
			at := constTerm(index, 32)
			restored = memoryAt(entry, at, selectTerm(span, at, t.width))
		}
		if restored != nil {
			memo[t] = restored
			return restored
		}
		if strings.HasPrefix(t.name, fmt.Sprintf("loop%d.", ev.index)) || strings.HasPrefix(t.name, fmt.Sprintf("loop%d[", ev.index)) {
			*valid = false
		}
		return t
	}
	out := *t
	out.kbDone = false
	out.cond = restoreLoopEntryMemories(t.cond, ev, memo, valid)
	out.left = restoreLoopEntryMemories(t.left, ev, memo, valid)
	out.right = restoreLoopEntryMemories(t.right, ev, memo, valid)
	memo[t] = &out
	return &out
}

func substituteMemo(t *term, sigma map[string]*term, memo map[*term]*term) *term {
	if t == nil {
		return nil
	}
	if done, seen := memo[t]; seen {
		return done // shared subterms are substituted once
	}
	switch t.kind {
	case termConst:
		return t
	case termParam:
		if to, bound := sigma[t.name]; bound {
			return adaptWidth(to, t.width)
		}
		return t
	}
	if t.kind == termFloat {
		// An operation is rebuilt through its constructor: known operands
		// after the substitution fold as they would have at construction.
		args := []*term{substituteMemo(t.left, sigma, memo)}
		if t.right != nil {
			args = append(args, substituteMemo(t.right, sigma, memo))
		}
		if t.cond != nil {
			args = append(args, substituteMemo(t.cond, sigma, memo))
		}
		rebuilt := floatTerm(t.op, t.width, args...)
		memo[t] = rebuilt
		return rebuilt
	}
	out := *t
	out.kbDone = false
	out.cond = substituteMemo(t.cond, sigma, memo)
	out.left = substituteMemo(t.left, sigma, memo)
	out.right = substituteMemo(t.right, sigma, memo)
	if lane, isExtraction := extractedLane(&out); isExtraction {
		// A lane read out of a register the substitution made a pack of
		// the Oak lanes is that Oak lane (extractedLane).
		memo[t] = lane
		return lane
	}
	memo[t] = &out
	return &out
}

// loopTermNodeBudget bounds the distinct nodes of the loop events' terms
// (headers, conditions, next values, stores) the coupling search works
// over.
const loopTermNodeBudget = 250000

// loopTermNodes counts the distinct term nodes of every event's terms on
// both sides.
func loopTermNodes(asmLoops, oakLoops []*loopEvent) int {
	visited := map[*term]bool{}
	var count func(t *term)
	count = func(t *term) {
		if t == nil || visited[t] {
			return
		}
		visited[t] = true
		count(t.left)
		count(t.right)
		count(t.cond)
	}
	for _, side := range [][]*loopEvent{asmLoops, oakLoops} {
		for _, ev := range side {
			count(ev.cond)
			for _, name := range ev.vars {
				count(ev.header[name])
				count(ev.next[name])
			}
			for _, writes := range ev.writes {
				for _, w := range writes {
					count(w.index)
					count(w.value)
					count(w.guard)
				}
			}
		}
	}
	return len(visited)
}

// nodeBudget is the diagram nodes one loop proof may spend across all of
// its implications (loopProofNodeBudget): a coupling search that keeps
// failing candidates near the per-decision budget ends as evidence rather
// than running for minutes. It also carries the proof's decisions so far
// (decided), by the terms' identity: the sides are DAGs whose tree
// unfolding may be exponential, and the congruence rule descends them by
// operand pairs, so a shared pair is met once per parent and decided
// once. An undecided result stays: the decision is deterministic and the
// budget only shrinks.
type nodeBudget struct {
	remaining int // diagram nodes the proof may still spend
	calls     int // implications tried so far (implicationCallLimit)
	decided   map[decisionKey]decisionResult
}

// decisionKey identifies one implication within a proof: its premise and
// sides by identity, at its case-split depth (the depth bounds the splits
// a decision may still make).
type decisionKey struct {
	premise, a, b *term
	depth         int
}

type decisionResult struct{ holds, decided bool }

// loopProofNodeBudget bounds one loop proof's diagram nodes in all;
// loopDecisionNodeBudget bounds each of its implications. Three failed
// diagrams end the proof: a coupling that fails three implications at
// the per-decision budget is not about to succeed, and each such failure
// is four orders of two million nodes raced — a minute or more — so the
// eight of before let a body with sixty-four-way selects (`count_leading_
// zeros`) spend seven minutes a candidate deciding nothing. Each of a
// loop proof's implications gets a quarter of the straight-line
// decision's nodes: the implications that hold do so in tens of
// thousands, and a failing one at two million nodes cost half a minute
// per order under load (`protocol_line_done`, seven minutes a candidate).
const (
	loopDecisionNodeBudget = blastNodeBudget / 4
	loopProofNodeBudget    = 3 * loopDecisionNodeBudget
)

// impliesEqual decides premise → (a = b) at the terms' common width:
// valuations first (one satisfying the premise under which the sides
// differ refutes it — elements read the fixed memory, as the witness layer
// does), then bit-blasting under the variable orders of equalityBlasters
// raced as decideEqual races them; decided is false when every order
// exceeds the node budget.
func impliesEqual(premise, a, b *term, widthOf func(string) int) (holds bool, decided bool) {
	return impliesEqualWithin(premise, a, b, widthOf, nil)
}

// impliesEqualWithin is impliesEqual spending from a shared budget when
// one is given: a decision that would exceed what remains is undecided.
func impliesEqualWithin(premise, a, b *term, widthOf func(string) int, budget *nodeBudget) (holds bool, decided bool) {
	return impliesEqualDepth(premise, a, b, widthOf, budget, 0)
}

// impliesEqualDepth is impliesEqualWithin at a case-split depth: when every
// variable order exceeds its budget, the decision splits on the condition
// of the largest branch in the terms and decides both cases under it
// (splitDecide), up to splitDepth deep. Each decision is made once per
// proof (nodeBudget.decided).
func impliesEqualDepth(premise, a, b *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	if budget == nil {
		// A decision that arrives without a budget (decideEqual on a
		// chunk's terms) still ends: the case splits and the congruence
		// rule recurse over the operands of both sides, each pair pruned
		// and blasted anew, and over a hash block's term that walk ran
		// for hours (docs/spec/94-assembler.md §9 "Loop invariants", the
		// implication budget). One decision's allowance bounds it; past
		// the allowance the implication is undecided, not unending.
		budget = &nodeBudget{remaining: loopDecisionNodeBudget}
	}
	key := decisionKey{premise, a, b, depth}
	if r, seen := budget.decided[key]; seen {
		return r.holds, r.decided // met before, under another parent
	}
	// Each implication costs a call from the proof's allowance, and
	// terms too large to blast cost a failed diagram's nodes, before
	// they are canonicalized, pruned, or substituted: those walks are
	// linear, and a body whose write coupling tries thousands of
	// implications over a memory's selects (`add_bits`) would spend
	// hours in them alone.
	budget.calls++
	if budget.calls > implicationCallLimit {
		return false, false
	}
	if dagNodesExceed(implicationNodeLimit, premise, a, b) {
		budget.remaining -= blastNodeBudget
		return false, false
	}
	holds, decided = impliesEqualDepthUncached(premise, a, b, widthOf, budget, depth)
	if budget.decided == nil {
		budget.decided = map[decisionKey]decisionResult{}
	}
	budget.decided[key] = decisionResult{holds, decided}
	return holds, decided
}

func impliesEqualDepthUncached(premise, a, b *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	if depth == 0 {
		premise, a, b = canonical(premise), canonical(a), canonical(b)
	}
	width := a.width
	if b.width > width {
		width = b.width
	}
	a, b = adaptWidth(a, width), adaptWidth(b, width)
	branching := hasLargeBranch(a) || hasLargeBranch(b)
	if premise.kind != termConst && branching {
		// The premise settles branches on both sides (a loop guard, a case
		// split's condition): with those pruned the sides may be one term.
		pruned := pruneUnder(premise, []*term{a, b}, widthOf)
		// Pruning rebuilds the branches it settles; the rebuilt terms
		// take the canonical spelling again, or the rules the sides met
		// under (a negation, a cset) are lost to the arm rule below.
		a, b = canonical(pruned[0]), canonical(pruned[1])
		if os.Getenv("OAK_VERIFY_TRACE") != "" {
			fmt.Fprintf(os.Stderr, "verify: pruned under the premise: a %d nodes, b %d nodes, same=%v\n", termSize(a, map[*term]int{}), termSize(b, map[*term]int{}), equalTerms(a, b))
		}
	}
	if equalTerms(a, b) {
		return true, true // the same term on both sides: no diagram needed
	}
	if equalReductions(a, b) {
		return true, true // the same lane tests, reduced and negated alike
	}
	if budget != nil && budget.remaining <= 0 {
		return false, false
	}
	mentioned := map[string]bool{}
	collectParams(premise, mentioned)
	collectParams(a, mentioned)
	collectParams(b, mentioned)
	names := make([]string, 0, len(mentioned))
	widths := map[string]int{}
	for name := range mentioned {
		names = append(names, name)
		widths[name] = widthOf(name)
	}
	sort.Strings(names)
	narrowByPremise(premise, widths)
	if refutedByValuation(premise, a, b, names, widths) {
		return false, true
	}
	if premise.kind != termConst && termSize(a, map[*term]int{})+termSize(b, map[*term]int{}) <= smallSides {
		// Small sides may agree without any premise (`g < n` against
		// `¬(g ≥ n)`, a loop's continue conditions): decided on their own
		// diagram first, where the premise — a conjunction of the inner
		// loops' exit facts over their element reads — costs every order
		// its budget for nothing.
		if holds, decided := impliesEqualDepth(constTerm(1, 1), a, b, widthOf, budget, depth); decided && holds {
			return true, true
		}
	}
	if relevant, dropped := relevantPremise(premise, a, b); dropped {
		// The premise's conjuncts that share no symbol with the sides,
		// even through other conjuncts (an inner loop's exit facts over
		// its own symbols, a callee's summary), weigh on every diagram
		// and decide nothing: the implication is tried first under the
		// conjuncts that can bear on it — a weaker premise, so a proof
		// under it is a proof — and under the whole only when that fails.
		if holds, decided := impliesEqualDepth(relevant, a, b, widthOf, budget, depth); decided && holds {
			return true, true
		}
	}
	if holds, decided := impliesEqualByArms(premise, a, b, widthOf, budget, depth); decided {
		return holds, true
	}
	if holds, decided := impliesEqualCongruent(premise, a, b, widthOf, budget, depth); decided {
		return holds, true
	}
	blasters := equalityBlasters(names, widths, a, b)
	var stop atomic.Bool
	type attempt struct{ holds, decided bool }
	results := make(chan attempt, len(blasters))
	for _, bl := range blasters {
		bl.bdd.stop = &stop
		if budget != nil {
			// One implication spends no more than the proof has left: the
			// shared budget bounds the diagrams as they grow, not only the
			// number of implications tried — and no more than a loop
			// proof's per-implication cap (loopDecisionNodeBudget).
			if bl.bdd.budget > loopDecisionNodeBudget {
				bl.bdd.budget = loopDecisionNodeBudget
			}
			if budget.remaining < bl.bdd.budget {
				bl.bdd.budget = budget.remaining
			}
		}
		go func(bl *blaster) {
			holds, decided := impliesEqualUnder(bl, premise, a, b, width)
			results <- attempt{holds, decided}
		}(bl)
	}
	holds, decided = false, false
	for range blasters {
		// The first order to finish decides; the rest stop at their next
		// node, and every racer has returned before its diagram is read.
		if r := <-results; r.decided && !decided {
			holds, decided = r.holds, true
			stop.Store(true)
		}
	}
	if budget != nil {
		// The decision cost the proof its largest diagram: undecided ones
		// near the per-decision budget exhaust the proof's in a few tries.
		spent := 0
		for _, bl := range blasters {
			if n := len(bl.bdd.nodes); n > spent {
				spent = n
			}
		}
		budget.remaining -= spent
	}
	if decided {
		return holds, true
	}
	if os.Getenv("OAK_VERIFY_TRACE") != "" {
		remaining := -1
		if budget != nil {
			remaining = budget.remaining
		}
		fmt.Fprintf(os.Stderr, "verify: undecided implication at depth %d: a %d nodes (width %d), b %d nodes (width %d), premise %d nodes, %d names %v, branching=%v, budget remaining %d\n  premise: %s\n", depth, termSize(a, map[*term]int{}), a.width, termSize(b, map[*term]int{}), b.width, termSize(premise, map[*term]int{}), len(names), names, branching, remaining, premise)
		for _, bl := range blasters {
			fmt.Fprintf(os.Stderr, "  order %s: %d bdd nodes, exceeded=%v, budget %d\n", bl.label, len(bl.bdd.nodes), bl.bdd.exceeded, bl.bdd.budget)
		}
	}
	if !branching {
		return false, false // no branch worth a split: the diagrams were the decision
	}
	return splitDecide(premise, a, b, widthOf, budget, depth)
}

// hasLargeBranch reports an ite in the term, other than a table lookup's
// step, whose arms together exceed largeBranch nodes: the branches a case
// split or a pruning under a premise can shrink a decision by.
func hasLargeBranch(t *term) bool {
	sizes := map[*term]int{}
	visited := map[*term]bool{}
	var walk func(t *term) bool
	walk = func(t *term) bool {
		if t == nil || visited[t] {
			return false
		}
		visited[t] = true
		if t.kind == termIte && t.cond.kind != termConst && !isLookupStep(t.cond, sizes) && termSize(t.left, sizes)+termSize(t.right, sizes) >= largeBranch {
			return true
		}
		return walk(t.cond) || walk(t.left) || walk(t.right)
	}
	return walk(t)
}

// largeBranch is the arm size from which a branch is worth splitting on.
const largeBranch = 200

// splitDecide decides premise → (a = b) by a case split on the condition
// of the largest branch in a or b: both cases must hold, and either
// refuted refutes the whole (a counterexample under a stronger premise is
// one under the premise). Under each case the blaster prunes every ite
// the case settles, so a branch on a condition over many inputs — the
// UTF-8 kernel's "any high bit in the sixty-four bytes" — no longer
// multiplies its arms' diagrams. Undecided past splitDepth.
func splitDecide(premise, a, b *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	if depth >= splitDepth {
		return false, false
	}
	cond := splitCondition(a, b)
	if cond == nil {
		return false, false
	}
	if os.Getenv("OAK_VERIFY_TRACE") != "" {
		fmt.Fprintf(os.Stderr, "verify: case split at depth %d on %s\n", depth, abbreviate(cond.String(), 150))
	}
	c := truncate(cond, 1)
	for polarity, branch := range []*term{c, binaryTerm("xor", c, constTerm(1, 1))} {
		holds, decided := impliesEqualDepth(binaryTerm("and", premise, branch), a, b, widthOf, budget, depth+1)
		if os.Getenv("OAK_VERIFY_TRACE") != "" {
			fmt.Fprintf(os.Stderr, "verify: case split depth %d polarity %d: holds=%v decided=%v\n", depth, polarity, holds, decided)
		}
		if !decided {
			return false, false
		}
		if !holds {
			return false, true
		}
	}
	return true, true
}

// splitDepth bounds the case splits nested in one decision.
const splitDepth = 2

// pruneUnder rewrites terms under a premise: an ite whose condition the
// premise implies or refutes — decided on a small diagram of the premise
// and the condition alone — becomes the arm the premise selects, so that
// two sides which agree once a branch is settled become one term (equal
// structurally, no diagram of their arms needed), and any diagram still
// built is over the arms alone. The walk is memoized over the DAG; a
// condition past the small budget leaves its branch in place.
func pruneUnder(premise *term, terms []*term, widthOf func(string) int) []*term {
	mentioned := map[string]bool{}
	collectParams(premise, mentioned)
	for _, t := range terms {
		collectParams(t, mentioned)
	}
	names := make([]string, 0, len(mentioned))
	widths := map[string]int{}
	for name := range mentioned {
		names = append(names, name)
		widths[name] = widthOf(name)
	}
	sort.Strings(names)
	bl := newBlaster(names, widths)
	bl.bdd = newBDD(pruneNodeBudget)
	pBits := bl.blast(premise)
	trace := os.Getenv("OAK_VERIFY_TRACE") != ""
	if pBits == nil || bl.bdd.exceeded || pBits[0] == bddTrue {
		if trace {
			fmt.Fprintf(os.Stderr, "verify: pruning skipped: premise nil=%v exceeded=%v trivial=%v (%d nodes)\n", pBits == nil, bl.bdd.exceeded, pBits != nil && pBits[0] == bddTrue, len(bl.bdd.nodes))
		}
		return terms
	}
	assume := pBits[0]
	ites, settled, unblastable := 0, 0, 0
	defer func() {
		if trace {
			fmt.Fprintf(os.Stderr, "verify: pruning: %d branches met, %d settled, %d conditions beyond the small budget, %d nodes\n", ites, settled, unblastable, len(bl.bdd.nodes))
		}
	}()
	memo := map[*term]*term{}
	sizes := map[*term]int{}
	var rewrite func(t *term) *term
	rewrite = func(t *term) *term {
		if t == nil {
			return nil
		}
		if done, seen := memo[t]; seen {
			return done
		}
		out := t
		switch t.kind {
		case termConst, termParam:
		case termIte:
			if isLookupStep(t.cond, sizes) {
				// A table lookup's step (`index = k`) is never settled by a
				// premise worth splitting on; its condition would only spend
				// the budget.
				c, l, r := rewrite(t.cond), rewrite(t.left), rewrite(t.right)
				if c != t.cond || l != t.left || r != t.right {
					copy := *t
					copy.cond, copy.left, copy.right = c, l, r
					out = &copy
				}
				break
			}
			ites++
			cond := bl.blast(t.cond)
			if cond == nil || bl.bdd.exceeded {
				unblastable++
				break // the condition is beyond the small budget: keep the branch
			}
			implied := bl.bdd.apply(opAnd, assume, bl.bdd.not(cond[0])) == bddFalse
			refuted := bl.bdd.apply(opAnd, assume, cond[0]) == bddFalse
			if bl.bdd.exceeded {
				unblastable++
				break
			}
			switch {
			case implied:
				settled++
				out = adaptWidth(rewrite(t.left), t.width)
			case refuted:
				settled++
				out = adaptWidth(rewrite(t.right), t.width)
			default:
				if trace && termSize(t.left, sizes)+termSize(t.right, sizes) > 1000 {
					fmt.Fprintf(os.Stderr, "verify: pruning left a branch of %d nodes unsettled on %s\n", termSize(t.left, sizes)+termSize(t.right, sizes), abbreviate(t.cond.String(), 120))
				}
				c, l, r := rewrite(t.cond), rewrite(t.left), rewrite(t.right)
				if c != t.cond || l != t.left || r != t.right {
					copy := *t
					copy.cond, copy.left, copy.right = c, l, r
					out = &copy
				}
			}
		default:
			l, r := rewrite(t.left), rewrite(t.right)
			if l != t.left || r != t.right {
				copy := *t
				copy.left, copy.right = l, r
				out = &copy
			}
		}
		memo[t] = out
		return out
	}
	pruned := make([]*term, len(terms))
	for i, t := range terms {
		pruned[i] = rewrite(t)
	}
	return pruned
}

// isLookupStep recognizes the condition of one step of a table lookup
// (laneTable): an equality of a small index term with a constant.
func isLookupStep(cond *term, sizes map[*term]int) bool {
	return cond.kind == termCmp && cond.op == "eq" && cond.right.kind == termConst && termSize(cond.left, sizes) <= 8
}

// pruneNodeBudget bounds the diagram pruneUnder decides conditions on:
// conditions are small, and a pass that cannot settle them cheaply is
// skipped.
const pruneNodeBudget = 200000

// equalReductions decides two 1/0 results that each test whether some
// lane of a vector is nonzero — `any` as the Oak side spells it (an or of
// `lane ≠ 0` tests) and as the machine spells it (`umaxv`, `cmp #0`,
// `cset`, `eor #1`, distributed by cmpTerm) — by their lane tests: the
// same negation and the same lanes, each lane the same term on both
// sides. A reduction over lanes that are one term is one value, whatever
// order or width the reduction was spelled in; the diagram of the lanes
// themselves (a table-driven classification) is never needed.
func equalReductions(a, b *term) bool {
	lanesA, negA, okA := laneTests(a)
	lanesB, negB, okB := laneTests(b)
	if !okA || !okB || negA != negB || len(lanesA) != len(lanesB) || len(lanesA) == 0 {
		return false
	}
	used := make([]bool, len(lanesB))
	for _, lane := range lanesA {
		matched := false
		for j, other := range lanesB {
			if !used[j] && equalTerms(lane, other) {
				used[j] = true
				matched = true
				break
			}
		}
		if !matched {
			return false
		}
	}
	return true
}

// laneTests reads a 1/0 term as a negated-or-not disjunction of `x ≠ 0`
// tests and returns the x's; ok is false for any other shape.
func laneTests(t *term) (lanes []*term, negated bool, ok bool) {
	for {
		switch {
		case t.kind == termBinary && t.op == "and" && t.right.kind == termConst && t.right.value == 1:
			t = t.left // a Bool narrowed to its bit
			continue
		case t.kind == termBinary && t.op == "and" && t.right.kind == termConst && isLowMask(t.right.value) && t.left.width <= bits.Len64(t.right.value):
			t = t.left // a zero-extension
			continue
		case t.kind == termBinary && t.op == "xor" && t.right.kind == termConst && t.right.value == 1:
			negated = !negated
			t = t.left
			continue
		case t.kind == termIte && t.left.kind == termConst && t.right.kind == termConst && t.left.value == 1 && t.right.value == 0:
			t = t.cond // cset: the condition as 1/0
			continue
		case t.kind == termIte && t.left.kind == termConst && t.right.kind == termConst && t.left.value == 0 && t.right.value == 1:
			negated = !negated
			t = t.cond
			continue
		case t.kind == termCmp && t.op == "eq" && t.right.kind == termConst && t.right.value == 0 && t.left.kind == termIte && t.left.left.kind == termConst && t.left.right.kind == termConst && t.left.left.value == 1 && t.left.right.value == 0:
			negated = !negated // (c ? 1 : 0) == 0 is ¬c
			t = t.left.cond
			continue
		case t.kind == termCmp && t.op == "ne" && t.right.kind == termConst && t.right.value == 0 && t.left.kind == termIte && t.left.left.kind == termConst && t.left.right.kind == termConst && t.left.left.value == 1 && t.left.right.value == 0:
			t = t.left.cond // (c ? 1 : 0) != 0 is c
			continue
		}
		break
	}
	var collect func(t *term) bool
	collect = func(t *term) bool {
		switch {
		case t.kind == termConst && t.value == 0:
			return true
		case t.kind == termBinary && t.op == "or":
			return collect(t.left) && collect(t.right)
		case t.kind == termCmp && t.op == "ne" && t.right.kind == termConst && t.right.value == 0:
			lanes = append(lanes, t.left)
			return true
		case t.kind == termBinary && t.op == "and" && t.right.kind == termConst && isLowMask(t.right.value) && t.left.width <= bits.Len64(t.right.value):
			return collect(t.left) // a test zero-extended
		}
		return false
	}
	if !collect(t) {
		return nil, false, false
	}
	return lanes, negated, true
}

// splitCondition is the condition of the ite in a or b with the largest
// arms (by shared-node count), nil when neither has a branch.
func splitCondition(a, b *term) *term {
	sizes := map[*term]int{}
	var best *term
	bestSize := 0
	visited := map[*term]bool{}
	var walk func(t *term)
	walk = func(t *term) {
		if t == nil || visited[t] {
			return
		}
		visited[t] = true
		if t.kind == termIte && t.cond.kind != termConst {
			if size := termSize(t.left, sizes) + termSize(t.right, sizes); size > bestSize {
				best, bestSize = t.cond, size
			}
		}
		walk(t.cond)
		walk(t.left)
		walk(t.right)
	}
	walk(a)
	walk(b)
	return best
}

// termSize measures a term as a tree, saturating at termSizeCap: shared
// subterms count once per reference (a heuristic for the size of the
// diagram a branch's arms would need, not a node count).
func termSize(t *term, memo map[*term]int) int {
	if t == nil {
		return 0
	}
	if n, seen := memo[t]; seen {
		return n
	}
	n := min(termSizeCap, 1+termSize(t.cond, memo)+termSize(t.left, memo)+termSize(t.right, memo))
	memo[t] = n
	return n
}

const termSizeCap = 1 << 40

// implicationNodeLimit bounds the distinct term nodes an implication's
// three terms may hold before the decider gives up on the diagrams;
// implicationCallLimit bounds the implications one loop proof may try.
const (
	implicationNodeLimit = 1 << 16
	implicationCallLimit = 2048
)

// dagNodesExceed reports whether the terms hold more than limit distinct
// nodes between them, stopping the count there.
func dagNodesExceed(limit int, terms ...*term) bool {
	seen := map[*term]bool{}
	var walk func(t *term) bool
	walk = func(t *term) bool {
		if t == nil || seen[t] {
			return false
		}
		seen[t] = true
		if len(seen) > limit {
			return true
		}
		return walk(t.cond) || walk(t.left) || walk(t.right)
	}
	for _, t := range terms {
		if walk(t) {
			return true
		}
	}
	return false
}

// abbreviate cuts a rendering for a trace line.
func abbreviate(s string, n int) string {
	if len(s) <= n {
		return s
	}
	return s[:n] + "…"
}

// refutedByCoupling is refutedByValuation over the symbols the obligation
// mentions, at their declared widths.
func refutedByCoupling(premise, a, b *term, widthOf func(string) int) bool {
	width := a.width
	if b.width > width {
		width = b.width
	}
	a, b = adaptWidth(a, width), adaptWidth(b, width)
	mentioned := map[string]bool{}
	collectParams(premise, mentioned)
	collectParams(a, mentioned)
	collectParams(b, mentioned)
	names := make([]string, 0, len(mentioned))
	widths := map[string]int{}
	for name := range mentioned {
		names = append(names, name)
		widths[name] = widthOf(name)
	}
	sort.Strings(names)
	return refutedByValuation(premise, a, b, names, widths)
}

// impliesEqualByArms proves premise → (a = b) for two conditionals by
// their parts: the conditions equal under the premise, the taken arms
// equal under the premise and the condition, the other arms under its
// negation. A diagram of the whole repeats the condition's in every
// result bit — a conditional on a test over the loop's inputs (a literal
// occurs at this position) selecting an arm over the same inputs (the
// position) costs the test's diagram thirty-two times over, past any
// budget, where the parts cost it once. The rule proves and never
// refutes: conditionals with different conditions may still agree
// (where their arms do), so a part that fails leaves the decision to
// the whole. A mask over a conditional is pushed into its arms first.
func impliesEqualByArms(premise, a, b *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	a, b = pushMask(a), pushMask(b)
	if a.kind != termIte || b.kind != termIte {
		return false, false
	}
	trace := os.Getenv("OAK_VERIFY_TRACE") != ""
	if holds, decided := impliesEqualDepth(premise, truncate(a.cond, 1), truncate(b.cond, 1), widthOf, budget, depth); !decided || !holds {
		if trace {
			fmt.Fprintf(os.Stderr, "verify: arm rule: conditions not proven equal (holds=%v decided=%v; a.cond %d nodes, b.cond %d nodes)\n  a.cond: %s\n  b.cond: %s\n", holds, decided, termSize(a.cond, map[*term]int{}), termSize(b.cond, map[*term]int{}), spineOf(a.cond, 4), spineOf(b.cond, 4))
		}
		// The conditions may be each other's negation with the arms
		// swapped (`x == 0 ? p : q` against `x != 0 ? q : p`, a branch
		// taken on the other side): the arms are compared crosswise under
		// the proven negation, once.
		if holds, decided := impliesEqualDepth(premise, truncate(a.cond, 1), notTerm(b.cond), widthOf, budget, depth); decided && holds {
			return impliesEqualArms(premise, a, iteTerm(notTerm(b.cond), b.right, b.left), widthOf, budget, depth)
		}
		return false, false
	}
	return impliesEqualArms(premise, a, b, widthOf, budget, depth)
}

// impliesEqualCongruent proves premise → (a = b) for two terms of one
// shape by their operands: the same operation over operands proven equal
// pairwise (a commutative one also with the operands crossed), the same
// comparison, or a read of the same span at indices proven equal. Like
// the arm rule it proves and never refutes — different operands may give
// one value — so a part that fails leaves the decision to the whole. A
// sum of a selected value and a call's result on both sides, each side
// a diagram beyond any budget, is two small decisions.
func impliesEqualCongruent(premise, a, b *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	if a.kind != b.kind || a.width != b.width {
		if os.Getenv("OAK_VERIFY_TRACE") != "" {
			fmt.Fprintf(os.Stderr, "verify: congruence: shapes differ\n  a: %s\n  b: %s\n", spineOf(a, 4), spineOf(b, 4))
			if termSize(a, map[*term]int{})+termSize(b, map[*term]int{}) < 60 {
				fmt.Fprintf(os.Stderr, "  a in full: %s\n  b in full: %s\n", a, b)
			}
		}
		return false, false
	}
	pair := func(x, y *term) bool {
		if x == nil || y == nil {
			return x == y
		}
		holds, decided := impliesEqualDepth(premise, x, y, widthOf, budget, depth)
		if !(decided && holds) && os.Getenv("OAK_VERIFY_TRACE") != "" {
			fmt.Fprintf(os.Stderr, "verify: congruence: operands not proven equal (holds=%v decided=%v)\n  a: %s\n  b: %s\n", holds, decided, spineOf(x, 4), spineOf(y, 4))
		}
		return decided && holds
	}
	switch a.kind {
	case termBinary:
		if a.op != b.op || a.left.width != b.left.width || a.right.width != b.right.width {
			return false, false
		}
		if pair(a.left, b.left) && pair(a.right, b.right) {
			return true, true
		}
		switch a.op {
		case "add", "and", "or", "xor", "mul":
			if a.left.width == b.right.width && a.right.width == b.left.width && pair(a.left, b.right) && pair(a.right, b.left) {
				return true, true
			}
		}
	case termCmp:
		if a.op == b.op && pair(a.left, b.left) && pair(a.right, b.right) {
			return true, true
		}
	case termSelect:
		if a.name == b.name && pair(a.left, b.left) {
			return true, true
		}
	}
	return false, false
}

// spineOf renders a term's operator spine to the given depth (trace).
func spineOf(t *term, depth int) string {
	if t == nil {
		return "-"
	}
	if depth == 0 {
		return fmt.Sprintf("…%d", termSize(t, map[*term]int{}))
	}
	switch t.kind {
	case termConst:
		return fmt.Sprintf("%d", t.value)
	case termParam:
		return t.name
	case termSelect:
		return t.name + "[" + spineOf(t.left, depth-1) + "]"
	case termIte:
		return fmt.Sprintf("ite(%s, %s, %s)", spineOf(t.cond, depth-1), spineOf(t.left, depth-1), spineOf(t.right, depth-1))
	case termCmp:
		return fmt.Sprintf("(%s %s %s)", spineOf(t.left, depth-1), t.op, spineOf(t.right, depth-1))
	}
	return fmt.Sprintf("%s%d(%s, %s)", t.op, t.width, spineOf(t.left, depth-1), spineOf(t.right, depth-1))
}

// impliesEqualArms is the arms' half of impliesEqualByArms: a's condition
// already proven b's, each pair of arms under it or its negation.
func impliesEqualArms(premise, a, b *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	taken := binaryTerm("and", premise, truncate(a.cond, 1))
	if holds, decided := impliesEqualDepth(taken, a.left, b.left, widthOf, budget, depth); !decided || !holds {
		if os.Getenv("OAK_VERIFY_TRACE") != "" {
			fmt.Fprintf(os.Stderr, "verify: arm rule: taken arms not proven equal (holds=%v decided=%v; %d vs %d nodes)\n", holds, decided, termSize(a.left, map[*term]int{}), termSize(b.left, map[*term]int{}))
		}
		return false, false
	}
	other := binaryTerm("and", premise, notTerm(a.cond))
	if holds, decided := impliesEqualDepth(other, a.right, b.right, widthOf, budget, depth); !decided || !holds {
		if os.Getenv("OAK_VERIFY_TRACE") != "" {
			fmt.Fprintf(os.Stderr, "verify: arm rule: other arms not proven equal (holds=%v decided=%v; %d vs %d nodes)\n", holds, decided, termSize(a.right, map[*term]int{}), termSize(b.right, map[*term]int{}))
		}
		return false, false
	}
	return true, true
}

// pushMask moves a low mask over a conditional into its arms: the
// conditional's width is the arms', a zero-extension of a narrower
// conditional becomes one of each arm (the same term a parameter's
// extension is on the other side).
func pushMask(t *term) *term {
	if t.kind != termBinary || t.op != "and" || t.right.kind != termConst || !isLowMask(t.right.value) || t.left.kind != termIte {
		return t
	}
	inner := t.left
	arm := func(x *term) *term {
		if t.right.value == mask(inner.width) && inner.width < t.width {
			return zeroExtend(adaptWidth(x, inner.width), t.width)
		}
		return binaryTerm("and", adaptWidth(x, t.width), t.right)
	}
	return iteTerm(inner.cond, pushMask(arm(inner.left)), pushMask(arm(inner.right)))
}

// diagnoseBlast (under OAK_VERIFY_DIAGNOSE; it builds a diagram per
// subterm) reports, along the path of the largest subterm, the diagram
// each subterm of t needs on its own under bl's order and premise: where
// a decision past the budget spends it.
func diagnoseBlast(bl *blaster, premise, t *term) {
	fresh := func() *blaster {
		nb := *bl
		nb.bdd = newBDD(blastNodeBudget)
		nb.selects = nil
		nb.memo = nil
		nb.owners = map[int]variableOwner{}
		nb.assumed = false
		p := nb.blast(premise)
		if p != nil && p[0] != bddTrue {
			nb.assume, nb.assumed = p[0], true
		}
		return &nb
	}
	size := func(t *term) int {
		nb := fresh()
		before := len(nb.bdd.nodes)
		nb.blast(t)
		if nb.bdd.exceeded {
			return -1
		}
		return len(nb.bdd.nodes) - before
	}
	for depth := 0; t != nil && depth < 12; depth++ {
		fmt.Fprintf(os.Stderr, "  diagnose depth %d: %d nodes for %.200s\n", depth, size(t), t.String())
		var largest *term
		worst := -2
		for _, child := range []*term{t.cond, t.left, t.right} {
			if child == nil || child.kind == termConst || child.kind == termParam {
				continue
			}
			n := size(child)
			if n == -1 {
				n = 1 << 30
			}
			if n > worst {
				worst, largest = n, child
			}
		}
		t = largest
	}
}

// smallSides is the size, in term nodes, up to which an implication's two
// sides are first decided without the premise.
const smallSides = 64

// relevantPremise keeps the premise's conjuncts that can bear on a = b:
// those mentioning a symbol of a or b, and, to a fixpoint, those sharing
// a symbol with a kept conjunct. Reports whether any conjunct was
// dropped (nothing to gain otherwise). Element reads of the same span
// count as sharing its name.
func relevantPremise(premise, a, b *term) (*term, bool) {
	var conjuncts []*term
	var split func(t *term)
	split = func(t *term) {
		if t.kind == termBinary && t.op == "and" && t.width == 1 {
			split(t.left)
			split(t.right)
			return
		}
		conjuncts = append(conjuncts, t)
	}
	split(premise)
	if len(conjuncts) < 2 {
		return premise, false
	}
	symbolsOf := func(t *term) map[string]bool {
		names := map[string]bool{}
		collectParams(t, names)
		out := map[string]bool{}
		for name := range names {
			if span, _, isElement := elementParam(name); isElement {
				name = span
			}
			out[rootParam(name)] = true
		}
		return out
	}
	live := symbolsOf(a)
	for name := range symbolsOf(b) {
		live[name] = true
	}
	kept := make([]bool, len(conjuncts))
	symbols := make([]map[string]bool, len(conjuncts))
	for i, c := range conjuncts {
		symbols[i] = symbolsOf(c)
	}
	for changed := true; changed; {
		changed = false
		for i, c := range conjuncts {
			if kept[i] || c.kind == termConst {
				continue
			}
			shares := false
			for name := range symbols[i] {
				if live[name] {
					shares = true
					break
				}
			}
			if !shares {
				continue
			}
			kept[i], changed = true, true
			for name := range symbols[i] {
				live[name] = true
			}
		}
	}
	var out *term
	dropped := false
	for i, c := range conjuncts {
		if !kept[i] {
			if c.kind != termConst || c.value != 1 {
				dropped = true
			}
			continue
		}
		if out == nil {
			out = c
		} else {
			out = binaryTerm("and", out, c)
		}
	}
	if out == nil {
		out = constTerm(1, 1)
	}
	return out, dropped
}

// narrowByPremise bounds the parameters' widths under the premise: a
// conjunct `p < c` (or `p <= c`) over a parameter leaves p's bits from the
// bound's up zero wherever the premise holds, so the decision reads p at
// that many bits. The implication is unchanged — where the bits are set
// the premise fails and it holds — and a conditional chain over a loop
// index below sixteen is decided over the index's four bits, an adder
// over it copied sixteen times rather than once per value of a word.
func narrowByPremise(premise *term, widths map[string]int) {
	var walk func(t *term)
	walk = func(t *term) {
		switch {
		case t.kind == termBinary && t.op == "and":
			walk(t.left)
			walk(t.right)
		case t.kind == termCmp && t.left.kind == termParam && t.right.kind == termConst:
			var bound uint64 // p ranges over [0, bound)
			switch t.op {
			case "lo":
				bound = t.right.value
			case "ls":
				bound = t.right.value + 1
			}
			if bound == 0 {
				return
			}
			k := bits.Len64(bound - 1)
			if k < 1 {
				k = 1
			}
			if w, known := widths[t.left.name]; known && k < w {
				widths[t.left.name] = k
			}
		}
	}
	walk(premise)
}

// impliesEqualUnder is impliesEqual's bit-level decision under one
// variable order.
func impliesEqualUnder(bl *blaster, premise, a, b *term, width int) (holds bool, decided bool) {
	trace := os.Getenv("OAK_VERIFY_TRACE") != ""
	stage := func(what string) {
		if trace && bl.bdd.exceeded {
			fmt.Fprintf(os.Stderr, "verify: order %q exceeded while blasting %s (%d nodes)\n", bl.label, what, len(bl.bdd.nodes))
		}
	}
	pBits := bl.blast(premise)
	stage("the premise")
	if pBits == nil {
		return false, false
	}
	if pBits[0] != bddTrue {
		bl.assume, bl.assumed = pBits[0], true // the premise settles the branches it decides
	}
	aBits := bl.blast(a)
	stage("a")
	if bl.bdd.exceeded && bl.label == "selectors first" && os.Getenv("OAK_VERIFY_DIAGNOSE") != "" {
		diagnoseBlast(bl, premise, a)
	}
	bBits := bl.blast(b)
	stage("b")
	if pBits == nil || aBits == nil || bBits == nil || bl.bdd.exceeded {
		return false, false
	}
	allEqual := bddTrue
	for i := 0; i < width; i++ {
		allEqual = bl.bdd.apply(opAnd, allEqual, bl.bdd.not(bl.bdd.apply(opXor, aBits[i], bBits[i])))
		if bl.bdd.exceeded {
			stage(fmt.Sprintf("the equality at bit %d", i))
			break
		}
	}
	implication := bl.bdd.apply(opOr, bl.bdd.not(pBits[0]), allEqual)
	stage("the implication")
	if bl.bdd.exceeded {
		return false, false
	}
	if implication == bddTrue {
		return true, true
	}
	// Under the element reads' functional consistency (blaster.consistency)
	// the premise and the reads' equalities together may imply the
	// coupling where the independent reads did not.
	premiseHolds := bl.apply(opAnd, pBits[0], bl.consistency())
	implication = bl.apply(opOr, bl.not(premiseHolds), allEqual)
	stage("the consistency")
	if bl.bdd.exceeded {
		return false, false
	}
	return implication == bddTrue, true
}

// refutedByValuation looks for a valuation of the symbols satisfying the
// premise under which a and b differ: a cheap, sound refutation before any
// diagram is built (and the pruning of the coupling search). Span
// elements stay unbound so that they read the fixed memory, consistently
// with the select terms over the same span.
func refutedByValuation(premise, a, b *term, names []string, widths map[string]int) bool {
	var free []string
	for _, name := range names {
		if _, _, isElement := elementParam(name); isElement && !strings.HasPrefix(name, "loop") {
			continue
		}
		free = append(free, name)
	}
	// The constants the obligation compares against (a lane index, a
	// stride, a length bound) are the values a symbol must take for an
	// index to select a lane or a guard to turn: they join the small and
	// the random values.
	constants := []uint64{0, 1}
	seen := map[uint64]bool{0: true, 1: true}
	collectConstants(premise, seen, &constants)
	collectConstants(a, seen, &constants)
	collectConstants(b, seen, &constants)
	seed := uint64(0xD1B54A32D192ED03)
	random := func() uint64 {
		seed ^= seed << 13
		seed ^= seed >> 7
		seed ^= seed << 17
		return seed
	}
	// Targeted valuations first: a comparison of a symbol with a constant
	// (`i = 11`, the index selecting a lane; `len < 64`, a guard) is
	// decided one way or the other by the symbol taking the constant and
	// its neighbors, so each such pair is tried with the rest random.
	var targets []comparisonTarget
	collectTargets(premise, &targets, map[*term]bool{})
	collectTargets(a, &targets, map[*term]bool{})
	collectTargets(b, &targets, map[*term]bool{})
	if len(targets) > couplingTargets {
		targets = targets[:couplingTargets]
	}
	// The terms are numbered once and evaluated through slices
	// (termEvaluator, as decideEqual's witness pass evaluates); the
	// valuations are thinned so the pass visits a bounded number of nodes,
	// since an obligation over summarized callees is a large DAG.
	evaluator := newTermEvaluator(premise, a, b)
	rounds := couplingValuations
	if visits := len(evaluator.terms) * (3*len(targets) + rounds); visits > witnessVisitBudget {
		rounds = witnessVisitBudget / (3*len(targets) + 1) / max(len(evaluator.terms), 1)
		if rounds < 8 {
			rounds = 8
		}
	}
	// The premise's own bindings: a conjunct comparing a symbol with a
	// term (`g = (total + 15) >> 4`, an inner loop's exit fact; `off <
	// len - 66`, a guard) is satisfied by the symbol taking the term's
	// value (its neighbor for a strict comparison), so each valuation is
	// settled through them before the premise is evaluated — a premise
	// of exit facts over a dozen loop counters is otherwise satisfied by
	// no random valuation, and an obligation over two distinct symbols
	// (`off = found`, a wrong pairing) goes undecided instead of refuted.
	bindings := premiseBindings(premise)
	settle := func(env map[string]uint64, pinned string) {
		for pass := 0; pass < 3 && len(bindings) > 0; pass++ {
			for _, bind := range bindings {
				if bind.name == pinned {
					continue
				}
				value := evaluator.evaluate(bind.value, env)
				switch bind.op {
				case "lo", "lt":
					value--
				case "hi", "gt":
					value++
				}
				env[bind.name] = value & mask(widths[bind.name])
			}
		}
	}
	for _, target := range targets {
		for _, delta := range []uint64{0, 1, ^uint64(0)} {
			env := map[string]uint64{}
			for _, name := range free {
				env[name] = random() & mask(widths[name])
			}
			env[target.name] = (target.value + delta) & mask(widths[target.name])
			settle(env, target.name)
			if evaluator.evaluate(premise, env) != 0 && evaluator.evaluate(a, env) != evaluator.evaluate(b, env) {
				return true
			}
		}
	}
	for round := 0; round < rounds; round++ {
		env := map[string]uint64{}
		for _, name := range free {
			value := random()
			switch round % 5 {
			case 0:
				value = 0 // every symbol zero, then small values
			case 1:
				value = seed % 8
			case 2:
				value = mask(widths[name]) - seed%4
			case 3:
				value = constants[(seed>>8)%uint64(len(constants))]
				if seed&1 == 1 {
					value++
				}
			}
			env[name] = value & mask(widths[name])
		}
		if round%2 == 1 {
			settle(env, "")
		}
		if evaluator.evaluate(premise, env) == 0 {
			continue
		}
		if evaluator.evaluate(a, env) != evaluator.evaluate(b, env) {
			return true
		}
	}
	return false
}

// A premiseBinding is a premise conjunct comparing a symbol with a term:
// the symbol, the term, and the comparison (its negation folded in).
type premiseBinding struct {
	name  string
	value *term
	op    string
}

// premiseBindings collects the conjuncts of a premise that compare a
// symbol (possibly masked) with a term not mentioning it, as bindings a
// valuation can settle: `x = t`, `x < t`, `x ≤ t`, `x ≥ t`, `x > t`, or
// the negation of one. Disjunctions and conditionals are not looked into.
func premiseBindings(premise *term) []premiseBinding {
	var out []premiseBinding
	var walk func(t *term)
	walk = func(t *term) {
		if t == nil {
			return
		}
		if t.kind == termBinary && t.op == "and" && t.width == 1 {
			walk(t.left)
			walk(t.right)
			return
		}
		negated := false
		if t.kind == termBinary && t.op == "xor" && t.right.kind == termConst && t.right.value == 1 {
			negated, t = true, t.left
		}
		if t.kind != termCmp {
			return
		}
		op := t.op
		if negated {
			op = negatedCondition[op]
		}
		symbol := func(side *term) (string, bool) {
			for side != nil && side.kind == termBinary && side.op == "and" && side.right.kind == termConst && isLowMask(side.right.value) {
				side = side.left
			}
			if side != nil && side.kind == termParam {
				return side.name, true
			}
			return "", false
		}
		flip := map[string]string{"eq": "eq", "lo": "hi", "ls": "hs", "hs": "ls", "hi": "lo", "lt": "gt", "le": "ge", "ge": "le", "gt": "lt"}
		if name, isSymbol := symbol(t.left); isSymbol && !mentions(t.right, name) {
			if _, known := flip[op]; known {
				out = append(out, premiseBinding{name: name, value: t.right, op: op})
			}
			return
		}
		if name, isSymbol := symbol(t.right); isSymbol && !mentions(t.left, name) {
			if flipped, known := flip[op]; known {
				out = append(out, premiseBinding{name: name, value: t.left, op: flipped})
			}
		}
	}
	walk(premise)
	return out
}

// mentions reports whether the term reads the named symbol.
func mentions(t *term, name string) bool {
	seen := map[*term]bool{}
	var walk func(t *term) bool
	walk = func(t *term) bool {
		if t == nil || seen[t] {
			return false
		}
		seen[t] = true
		if t.kind == termParam && t.name == name {
			return true
		}
		return walk(t.cond) || walk(t.left) || walk(t.right)
	}
	return walk(t)
}

// A comparisonTarget is a symbol compared with a constant somewhere in an
// obligation, and the constant.
type comparisonTarget struct {
	name  string
	value uint64
}

// collectTargets gathers the (symbol, constant) pairs of the comparisons
// in a term, looking through width changes of the symbol.
func collectTargets(t *term, into *[]comparisonTarget, visited map[*term]bool) {
	if t == nil || visited[t] {
		return
	}
	visited[t] = true
	if t.kind == termCmp {
		symbol := func(side *term) (string, bool) {
			for side != nil && side.kind == termBinary && side.op == "and" && side.right.kind == termConst && isLowMask(side.right.value) {
				side = side.left
			}
			if side != nil && side.kind == termParam {
				return side.name, true
			}
			return "", false
		}
		if name, isSymbol := symbol(t.left); isSymbol && t.right.kind == termConst {
			*into = append(*into, comparisonTarget{name: name, value: t.right.value})
		} else if name, isSymbol := symbol(t.right); isSymbol && t.left.kind == termConst {
			*into = append(*into, comparisonTarget{name: name, value: t.left.value})
		}
	}
	collectTargets(t.cond, into, visited)
	collectTargets(t.left, into, visited)
	collectTargets(t.right, into, visited)
}

// couplingTargets caps the targeted valuations of one obligation.
const couplingTargets = 96

// collectConstants gathers the constants a term mentions (once each).
func collectConstants(t *term, seen map[uint64]bool, into *[]uint64) {
	collectConstantsVisited(t, seen, into, map[*term]bool{})
}

func collectConstantsVisited(t *term, seen map[uint64]bool, into *[]uint64, visited map[*term]bool) {
	if t == nil || visited[t] {
		return
	}
	visited[t] = true
	if t.kind == termConst {
		if !seen[t.value] && len(*into) < 64 {
			seen[t.value] = true
			*into = append(*into, t.value)
		}
		return
	}
	collectConstantsVisited(t.cond, seen, into, visited)
	collectConstantsVisited(t.left, seen, into, visited)
	collectConstantsVisited(t.right, seen, into, visited)
}

// couplingValuations is the number of valuations tried before a diagram.
const couplingValuations = 80

// couplingSearchBudget bounds the pairings the coupling search visits.
const couplingSearchBudget = 1024

// isUncoupledLoopSymbol reports a term that is a loop's fresh symbol
// itself, at any width, which the substitution does not yet map (an inner
// loop's register whose header value is the outer loop's symbol for it,
// the outer slot still open).
func isUncoupledLoopSymbol(t *term, sigma map[string]*term) bool {
	for t != nil {
		switch t.kind {
		case termParam:
			return strings.HasPrefix(t.name, "loop") && sigma[t.name] == nil
		case termBinary:
			if t.op == "and" && t.right.kind == termConst {
				t = t.left
				continue
			}
		}
		return false
	}
	return false
}

// isFreshSymbol reports a one-iteration value that is the variable's own
// fresh symbol at any width: the iteration left the variable unchanged.
func isFreshSymbol(next, fresh *term) bool {
	if next == nil || fresh == nil {
		return false
	}
	for next != nil {
		switch next.kind {
		case termParam:
			return next.name == fresh.name
		case termBinary:
			if next.op == "and" && next.right.kind == termConst {
				next = next.left
				continue
			}
		}
		return false
	}
	return false
}

// slotUnchanged reports a slot every one of whose locals the iteration
// leaves unchanged.
func slotUnchanged(s loopSlot, ev *loopEvent) bool {
	for _, local := range s.locals {
		if !isFreshSymbol(ev.next[local], ev.fresh[local]) {
			return false
		}
	}
	return true
}

// sigmaShow renders a coupling substitution for the trace.
func sigmaShow(sigma map[string]*term) string {
	var parts []string
	for name, value := range sigma {
		parts = append(parts, name+"="+value.String())
	}
	sort.Strings(parts)
	return strings.Join(parts, ", ")
}

// renameLoopMemory rewrites every read of the loop's unknown memory
// `from` in the term as a read of the memory the loop found on entry —
// the entry log's element at the index over the span's entry memory —
// for the case in which the loop ran no iteration. Shared subterms are
// rewritten once.
func renameLoopMemory(t *term, from string, entryLog []*spanWrite, base string, width int, memo map[*term]*term) *term {
	if t == nil {
		return nil
	}
	if done, seen := memo[t]; seen {
		return done
	}
	var out *term
	switch t.kind {
	case termConst, termParam:
		out = t
	case termSelect:
		index := renameLoopMemory(t.left, from, entryLog, base, width, memo)
		if t.name == from {
			out = memoryAt(entryLog, index, selectTerm(base, index, t.width))
		} else if index != t.left {
			copied := *t
			copied.left = index
			out = &copied
		} else {
			out = t
		}
	default:
		left := renameLoopMemory(t.left, from, entryLog, base, width, memo)
		right := renameLoopMemory(t.right, from, entryLog, base, width, memo)
		cond := renameLoopMemory(t.cond, from, entryLog, base, width, memo)
		if left == t.left && right == t.right && cond == t.cond {
			out = t
		} else {
			copied := *t
			copied.left, copied.right, copied.cond = left, right, cond
			copied.id = 0
			out = &copied
		}
	}
	memo[t] = out
	return out
}

// loopSplit is a loop whose memory marker the two sides may place under
// different conditions: the Oak side where the loop is lowered, the
// machine side only where its path reached the loop and entered it — a
// peeled or rotated loop, a loop inside a conditional arm.
type loopSplit struct {
	ev      *loopEvent // the Oak side's event
	reached *term      // the machine's condition for reaching the loop, over the Oak symbols; nil when always
}

// splitsFor builds the splits for the listed loops (indices into the
// matched events).
func splitsFor(indices []int, oakLoops, asmLoops []*loopEvent, sigma map[string]*term) []loopSplit {
	var out []loopSplit
	for _, k := range indices {
		if k < 0 || k >= len(oakLoops) || k >= len(asmLoops) {
			continue
		}
		s := loopSplit{ev: oakLoops[k]}
		if reached := asmLoops[k].reached; reached != nil {
			s.reached = truncate(substitute(reached, sigma), 1)
		}
		out = append(out, s)
	}
	return out
}

// earlierSiblings lists the loops before k under the same parent: the
// loops whose markers loop k's entry memory may carry.
func earlierSiblings(k int, oakLoops []*loopEvent) []int {
	var out []int
	for i := 0; i < k && i < len(oakLoops); i++ {
		if oakLoops[i].parent == oakLoops[k].parent {
			out = append(out, i)
		}
	}
	return out
}

// spanEqualSplitting decides that two span memories agree. When the
// direct decision closes as unequal, it splits on whether each listed
// loop ran — reached and entered, over the header values: then both
// sides keep the loop's marker; otherwise the loop's unknown memory is
// the memory it found on entry, on both sides (renameLoopMemory), which
// is what the machine's conditional marker spells. A loop that never ran
// leaves memory as it found it. At most two loops split, four cases.
func spanEqualSplitting(premise *term, name string, elemWidth int, oakMemory, asmMemory *term, splits []loopSplit, implies func(premise, a, b *term) (bool, bool)) (equal, decided bool) {
	if equal, decided = implies(premise, oakMemory, asmMemory); !decided || equal {
		return equal, decided // closed, or past the budget: the cases would be too
	}
	var marking []loopSplit
	for _, s := range splits {
		if _, marked := s.ev.entry[name]; marked {
			marking = append(marking, s)
		}
	}
	if len(marking) == 0 || len(marking) > 2 {
		return equal, decided
	}
	allEqual := true
	for mask := 0; mask < 1<<len(marking); mask++ {
		p, o, a := premise, oakMemory, asmMemory
		for i, s := range marking {
			ev := s.ev
			headerSigma := map[string]*term{}
			for v, fresh := range ev.fresh {
				if header, ok := ev.header[v]; ok {
					headerSigma[fresh.name] = header
				}
			}
			runs := truncate(substitute(ev.cond, headerSigma), 1)
			if s.reached != nil {
				runs = binaryTerm("and", runs, s.reached)
			}
			if mask&(1<<i) != 0 {
				p = binaryTerm("and", p, runs)
				continue
			}
			p = binaryTerm("and", p, binaryTerm("xor", runs, constTerm(1, 1)))
			from := loopMemoryName(ev.index, name)
			o = renameLoopMemory(o, from, ev.entry[name], name, elemWidth, map[*term]*term{})
			a = renameLoopMemory(a, from, ev.entry[name], name, elemWidth, map[*term]*term{})
		}
		caseEqual, caseDecided := implies(p, o, a)
		if !caseDecided {
			return false, false
		}
		if !caseEqual {
			allEqual = false
		}
	}
	return allEqual, true
}
