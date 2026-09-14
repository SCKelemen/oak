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
	"os"
	"sort"
	"strings"

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
}

// findLoops recognizes loops by their back edges, keyed by the exit branch.
// Back edges are met in item order, so an inner loop is recognized before
// the outer body containing it is examined.
func findLoops(items []Item, labels map[string]int) map[int]loopShape {
	loops := map[int]loopShape{}
	innerHeaders := map[int]int{} // header index -> back edge index of a recognized loop
	for back, item := range items {
		branch, isBranch := item.(Instruction)
		if !isBranch || !isUnconditionalJump(branch.Mnemonic) {
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
			if isGuardBranch(items, labels, instr) || isHeaderLoad(instr) {
				continue
			}
			if isConditionalBranch(instr.Mnemonic) {
				target, ok := labels[instr.Operands[len(instr.Operands)-1].(Symbol).Name]
				switch {
				case !ok:
					wellFormed = false
				case target > back:
					if exitLabel < 0 {
						exitLabel = target
					}
					if target != exitLabel {
						wellFormed = false
					}
					exits = append(exits, scan)
					bodyStart = scan + 1
				case target > scan:
					forwards = append(forwards, forward{at: scan, target: target})
					pending[target] = true
				default:
					wellFormed = false
				}
				if !wellFormed {
					break
				}
				continue
			}
			if isUnconditionalJump(instr.Mnemonic) || isStoreMnemonic(instr.Mnemonic) || isLoad(instr.Mnemonic) || isFrameMemory(instr) || hasVectorOperand(instr) {
				break
			}
			switch instr.Mnemonic {
			case "bl", "ret", "eret", "jal", "jalr", "auipc", "jr", "call":
				wellFormed = false
			}
			if !wellFormed {
				break
			}
		}
		if !wellFormed || len(exits) == 0 || bodyStart >= back {
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
			continue
		}
		exitIndex := exits[0]
		cmpIndex := -1
		for i := bodyStart; i < back; i++ {
			instr, isInstr := items[i].(Instruction)
			if !isInstr {
				continue // an inner label
			}
			switch instr.Mnemonic {
			case "bl", "ret", "eret", "jal", "jalr", "auipc", "jr", "call":
				wellFormed = false
			case "b", "j", "b.", "cbz", "cbnz", "tbz", "tbnz", "beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz", "bnez", "bgez", "bltz", "blez", "bgtz":
				target, ok := labels[instr.Operands[len(instr.Operands)-1].(Symbol).Name]
				if !ok || target >= back {
					// A guard's branch to the trap block is not an exit: the
					// path it takes delivers no result (docs/spec/94-assembler.md §8).
					if !ok || !isTrapBlock(items, target) || isUnconditionalJump(instr.Mnemonic) {
						wellFormed = false
					}
				} else if target <= i {
					// A backward branch inside the body: admitted only as
					// the back edge of a recognized inner loop lying inside.
					if innerBack, isInner := innerHeaders[target]; !isInner || innerBack != i || target <= header {
						wellFormed = false
					}
				}
			}
		}
		if !wellFormed {
			continue
		}
		shape := loopShape{header: header, cmp: cmpIndex, exit: exitIndex, exitLabel: exitLabel, bodyStart: bodyStart, bodyEnd: back, exits: exits, internal: internal}
		for _, at := range exits {
			loops[at] = shape // an undecided branch at any exit test summarizes the loop
		}
		for _, at := range internal {
			loops[at] = shape // an undecided short-circuit branch in the header too
		}
		innerHeaders[header] = back
	}
	return loops
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
}

func (ev *loopEvent) freshName(v string) string { return fmt.Sprintf("loop%d.%s", ev.index, v) }

// loopEvent summarizes the top-level asm loop whose exit branch was just
// reached with an undecided condition, then continues past the exit.
func (x *pathExecutor) loopEvent(shape loopShape, exit Instruction, state *symbolicState) (*term, string, bool) {
	post, reason, ok := x.summarizeLoop(shape, exit, state)
	if !ok {
		return nil, reason, false
	}
	// The cells written past the exit belong to a body the verdict trusts
	// (package state around a data-dependent loop): the result suffices.
	result, _, reason, ok := x.run(shape.exitLabel, post)
	return result, reason, ok
}

// summarizeLoop records the loop event and returns the state past the
// exit: the loop-carried registers hold their fresh symbols, scratch
// registers are unbound.
func (x *pathExecutor) summarizeLoop(shape loopShape, exit Instruction, state *symbolicState) (*symbolicState, string, bool) {
	if x.concrete {
		return nil, "a loop that a witness run could not decide", false
	}
	if len(x.loops) >= loopEventBudget {
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
	for at := shape.header + 1; at < shape.bodyStart; at++ {
		instr, isInstr := x.items[at].(Instruction)
		if !isInstr || instr.Mnemonic == "cmp" || instr.Mnemonic == "tst" || isConditionalBranch(instr.Mnemonic) || len(instr.Operands) == 0 {
			continue
		}
		if dest, isReg := instr.Operands[0].(Register); isReg && !dest.ZeroRegister() && dest.Class != ClassV {
			headerWritten[dest.Num] = true
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
	writtenSlots := map[int64]bool{}
	for i := shape.bodyStart; i < shape.bodyEnd; i++ {
		instr, isInstr := x.items[i].(Instruction)
		if !isInstr || isConditionalBranch(instr.Mnemonic) || isUnconditionalJump(instr.Mnemonic) {
			continue
		}
		if isFrameMemory(instr) && isStoreMnemonic(instr.Mnemonic) {
			mem := instr.Operands[len(instr.Operands)-1].(Memory)
			if mem.Mode != MemOffset {
				return nil, "a frame access moving sp in a loop body", false
			}
			addr := -state.disp + mem.Offset
			for _, reg := range registerOperands(instr.Operands[:len(instr.Operands)-1]) {
				size := memorySizeReg(instr.Mnemonic, reg)
				if isPairAccess(instr.Mnemonic) {
					size /= 2
				}
				if size%8 != 0 {
					return nil, "a narrow frame slot written in a loop body", false
				}
				for k := int64(0); k < size; k += 8 {
					writtenSlots[addr+k] = true
				}
				addr += size
			}
			continue
		}
		if isStoreMnemonic(instr.Mnemonic) {
			continue
		}
		if dest, isReg := instr.Operands[0].(Register); isReg && dest.Class == ClassV {
			writtenV[dest.Num] = true
		}
	}
	ev := &loopEvent{index: len(x.loops) + 1, header: map[string]*term{}, fresh: map[string]*term{}, width: map[string]int{}, next: map[string]*term{}}
	if n := len(x.loopStack); n > 0 {
		ev.parent = x.loopStack[n-1]
	}
	x.loops = append(x.loops, ev)
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
	slots := make([]int64, 0, len(writtenSlots))
	for addr := range writtenSlots {
		slots = append(slots, addr)
	}
	sort.Slice(slots, func(i, j int) bool { return slots[i] < slots[j] })
	if freshState.frame == nil {
		freshState.frame = map[int64]frameSlot{}
	}
	for _, addr := range slots {
		name := fmt.Sprintf("s%d", addr)
		fresh := paramTerm(ev.freshName(name), 64)
		x.declared[fresh.name] = 64
		value, bound := state.loadSlot(addr, 8)
		freshState.storeSlot(addr, fresh, 8)
		if !bound {
			scratchSlots[addr] = true
			continue
		}
		ev.vars = append(ev.vars, name)
		ev.width[name] = 64
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
	// The continue condition: no exit test taken along the header's paths,
	// each test evaluated on the fresh state after the header instructions
	// before it (headerCondition).
	cond, reason, ok := x.headerCondition(shape, freshState)
	if !ok {
		return nil, reason, false
	}
	ev.cond = cond
	_ = exit
	// One iteration of the body on the fresh state: its paths (a branch
	// inside the body forks on its condition; an inner loop is summarized
	// in place) all reach the back edge and merge register by register
	// into selects on the path conditions.
	x.loopStack = append(x.loopStack, ev.index)
	ends, reason, ok := x.runBody(shape, freshState.clone())
	x.loopStack = x.loopStack[:len(x.loopStack)-1]
	if !ok {
		return nil, reason + " (in a loop body)", false
	}
	for _, name := range ev.vars {
		merged := ends[len(ends)-1].valueOfVar(name, freshState)
		for i := len(ends) - 2; i >= 0; i-- {
			merged = iteTerm(ends[i].cond, ends[i].valueOfVar(name, freshState), merged)
		}
		ev.next[name] = truncate(merged, ev.width[name])
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
	for addr := range scratchSlots {
		delete(freshState.frame, addr)
	}
	freshState.flags = nil
	return freshState, "", true
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
func (x *pathExecutor) headerCondition(shape loopShape, fresh *symbolicState) (*term, string, bool) {
	type headerPath struct {
		pc    int
		cond  *term
		state *symbolicState
	}
	work := []headerPath{{pc: shape.header + 1, cond: constTerm(1, 1), state: fresh.clone()}}
	var cont *term
	paths := 0
	for len(work) > 0 {
		cur := work[len(work)-1]
		work = work[:len(work)-1]
		pc, cond, st := cur.pc, cur.cond, cur.state
		for pc < shape.bodyStart {
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
					return nil, reason, false
				}
				taken = truncate(taken, 1)
				target := x.labels[instr.Operands[len(instr.Operands)-1].(Symbol).Name]
				if target < shape.bodyStart {
					if paths+len(work)+1 > headerPathBudget {
						return nil, "more header paths than the verifier's budget", false
					}
					work = append(work, headerPath{pc: target, cond: binaryTerm("and", cond, taken), state: st.clone()})
				}
				cond = binaryTerm("and", cond, binaryTerm("xor", taken, constTerm(1, 1)))
				pc++
				continue
			}
			var reason string
			var ok bool
			switch {
			case x.arch == ArchRV64:
				reason, ok = x.stepRV64(instr, st)
			case isHeaderLoad(instr):
				reason, ok = x.load(instr, st)
			default:
				reason, ok = step(instr, st)
			}
			if !ok {
				return nil, reason, false
			}
			pc++
		}
		paths++
		if cont == nil {
			cont = cond
		} else {
			cont = binaryTerm("or", cont, cond)
		}
	}
	if cont == nil {
		return constTerm(0, 1), "", true
	}
	return cont, "", true
}

// loopEventBudget bounds the data-dependent loops one body may hold.
const loopEventBudget = 8

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
// `v8.hi`), or an eight-byte frame slot (`s144`).
func (e bodyEnd) valueOfVar(name string, header *symbolicState) *term {
	var reg int
	var side string
	var addr int64
	switch {
	case len(name) > 1 && name[0] == 'r':
		fmt.Sscanf(name, "r%d", &reg)
		return e.valueOf(reg, header)
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
		fmt.Sscanf(name, "s%d", &addr)
		if value, ok := e.state.loadSlot(addr, 8); ok {
			return value
		}
		value, _ := header.loadSlot(addr, 8)
		return value
	}
}

// bodyPathBudget bounds the paths one loop body may fork into.
const bodyPathBudget = 64

// runBody executes a loop body from its first instruction to the back edge
// along every path.
func (x *pathExecutor) runBody(shape loopShape, state *symbolicState) ([]bodyEnd, string, bool) {
	type frontier struct {
		pc    int
		cond  *term
		state *symbolicState
	}
	work := []frontier{{pc: shape.bodyStart, cond: constTerm(1, 1), state: state}}
	var ends []bodyEnd
	for len(work) > 0 {
		cur := work[len(work)-1]
		work = work[:len(work)-1]
		pc, cond, st := cur.pc, cur.cond, cur.state
		for pc < shape.bodyEnd {
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
				pc = x.labels[instr.Operands[0].(Symbol).Name]
				continue
			case "b.", "cbz", "cbnz", "tbz", "tbnz", "beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz", "bnez", "bgez", "bltz", "blez", "bgtz":
				branch, reason, ok := branchCondition(instr, st)
				if !ok {
					return nil, reason, false
				}
				target := x.labels[instr.Operands[len(instr.Operands)-1].(Symbol).Name]
				if branch.kind == termConst {
					if branch.value != 0 {
						pc = target
					} else {
						pc++
					}
					continue
				}
				// An undecided exit of an inner recognized loop: summarize
				// it and continue past its exit, still inside this body.
				if inner, isLoopExit := x.loopExits[pc]; isLoopExit {
					post, reason, ok := x.summarizeLoop(inner, instr, st)
					if !ok {
						return nil, reason, false
					}
					st = post
					pc = inner.exitLabel
					continue
				}
				if isTrapBlock(x.items, target) {
					// The trap arm delivers no result; the body continues on
					// the fall-through path, outside the trapping inputs.
					pc++
					continue
				}
				if len(ends)+len(work) >= bodyPathBudget {
					return nil, "more paths in a loop body than the verifier's budget", false
				}
				taken := truncate(branch, 1)
				notTaken := binaryTerm("xor", taken, constTerm(1, 1))
				work = append(work, frontier{pc: target, cond: binaryTerm("and", cond, taken), state: st.clone()})
				cond = binaryTerm("and", cond, notTaken)
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
				if !isLoad(instr.Mnemonic) {
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
			default:
				if x.arch == ArchRV64 {
					// The RV64 lane: its own semantics; frame memory and
					// stores stay outside a summarized body as on AArch64.
					base := rv64Base(instr)
					if len(base.Operands) == 2 {
						if mem, isMem := base.Operands[1].(Memory); isMem && (mem.Base.Class == ClassSP || rv64Stores[base.Mnemonic] != 0) {
							if mem.Base.Class == ClassSP {
								return nil, "frame memory in a loop body", false
							}
							return nil, "a store in a loop body", false
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
	case termSelect, termFloat:
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

// loopEvent summarizes the Oak `while` whose condition did not fold, then
// leaves the locals at their fresh symbols for the code after the loop.
func (lo *oakLowering) loopEvent(loop *ast.WhileStatement) (string, bool) {
	if lo.concrete != nil {
		return "a loop that a witness run could not decide", false
	}
	if len(lo.loops) >= loopEventBudget {
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
	ev := &loopEvent{index: len(lo.loops) + 1, header: map[string]*term{}, fresh: map[string]*term{}, width: map[string]int{}, next: map[string]*term{}}
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
		local, isLocal := lo.locals[name]
		if !isLocal {
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
		fresh := paramTerm(ev.freshName(name), local.width)
		lo.fresh[fresh.name] = local.width
		ev.fresh[name] = fresh
		local.value = fresh
	}
	cond, reason, ok := lo.lowerCondition(loop.Condition)
	if !ok {
		return reason, false
	}
	ev.cond = truncate(cond, 1)
	lo.loops = append(lo.loops, ev)
	lo.loopStack = append(lo.loopStack, ev.index)
	reason, ok = lo.lowerLoopBody(loop.Body)
	lo.loopStack = lo.loopStack[:len(lo.loopStack)-1]
	if !ok {
		return reason, false
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
		}
	}
}

// loopWitnessInputs are small concrete inputs: under them the loops
// unroll within budget. Scalars and span lengths vary; elements come from
// the fixed memory.
func loopWitnessInputs(fn *Function, sig *ast.FunctionStatement) []map[string]uint64 {
	var names []string
	for _, param := range sig.Parameters {
		if _, _, isSpan := spanShape(param.Type); isSpan {
			names = append(names, spanLenName(param.Name.Value))
			continue
		}
		if comp, isComposite := fn.Composites[typeText(param.Type)]; isComposite && len(comp.Fields) > 0 {
			continue // its leaves are appended below
		}
		names = append(names, param.Name.Value)
	}
	names = append(names, compositeParamLeaves(fn, sig)...)
	// The larger values clear the bounds checks of a body that reads a
	// table of several 16-byte vectors before its loops (a UTF-8 kernel
	// reads 64 bytes of tables): under the small ones alone every input
	// traps there and no witness decides anything.
	small := []uint64{0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 33, 63, 64, 65, 80, 81}
	var inputs []map[string]uint64
	if len(names) == 0 {
		return []map[string]uint64{{}}
	}
	for _, a := range small {
		if len(names) == 1 {
			inputs = append(inputs, map[string]uint64{names[0]: a})
			continue
		}
		for _, b := range small {
			env := map[string]uint64{names[0]: a, names[1]: b}
			for i, extra := range names[2:] {
				env[extra] = (a*7 + b*3 + uint64(i)) % 19
			}
			inputs = append(inputs, env)
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
	show  string
	ext   string // "" (same width), "zext" or "sext": a 64-bit register carrying a widened 32-bit variable
}

// widen applies a coupling's widening to a 32-bit term.
func widen(t *term, ext string) *term {
	switch ext {
	case "zext":
		return zeroExtend(t, 64)
	case "sext":
		return extendTerm(zeroExtend(t, 64), 32, 64, true)
	}
	return t
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
		return trusted("the asm body has a data-dependent loop but the Oak body does not")
	case len(asmLoops) != len(oakLoops):
		return trusted(fmt.Sprintf("the asm body has %d data-dependent loops, the Oak body %d", len(asmLoops), len(oakLoops)))
	}
	for k := range asmLoops {
		if asmLoops[k].parent != oakLoops[k].parent {
			return trusted("the data-dependent loops nest differently on the two sides")
		}
	}
	// Witnesses: concrete inputs decide every loop.
	checked := 0
	for _, env := range loopWitnessInputs(fn, sig) {
		if !lowering.inDomain(env) {
			continue // a union tag outside its variants: not a well-typed input
		}
		asmValue, _, reasonA, okA := executeBodyChunk(fn, sig, env, 0, exec.resultChunk)
		concrete := prepareLowering(fn, sig, env)
		concrete.resultChunk = exec.resultChunk
		oakValue, _, reasonO, okO := concrete.resultTerm(fn, sig, oakBody)
		if os.Getenv("OAK_VERIFY_TRACE") != "" {
			fmt.Fprintf(os.Stderr, "witness %s %v: asm ok=%v %q trap=%v; oak ok=%v %q\n", fn.Name, env, okA, reasonA, asmValue == trapPath, okO, reasonO)
		}
		if !okA || !okO || asmValue == trapPath {
			// Beyond the unrolling budget on this input, or an input on
			// which the body traps (an element read past a length the
			// input set to zero): no value to compare on either side.
			continue
		}
		got, want := truncate(maskResult(fn, sig, asmValue, exec.resultChunk), width).eval(env), oakValue.eval(env)
		if got != want {
			names := make([]string, 0, len(env))
			for name := range env {
				names = append(names, name)
			}
			sort.Strings(names)
			return Verdict{Kind: VerdictMismatch, Message: fmt.Sprintf("asm unit %s disagrees with its Oak body at %s (fixed element contents): asm yields %d, Oak yields %d", fn.Name, describeEnv(names, env), got, want)}
		}
		checked++
	}
	if checked == 0 {
		return trusted("no concrete input decided the loops within budget")
	}
	evidence := func(reason string) Verdict {
		return Verdict{Kind: VerdictWitnessed, Message: fmt.Sprintf("asm unit %s: agrees with its Oak body on %d concrete inputs (evidence, not proof: %s)", fn.Name, checked, reason)}
	}
	widthOfName := func(name string) int {
		var k int
		var reg string
		if n, _ := fmt.Sscanf(name, "loop%d.%s", &k, &reg); n == 2 && strings.HasPrefix(reg, "r") && k >= 1 && k <= len(asmLoops) {
			if w, isReg := asmLoops[k-1].width[reg]; isReg {
				return w
			}
		}
		return lowering.declaredWidth(name)
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
	type slot struct {
		event int
		local string
	}
	var slots []slot
	for k, ev := range oakLoops {
		for _, local := range ev.vars {
			slots = append(slots, slot{event: k, local: local})
		}
	}
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
		holds, decidedEntry := impliesEqual(constTerm(1, 1), substitute(inv, atHeader), constTerm(1, 1), widthOfName)
		preserved, decidedStep := impliesEqual(binaryTerm("and", truncate(inv, 1), truncate(guard, 1)), substitute(inv, afterBody), constTerm(1, 1), widthOfName)
		if decidedEntry && holds && decidedStep && preserved {
			invariants[k] = truncate(inv, 1)
		}
	}
	children := map[int][]int{}
	for k, ev := range oakLoops {
		children[ev.parent-1] = append(children[ev.parent-1], k)
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
		for at := oakLoops[k].parent - 1; at >= 0; at = oakLoops[at].parent - 1 {
			premise = binaryTerm("and", premise, binaryTerm("and", substitute(invariants[at], sigma), truncate(substitute(oakLoops[at].cond, sigma), 1)))
		}
		for _, child := range children[k] {
			premise = binaryTerm("and", premise, exitPremise(child, sigma))
		}
		return premise
	}
	chosen := map[slot]coupling{}
	used := map[string]bool{} // asm fresh symbol names already paired
	sigma := map[string]*term{}
	var failure string
	candidatesFor := func(s slot) []coupling {
		oakEv, asmEv := oakLoops[s.event], asmLoops[s.event]
		hx := oakEv.header[s.local]
		var out []coupling
		for _, reg := range asmEv.vars {
			if used[asmEv.freshName(reg)] {
				continue
			}
			// A 64-bit register may carry a 32-bit Oak variable widened (the
			// RV64 lane has no 32-bit register view): zero-extended by a
			// 64-bit increment kept below 2^32 by the loop's premise, or
			// sign-extended by the W-forms (addw, Oak.RiscV.addw_eq). Each
			// widening is a candidate image; the coupling is r = ext(x) + b at
			// 64 bits and one iteration must preserve it.
			var widenings []string
			switch {
			case asmEv.width[reg] == oakEv.width[s.local]:
				widenings = []string{""}
			case asmEv.width[reg] == 64 && oakEv.width[s.local] == 32:
				widenings = []string{"zext", "sext"}
			default:
				continue
			}
			for _, ext := range widenings {
				hx := widen(hx, ext)
				hr := substitute(asmEv.header[reg], sigma)
				for _, a := range []int{1, -1} {
					var b *term
					if a == 1 {
						b = binaryTerm("sub", hr, hx)
					} else {
						b = binaryTerm("add", hr, hx)
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
					show := s.local + "↔" + reg
					switch {
					case a == 1 && b.kind == termConst && b.value == 0:
					case a == 1:
						show = fmt.Sprintf("%s = %s + %s", reg, s.local, b)
					default:
						show = fmt.Sprintf("%s = %s - %s", reg, b, s.local)
					}
					out = append(out, coupling{event: s.event, local: s.local, reg: reg, a: a, b: b, show: show, ext: ext})
				}
			}
		}
		return out
	}
	trace := os.Getenv("OAK_VERIFY_TRACE") != ""
	var search func(i int) bool
	search = func(i int) bool {
		if i == len(slots) {
			for k := range oakLoops {
				oakEv, asmEv := oakLoops[k], asmLoops[k]
				if equal, decided := impliesEqual(bodyPremise(k, sigma, false), substitute(oakEv.cond, sigma), substitute(asmEv.cond, sigma), widthOfName); !decided || !equal {
					failure = fmt.Sprintf("loop %d's continue conditions were not proven equal", k+1)
					if trace {
						fmt.Fprintf(os.Stderr, "verify %s: %s (decided=%v)\n  oak: %s\n  asm: %s\n  premise: %s\n", fn.Name, failure, decided, substitute(oakEv.cond, sigma), substitute(asmEv.cond, sigma), bodyPremise(k, sigma, false))
					}
					return false
				}
				premise := bodyPremise(k, sigma, true)
				for _, local := range oakEv.vars {
					c := chosen[slot{event: k, local: local}]
					// r' = a*x' + b must hold after one iteration.
					next := substitute(oakEv.next[local], sigma)
					next = widen(next, c.ext)
					if c.a == 1 {
						next = binaryTerm("add", next, c.b)
					} else {
						next = binaryTerm("sub", c.b, next)
					}
					if equal, decided := impliesEqual(premise, next, substitute(asmEv.next[c.reg], sigma), widthOfName); !decided || !equal {
						failure = fmt.Sprintf("one iteration of loop %d was not proven to preserve %s", k+1, c.show)
						if trace {
							fmt.Fprintf(os.Stderr, "verify %s: %s (decided=%v)\n  oak next: %s\n  asm next: %s\n", fn.Name, failure, decided, next, substitute(asmEv.next[c.reg], sigma))
						}
						return false
					}
				}
			}
			return true
		}
		s := slots[i]
		for _, c := range candidatesFor(s) {
			asmName := asmLoops[s.event].freshName(c.reg)
			used[asmName] = true
			chosen[s] = c
			// r = a*x + b: the register's fresh symbol expressed for x.
			x := paramTerm(oakLoops[s.event].freshName(s.local), oakLoops[s.event].width[s.local])
			x = widen(x, c.ext)
			if c.a == 1 {
				sigma[asmName] = binaryTerm("add", x, c.b)
			} else {
				sigma[asmName] = binaryTerm("sub", c.b, x)
			}
			if search(i + 1) {
				return true
			}
			delete(used, asmName)
			delete(chosen, s)
			delete(sigma, asmName)
		}
		if failure == "" {
			failure = fmt.Sprintf("no register is an affine image of the loop variable %s of loop %d at its header", s.local, s.event+1)
		}
		return false
	}
	if !search(0) {
		return evidence(failure)
	}
	var pairs []string
	for _, s := range slots {
		pairs = append(pairs, chosen[s].show)
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
		if n, _ := fmt.Sscanf(name, "loop%d.%s", &k, &reg); n == 2 && strings.HasPrefix(reg, "r") && sigma[name] == nil {
			return evidence(fmt.Sprintf("the result reads loop-carried register %s of loop %d, which no Oak variable is coupled to", reg, k))
		}
	}
	premise := constTerm(1, 1)
	for k, ev := range oakLoops {
		if ev.parent == 0 {
			premise = binaryTerm("and", premise, exitPremise(k, sigma))
		}
	}
	equal, decided := impliesEqual(premise, oakTerm, substitute(truncate(asmTerm, width), sigma), widthOfName)
	if !decided || !equal {
		return evidence("the results after the loops were not proven equal")
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
		loopsNote = fmt.Sprintf("%d nested data-dependent loops coupled inductively", len(oakLoops))
	}
	return Verdict{Kind: VerdictProven, Message: fmt.Sprintf("asm unit %s: proven equal to its Oak body at the bit level — %s (%s)%s, %d concrete inputs agree", fn.Name, loopsNote, strings.Join(pairs, ", "), invariantNote, checked)}
}

// substitute replaces parameters by terms (the asm loop symbols by their
// expression in the Oak variables' symbols).
func substitute(t *term, sigma map[string]*term) *term {
	return substituteMemo(t, sigma, map[*term]*term{})
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
	out := *t
	out.cond = substituteMemo(t.cond, sigma, memo)
	out.left = substituteMemo(t.left, sigma, memo)
	out.right = substituteMemo(t.right, sigma, memo)
	memo[t] = &out
	return &out
}

// impliesEqual decides premise → (a = b) at the terms' common width by
// bit-blasting; decided is false past the node budget.
func impliesEqual(premise, a, b *term, widthOf func(string) int) (holds bool, decided bool) {
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
	bl := newBlaster(names, widths)
	pBits := bl.blast(premise)
	aBits, bBits := bl.blast(a), bl.blast(b)
	if pBits == nil || aBits == nil || bBits == nil || bl.bdd.exceeded {
		return false, false
	}
	allEqual := bddTrue
	for i := 0; i < width; i++ {
		allEqual = bl.bdd.apply(opAnd, allEqual, bl.bdd.not(bl.bdd.apply(opXor, aBits[i], bBits[i])))
	}
	implication := bl.bdd.apply(opOr, bl.bdd.not(pBits[0]), allEqual)
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
	if bl.bdd.exceeded {
		return false, false
	}
	return implication == bddTrue, true
}
