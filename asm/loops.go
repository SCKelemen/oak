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
		return isSym && callees[sym.Name] != nil
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
	// entry: each marked span's write log at the loop's entry, over the
	// span's entry memory — what the marker replaced. The coupling proof
	// requires the two sides' entry memories equal (the induction's base;
	// without it a store before the loop that differs between the sides
	// would vanish under the markers).
	entry map[string][]*spanWrite
}

func (ev *loopEvent) freshName(v string) string { return fmt.Sprintf("loop%d.%s", ev.index, v) }

// loopEvent summarizes the top-level asm loop whose exit branch was just
// reached with an undecided condition, then continues past the exit.
func (x *pathExecutor) loopEvent(shape loopShape, exit Instruction, state *symbolicState) (*term, *pathEffects, string, bool) {
	post, reason, ok := x.summarizeLoop(shape, exit, state)
	if !ok {
		return nil, nil, reason, false
	}
	// The effects are the run's past the exit: the loop's memory markers
	// and what the code after the loop stores.
	return x.run(shape.exitLabel, post)
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
	// The continue condition: no exit test taken along the header's paths,
	// each test evaluated on the fresh state after the header instructions
	// before it (headerCondition).
	cond, reason, ok := x.headerCondition(shape, freshState)
	if !ok {
		return nil, reason, false
	}
	ev.cond = cond
	_ = exit
	// The writable span parameters (`[*]T`, the only spans a body can
	// store through) take the loop's memory marker before the iteration
	// runs, so the body's reads see the iteration's unknown memory and its
	// stores layer on it; the Oak side marks the same parameters from the
	// same signature (loopEvent).
	storedSpans := map[string]bool{}
	writtenSpans := writableSpanParams(x.fn, x.spans)
	for _, span := range writtenSpans {
		storedSpans[span] = true
	}
	ev.entry = map[string][]*spanWrite{}
	for _, span := range writtenSpans {
		ev.entry[span] = freshState.writes[span]
		freshState.writes = appendMarker(freshState.writes, span, ev.index)
	}
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
	// The iteration's stores, each path's under its condition, in path
	// order; the state past the loop keeps the marker alone (the loop's
	// memory is the iteration's unknown memory, which the coupling proof
	// identifies with the Oak side's).
	for _, span := range writtenSpans {
		before := len(freshState.writes[span])
		var stores []*spanWrite
		for _, end := range ends {
			log := end.state.writes[span]
			if len(log) > before {
				stores = append(stores, guardWrites(log[before:], end.cond)...)
			}
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
	for reg := range scratchF {
		delete(freshState.fregs, reg)
	}
	for addr := range scratchSlots {
		delete(freshState.frame, addr)
	}
	freshState.flags = nil
	return freshState, "", true
}

// writableSpanParams names the function's writable span parameters
// (`[*]T`) that the executor knows as spans, sorted: the spans a loop's
// body may store through, which take the loop's memory marker.
func writableSpanParams(fn *Function, spans map[string]int64) []string {
	var out []string
	if fn == nil || fn.Signature == nil {
		return out
	}
	for _, param := range fn.Signature.Parameters {
		if param == nil || param.Name == nil || !isWritableSpan(param.Type) {
			continue
		}
		if _, known := spans[param.Name.Value]; known {
			out = append(out, param.Name.Value)
		}
	}
	sort.Strings(out)
	return out
}

// summarizeCallInLoop is summarizeCall inside a loop's header or body: the
// callee's result is a term over the iteration's fresh symbols; a callee
// with memory effects (stores through spans, package cells) is refused,
// since the loop summary carries registers and frame slots, not memories.
func (x *pathExecutor) summarizeCallInLoop(instr Instruction, st *symbolicState) (string, bool) {
	cellsBefore := len(st.globals)
	reason, ok := x.summarizeCall(instr, st)
	if !ok {
		return reason, false
	}
	// A callee's stores through the caller's spans join the iteration's
	// write log (the loop's memory); a callee writing package cells is
	// refused, since the loop summary carries no cells.
	if len(st.globals) != cellsBefore {
		return "a call writing package state in a loop", false
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
					// the fall-through path, outside the trapping inputs —
					// under the index bound the guard establishes.
					st.noteTrapGuard(instr)
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
			case "bl", "call":
				// A program function in the body: summarized on the path's
				// state, its result a term over the fresh symbols.
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
				if !isLoad(instr.Mnemonic) {
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
			if _, isSpan := lo.spans[name]; isSpan {
				continue // a store through a span: the loop's memory, below
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
	storedSpans := make([]string, 0, len(lo.writableSpans))
	for span := range lo.writableSpans {
		if _, isSpan := lo.spans[span]; isSpan {
			storedSpans = append(storedSpans, span)
		}
	}
	sort.Strings(storedSpans)
	before := map[string]int{}
	ev.entry = map[string][]*spanWrite{}
	for _, span := range storedSpans {
		ev.entry[span] = lo.writes[span]
		lo.writes = appendMarker(lo.writes, span, ev.index)
		lo.spans[loopMemoryName(ev.index, span)] = lo.spans[span] // the unknown memory's element width
		before[span] = len(lo.writes[span])
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
	// The iteration's stores, for the coupling proof; past the loop the
	// span's contents are the marker's unknown memory.
	for _, span := range storedSpans {
		log := lo.writes[span]
		if ev.writes == nil {
			ev.writes = map[string][]*spanWrite{}
		}
		ev.writes[span] = append([]*spanWrite{}, log[before[span]:]...)
		lo.writes[span] = log[:before[span]:before[span]]
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
		return trusted("the asm body has a data-dependent loop but the Oak body does not")
	case len(asmLoops) != len(oakLoops):
		return trusted(fmt.Sprintf("the asm body has %d data-dependent loops, the Oak body %d", len(asmLoops), len(oakLoops)))
	}
	for k := range asmLoops {
		if asmLoops[k].parent != oakLoops[k].parent {
			return trusted("the data-dependent loops nest differently on the two sides")
		}
	}
	// Witnesses: concrete inputs decide every loop. A unit function (no
	// result term: the span memories are the comparison) has none here;
	// its proof is the coupling alone.
	checked := 0
	for _, env := range loopWitnessInputs(fn, sig) {
		if !lowering.inDomain(env) {
			continue // a union tag outside its variants: not a well-typed input
		}
		asmValue, asmRun, reasonA, okA := executeBodyChunk(fn, sig, env, 0, exec.resultChunk)
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
		if os.Getenv("OAK_VERIFY_TRACE") != "" {
			fmt.Fprintf(os.Stderr, "witness %s %v: asm ok=%v %q trap=%v; oak ok=%v %q\n", fn.Name, env, okA, reasonA, asmValue == trapPath, okO, reasonO)
		}
		if !okA || !okO || asmValue == trapPath {
			// Beyond the unrolling budget on this input, or an input on
			// which the body traps (an element read past a length the
			// input set to zero): no value to compare on either side.
			continue
		}
		names := make([]string, 0, len(env))
		for name := range env {
			names = append(names, name)
		}
		sort.Strings(names)
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
		checked++
	}
	if checked == 0 && asmTerm != nil {
		return trusted("no concrete input decided the loops within budget")
	}
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
	// Every implication of this proof spends from one budget.
	budget := &nodeBudget{remaining: loopProofNodeBudget}
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
			if strings.HasPrefix(reg, "f") && !oakEv.floats[s.name] {
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
			case len(s.locals) == 1 && oakEv.floats[s.name] && asmEv.width[reg] == 64 && s.width() == 32 && (strings.HasPrefix(reg, "v") || strings.HasPrefix(reg, "f")):
				// An f32 local in the low lane of a v register (a scalar
				// write zeroes the rest) or in an RV64 f register (the file's
				// low-bits convention): zero-extended only.
				widenings = []string{"zext"}
			default:
				continue
			}
			if len(s.locals) > 1 {
				signs = []int{1}
			}
			for _, ext := range widenings {
				hx := widen(hx, ext, asmEv.width[reg])
				hr := substitute(asmEv.header[reg], sigma)
				for _, a := range signs {
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
					out = append(out, coupling{event: s.event, local: s.name, reg: reg, a: a, b: b, ext: ext})
				}
			}
		}
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
					fmt.Fprintf(os.Stderr, "verify %s: a valuation refutes one iteration preserving %s\n", fn.Name, c.show())
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
					fmt.Fprintf(os.Stderr, "verify %s: a valuation refutes loop %d's continue conditions agreeing\n", fn.Name, k+1)
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
		if visited > couplingSearchBudget {
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
			if visited > couplingSearchBudget {
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
		if reason, ok := coupledEntryMemories(k, oakEv, asmEv, sigma, entryPremise, lowering, implies); !ok {
			return evidence(reason)
		}
		if reason, ok := coupledWrites(k, oakEv, asmEv, sigma, bodyPremise(k, sigma, true), lowering, implies); !ok {
			// The stores did not pair one for one; the memories they leave
			// may still be one memory (stores in another order, a guarded
			// store against a split path): the iteration's memories are
			// compared whole at a fresh index.
			if memReason, memOk := coupledIterationMemories(k, oakEv, asmEv, sigma, bodyPremise(k, sigma, true), lowering, implies); !memOk {
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
	for k, ev := range oakLoops {
		if ev.parent == 0 {
			premise = binaryTerm("and", premise, exitPremise(k, sigma))
		}
	}
	if asmTerm != nil {
		equal, decided := implies(premise, oakTerm, substitute(truncate(asmTerm, width), sigma))
		if !decided || !equal {
			if trace {
				fmt.Fprintf(os.Stderr, "verify %s: results not proven equal (decided=%v)\n  oak: %s\n  asm: %s\n  premise: %s\n", fn.Name, decided, oakTerm, substitute(truncate(asmTerm, width), sigma), premise)
			}
			return evidence("the results after the loops were not proven equal")
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
		contract, isSpan := lowering.spans[name]
		if !isSpan {
			return trusted(fmt.Sprintf("a store through %s, which the Oak signature does not declare as a span", name))
		}
		elemWidth := contract.elemWidth
		lowering.fresh[spanIndexName(name)] = 32
		at := paramTerm(spanIndexName(name), 32)
		entry := selectTerm(name, at, elemWidth)
		asmMemory := substitute(memoryAt(exec.writes[name], at, entry), sigma)
		oakMemory := memoryAt(lowering.writes[name], at, entry)
		if equal, decided := implies(premise, oakMemory, asmMemory); !decided || !equal {
			if trace {
				fmt.Fprintf(os.Stderr, "verify %s: span %s after the loops (decided=%v)\n  oak: %s\n  asm: %s\n", fn.Name, name, decided, oakMemory, asmMemory)
			}
			return evidence(fmt.Sprintf("the memory of the span %s after the loops was not proven equal", name))
		}
	}
	memoryNote := ""
	if len(writtenSpans) > 0 {
		memoryNote = " and the span memory it writes (" + strings.Join(writtenSpans, ", ") + ")"
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
		contract := lowering.spans[span]
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
				if equal, decided := implies(premise, truncate(o.value, contract.elemWidth), substitute(truncate(a.value, contract.elemWidth), sigma)); !decided || !equal {
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
func coupledEntryMemories(k int, oakEv, asmEv *loopEvent, sigma map[string]*term, premise *term, lowering *oakLowering, implies func(premise, a, b *term) (bool, bool)) (string, bool) {
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
		contract, isSpan := lowering.spans[span]
		if !isSpan {
			return fmt.Sprintf("loop %d marks %s, which the signature does not declare as a span", k+1, span), false
		}
		lowering.fresh[spanIndexName(span)] = 32
		at := paramTerm(spanIndexName(span), 32)
		entry := selectTerm(span, at, contract.elemWidth)
		oakMemory := memoryAt(oakLog, at, entry)
		asmMemory := substitute(memoryAt(asmLog, at, entry), sigma)
		if equal, decided := implies(premise, oakMemory, asmMemory); !decided || !equal {
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
func coupledIterationMemories(k int, oakEv, asmEv *loopEvent, sigma map[string]*term, premise *term, lowering *oakLowering, implies func(premise, a, b *term) (bool, bool)) (string, bool) {
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
		contract, isSpan := lowering.spans[span]
		if !isSpan {
			return fmt.Sprintf("loop %d stores through %s, which the signature does not declare as a span", k+1, span), false
		}
		lowering.fresh[spanIndexName(span)] = 32
		at := paramTerm(spanIndexName(span), 32)
		unknown := selectTerm(loopMemoryName(oakEv.index, span), at, contract.elemWidth)
		oakMemory := memoryAt(oakEv.writes[span], at, unknown)
		asmMemory := substitute(memoryAt(asmEv.writes[span], at, unknown), sigma)
		if equal, decided := implies(premise, oakMemory, asmMemory); !decided || !equal {
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
		contract, isSpan := lowering.spans[name]
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
			entry := constTerm(elementValue(name, k, contract.elemWidth), contract.elemWidth)
			a := memoryAt(asmLogs[name], at, entry).eval(env)
			o := memoryAt(oakLogs[name], at, entry).eval(env)
			if a != o {
				return name, k, a, o, true
			}
		}
	}
	return "", 0, 0, 0, false
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
	memo[t] = &out
	return &out
}

// loopTermNodeBudget bounds the distinct nodes of the loop events' terms
// (headers, conditions, next values, stores) the coupling search works
// over.
const loopTermNodeBudget = 100000

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
// than running for minutes.
type nodeBudget struct{ remaining int }

// loopProofNodeBudget bounds one loop proof's diagram nodes in all;
// loopDecisionNodeBudget bounds each of its implications.
const (
	loopProofNodeBudget    = 8 * blastNodeBudget
	loopDecisionNodeBudget = blastNodeBudget
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
	width := a.width
	if b.width > width {
		width = b.width
	}
	a, b = adaptWidth(a, width), adaptWidth(b, width)
	if equalTerms(a, b) {
		return true, true // the same term on both sides: no diagram needed
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
	if refutedByValuation(premise, a, b, names, widths) {
		return false, true
	}
	blasters := equalityBlasters(names, widths, a, b)
	var stop atomic.Bool
	type attempt struct{ holds, decided bool }
	results := make(chan attempt, len(blasters))
	for _, bl := range blasters {
		bl.bdd.stop = &stop
		go func(bl *blaster) {
			holds, decided := impliesEqualUnder(bl, premise, a, b, width)
			results <- attempt{holds, decided}
		}(bl)
	}
	for range blasters {
		if r := <-results; r.decided {
			stop.Store(true)
			return r.holds, true
		}
	}
	return false, false
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

// impliesEqualUnder is impliesEqual's bit-level decision under one
// variable order.
func impliesEqualUnder(bl *blaster, premise, a, b *term, width int) (holds bool, decided bool) {
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
	for _, target := range targets {
		for _, delta := range []uint64{0, 1, ^uint64(0)} {
			env := map[string]uint64{}
			for _, name := range free {
				env[name] = random() & mask(widths[name])
			}
			env[target.name] = (target.value + delta) & mask(widths[target.name])
			if premise.eval(env) != 0 && a.eval(env) != b.eval(env) {
				return true
			}
		}
	}
	for round := 0; round < couplingValuations; round++ {
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
		if premise.eval(env) == 0 {
			continue
		}
		if a.eval(env) != b.eval(env) {
			return true
		}
	}
	return false
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
const couplingSearchBudget = 4096
