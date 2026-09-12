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
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// loopShape is a recognized asm loop: a header label, an exit test (`cmp`
// then `b.cond`, or a compare-and-branch), a body branching only forward
// within itself (or through recognized inner loops), and an unconditional
// back edge.
type loopShape struct {
	header, cmp, exit, exitLabel int // cmp is -1 for a compare-and-branch exit
	bodyStart, bodyEnd           int // body instructions are items [bodyStart, bodyEnd)
}

// findLoops recognizes loops by their back edges, keyed by the exit branch.
// Back edges are met in item order, so an inner loop is recognized before
// the outer body containing it is examined.
func findLoops(items []Item, labels map[string]int) map[int]loopShape {
	loops := map[int]loopShape{}
	innerHeaders := map[int]int{} // header index -> back edge index of a recognized loop
	for back, item := range items {
		branch, isBranch := item.(Instruction)
		if !isBranch || branch.Mnemonic != "b" {
			continue
		}
		header, ok := labels[branch.Operands[0].(Symbol).Name]
		if !ok || header >= back || header+2 >= back {
			continue
		}
		// The exit test: `cmp` then `b.cond`, or a compare-and-branch
		// (cbz/cbnz/tbz/tbnz) on its own.
		cmpIndex, exitIndex := -1, header+1
		if first, isInstr := items[header+1].(Instruction); isInstr && first.Mnemonic == "cmp" {
			cmpIndex, exitIndex = header+1, header+2
		}
		if exitIndex >= back {
			continue
		}
		exit, isExit := items[exitIndex].(Instruction)
		if !isExit || !isConditionalBranch(exit.Mnemonic) {
			continue
		}
		exitLabel, ok := labels[exit.Operands[len(exit.Operands)-1].(Symbol).Name]
		if !ok || exitLabel <= back {
			continue
		}
		wellFormed := true
		for i := exitIndex + 1; i < back; i++ {
			instr, isInstr := items[i].(Instruction)
			if !isInstr {
				continue // an inner label
			}
			switch instr.Mnemonic {
			case "bl", "ret", "eret":
				wellFormed = false
			case "b", "b.", "cbz", "cbnz", "tbz", "tbnz":
				target, ok := labels[instr.Operands[len(instr.Operands)-1].(Symbol).Name]
				if !ok || target >= back {
					// A guard's branch to the trap block is not an exit: the
					// path it takes delivers no result (docs/spec/94-assembler.md §8).
					if !ok || !isTrapBlock(items, target) || instr.Mnemonic == "b" {
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
		loops[exitIndex] = loopShape{header: header, cmp: cmpIndex, exit: exitIndex, exitLabel: exitLabel, bodyStart: exitIndex + 1, bodyEnd: back}
		innerHeaders[header] = back
	}
	return loops
}

// isTrapBlock reports a label whose first instruction is `brk`: the trap
// a bounds guard, a zero divisor, or a failed assert branches to.
func isTrapBlock(items []Item, index int) bool {
	for i := index; i < len(items); i++ {
		if instr, isInstr := items[i].(Instruction); isInstr {
			return instr.Mnemonic == "brk"
		}
	}
	return false
}

func isConditionalBranch(mnemonic string) bool {
	switch mnemonic {
	case "b.", "cbz", "cbnz", "tbz", "tbnz":
		return true
	}
	return false
}

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
	for i := shape.bodyStart; i < shape.bodyEnd; i++ {
		instr, isInstr := x.items[i].(Instruction)
		if !isInstr || instr.Mnemonic == "cmp" || instr.Mnemonic == "tst" || isConditionalBranch(instr.Mnemonic) || instr.Mnemonic == "b" || isStoreMnemonic(instr.Mnemonic) || len(instr.Operands) == 0 {
			continue // no register written: compares, branches, stores
		}
		dest, isReg := instr.Operands[0].(Register)
		if !isReg || dest.ZeroRegister() {
			continue
		}
		if !written[dest.Num] {
			allW[dest.Num] = true
		}
		written[dest.Num] = true
		if dest.Class != ClassW {
			allW[dest.Num] = false
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
	for _, reg := range regs {
		name := fmt.Sprintf("r%d", reg)
		width := 64
		if allW[reg] {
			width = 32
		}
		fresh := paramTerm(ev.freshName(name), width)
		value, bound := state.regs[reg]
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
	// The continue condition: the exit test on the fresh state, negated.
	condState := freshState.clone()
	if shape.cmp >= 0 {
		if reason, ok := step(x.items[shape.cmp].(Instruction), condState); !ok {
			return nil, reason, false
		}
	}
	exitCond, reason, ok := branchCondition(exit, condState)
	if !ok {
		return nil, reason, false
	}
	ev.cond = binaryTerm("xor", truncate(exitCond, 1), constTerm(1, 1))
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
		var reg int
		fmt.Sscanf(name, "r%d", &reg)
		merged := ends[len(ends)-1].valueOf(reg, freshState)
		for i := len(ends) - 2; i >= 0; i-- {
			merged = iteTerm(ends[i].cond, ends[i].valueOf(reg, freshState), merged)
		}
		ev.next[name] = truncate(merged, ev.width[name])
	}
	for reg := range scratch {
		delete(freshState.regs, reg)
	}
	freshState.flags = nil
	return freshState, "", true
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
			case "b":
				pc = x.labels[instr.Operands[0].(Symbol).Name]
				continue
			case "b.", "cbz", "cbnz", "tbz", "tbnz":
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
					return nil, "frame memory in a loop body", false
				}
				if !isLoad(instr.Mnemonic) {
					return nil, "a store in a loop body", false
				}
				if reason, ok := x.load(instr, st); !ok {
					return nil, reason, false
				}
			default:
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
	case termSelect:
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
	if lo.hasAggregates() {
		return "an aggregate local across a data-dependent loop", false
	}
	// The loop-carried locals are those the body assigns and that exist
	// before the loop; a local declared inside the body is the body's own.
	assigned := map[string]bool{}
	assignedLocals(loop.Body, assigned)
	declared := map[string]bool{}
	declaredLocals(loop.Body, declared)
	ev := &loopEvent{index: len(lo.loops) + 1, header: map[string]*term{}, fresh: map[string]*term{}, width: map[string]int{}, next: map[string]*term{}}
	if n := len(lo.loopStack); n > 0 {
		ev.parent = lo.loopStack[n-1]
	}
	for name := range assigned {
		if !declared[name] {
			ev.vars = append(ev.vars, name)
		}
	}
	sort.Strings(ev.vars)
	for _, name := range ev.vars {
		local, isLocal := lo.locals[name]
		if !isLocal {
			return fmt.Sprintf("an assignment to %s (not a local)", name), false
		}
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
		ev.next[name] = lo.locals[name].value
		lo.locals[name].value = ev.fresh[name]
	}
	return "", true
}

func assignedLocals(body *ast.BlockStatement, into map[string]bool) {
	if body == nil {
		return
	}
	for _, stmt := range body.Statements {
		switch s := stmt.(type) {
		case *ast.AssignmentStatement:
			into[s.Name.Value] = true
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
	small := []uint64{0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 33}
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
		asmValue, _, _, okA := executeBody(fn, sig, env)
		concrete := prepareLowering(fn, sig, env)
		oakValue, _, _, okO := concrete.resultTerm(fn, sig, oakBody)
		if !okA || !okO {
			continue // beyond the unrolling budget on this input
		}
		got, want := truncate(maskResult(fn, sig, asmValue), width).eval(env), oakValue.eval(env)
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
			if asmEv.width[reg] != oakEv.width[s.local] || used[asmEv.freshName(reg)] {
				continue
			}
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
				out = append(out, coupling{event: s.event, local: s.local, reg: reg, a: a, b: b, show: show})
			}
		}
		return out
	}
	var search func(i int) bool
	search = func(i int) bool {
		if i == len(slots) {
			for k := range oakLoops {
				oakEv, asmEv := oakLoops[k], asmLoops[k]
				if equal, decided := impliesEqual(bodyPremise(k, sigma, false), substitute(oakEv.cond, sigma), substitute(asmEv.cond, sigma), widthOfName); !decided || !equal {
					failure = fmt.Sprintf("loop %d's continue conditions were not proven equal", k+1)
					return false
				}
				premise := bodyPremise(k, sigma, true)
				for _, local := range oakEv.vars {
					c := chosen[slot{event: k, local: local}]
					// r' = a*x' + b must hold after one iteration.
					next := substitute(oakEv.next[local], sigma)
					if c.a == 1 {
						next = binaryTerm("add", next, c.b)
					} else {
						next = binaryTerm("sub", c.b, next)
					}
					if equal, decided := impliesEqual(premise, next, substitute(asmEv.next[c.reg], sigma), widthOfName); !decided || !equal {
						failure = fmt.Sprintf("one iteration of loop %d was not proven to preserve %s", k+1, c.show)
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
	return implication == bddTrue, true
}
