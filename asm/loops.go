package asm

// Data-dependent loops (docs/spec/94-assembler.md §8, sixth increment).
//
// A loop whose trip count depends on the inputs cannot be unrolled into a
// term. Both executors instead summarize it as a LOOP EVENT — the values
// of the loop-carried variables at the header, fresh symbols standing for
// them on an arbitrary iteration, the continue condition over those
// symbols, and their values after one iteration — and continue past the
// loop on the fresh symbols (the exit sees the header values of the
// exiting iteration). Verification then has two layers:
//
//   - WITNESSES: both sides are re-executed on concrete inputs, under which
//     the loops become counted and unroll; a disagreement is a definite
//     mismatch with a concrete input.
//   - COUPLING (Oak.AssemblerSemantics.whileFuel_coupled): each Oak local
//     is paired with a register whose header value is bit-level equal; the
//     continue conditions must agree and one iteration must preserve every
//     pairing; then the results after the loops are compared as usual. This
//     is the inductive proof, so the verdict is proven.

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// loopShape is a recognized asm loop: a header label, `cmp` then the exit
// `b.cond`, a straight-line body, and an unconditional back edge.
type loopShape struct {
	header, cmp, exit, exitLabel int
	bodyStart, bodyEnd           int // body instructions are items [bodyStart, bodyEnd)
}

// findLoops recognizes loops by their back edges, keyed by the exit branch.
func findLoops(items []Item, labels map[string]int) map[int]loopShape {
	loops := map[int]loopShape{}
	for back, item := range items {
		branch, isBranch := item.(Instruction)
		if !isBranch || branch.Mnemonic != "b" {
			continue
		}
		header, ok := labels[branch.Operands[0].(Symbol).Name]
		if !ok || header >= back || header+2 >= back {
			continue
		}
		cmp, isCmp := items[header+1].(Instruction)
		exit, isExit := items[header+2].(Instruction)
		if !isCmp || cmp.Mnemonic != "cmp" || !isExit || exit.Mnemonic != "b." {
			continue
		}
		exitLabel, ok := labels[exit.Operands[0].(Symbol).Name]
		if !ok || exitLabel <= back {
			continue
		}
		straight := true
		for i := header + 3; i < back; i++ {
			instr, isInstr := items[i].(Instruction)
			if !isInstr {
				straight = false
				break
			}
			switch instr.Mnemonic {
			case "b", "b.", "bl", "ret", "eret":
				straight = false
			}
		}
		if !straight {
			continue
		}
		loops[header+2] = loopShape{header: header, cmp: header + 1, exit: header + 2, exitLabel: exitLabel, bodyStart: header + 3, bodyEnd: back}
	}
	return loops
}

// loopEvent is one side's summary of a data-dependent loop.
type loopEvent struct {
	vars   []string         // loop-carried variables, in a stable order
	header map[string]*term // value at the header on entry
	fresh  map[string]*term // the symbol standing for the value on an iteration
	width  map[string]int
	cond   *term            // continue condition over the fresh symbols (1/0)
	next   map[string]*term // value after one iteration, over the fresh symbols
}

var negatedCondition = map[string]string{"eq": "ne", "ne": "eq", "hs": "lo", "cs": "lo", "lo": "hs", "cc": "hs", "hi": "ls", "ls": "hi", "ge": "lt", "lt": "ge", "gt": "le", "le": "gt"}

// loopEvent summarizes the asm loop whose exit branch was just reached
// with an undecided condition, then continues past the exit.
func (x *pathExecutor) loopEvent(shape loopShape, exitCond string, state *symbolicState) (*term, string, bool) {
	if x.concrete {
		return nil, "a loop that a witness run could not decide", false
	}
	if x.loop != nil {
		return nil, "a second data-dependent loop", false
	}
	// The loop-carried registers are those the body writes; each is a
	// fresh 32-bit symbol when the body only ever writes its w view and the
	// header value is already zero-extended from 32 bits, else 64-bit.
	written := map[int]bool{}
	allW := map[int]bool{}
	for i := shape.bodyStart; i < shape.bodyEnd; i++ {
		instr := x.items[i].(Instruction)
		if instr.Mnemonic == "cmp" || len(instr.Operands) == 0 {
			continue
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
	ev := &loopEvent{header: map[string]*term{}, fresh: map[string]*term{}, width: map[string]int{}, next: map[string]*term{}}
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
		fresh := paramTerm("loop."+name, width)
		value, bound := state.regs[reg]
		if !bound {
			// Written in the body but holding nothing at the header: a
			// scratch register. It takes a fresh value for the iteration and
			// is unbound after the loop (reading it there is outside the
			// subset — the executor loses the last iteration's value).
			scratch[reg] = true
			freshState.regs[reg] = zeroExtend(fresh, 64)
			continue
		}
		if width == 32 && !upperClear(value, x.declared) {
			width = 64
			fresh = paramTerm("loop."+name, width)
		}
		ev.vars = append(ev.vars, name)
		ev.width[name] = width
		ev.header[name] = truncate(value, width)
		ev.fresh[name] = fresh
		freshState.regs[reg] = zeroExtend(fresh, 64)
	}
	// The continue condition: the header comparison on the fresh state,
	// read with the negation of the exit code.
	condState := freshState.clone()
	if reason, ok := step(x.items[shape.cmp].(Instruction), condState); !ok {
		return nil, reason, false
	}
	continueCode, known := negatedCondition[exitCond]
	if !known || !verifiableConditions[exitCond] {
		return nil, fmt.Sprintf("condition code %s", exitCond), false
	}
	ev.cond = cmpTerm(continueCode, condState.flags.left, condState.flags.right)
	// One iteration of the body on the fresh state.
	bodyState := freshState.clone()
	for i := shape.bodyStart; i < shape.bodyEnd; i++ {
		instr := x.items[i].(Instruction)
		var reason string
		var ok bool
		if instr.Mnemonic == "ldr" {
			reason, ok = x.load(instr, bodyState)
		} else {
			reason, ok = step(instr, bodyState)
		}
		if !ok {
			return nil, reason + " (in a loop body)", false
		}
	}
	for _, name := range ev.vars {
		var reg int
		fmt.Sscanf(name, "r%d", &reg)
		ev.next[name] = truncate(bodyState.regs[reg], ev.width[name])
	}
	x.loop = ev
	// Past the exit the loop-carried registers hold their fresh symbols and
	// scratch registers are unbound.
	for reg := range scratch {
		delete(freshState.regs, reg)
	}
	freshState.flags = nil
	return x.run(shape.exitLabel, freshState)
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
		return strings.HasPrefix(t.name, "loop.") && t.width <= 32
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
	if lo.loop != nil {
		return "a second data-dependent loop", false
	}
	assigned := map[string]bool{}
	assignedLocals(loop.Body, assigned)
	ev := &loopEvent{header: map[string]*term{}, fresh: map[string]*term{}, width: map[string]int{}, next: map[string]*term{}}
	for name := range assigned {
		ev.vars = append(ev.vars, name)
	}
	sort.Strings(ev.vars)
	for _, name := range ev.vars {
		local, isLocal := lo.locals[name]
		if !isLocal {
			return fmt.Sprintf("an assignment to %s (not a local)", name), false
		}
		ev.width[name] = local.width
		ev.header[name] = local.value
		fresh := paramTerm("loop."+name, local.width)
		lo.fresh[fresh.name] = local.width
		ev.fresh[name] = fresh
		local.value = fresh
	}
	cond, reason, ok := lo.lowerCondition(loop.Condition)
	if !ok {
		return reason, false
	}
	ev.cond = truncate(cond, 1)
	lo.loop = ev // set first: a nested data-dependent loop is refused as a second one
	if reason, ok := lo.lowerLoopBody(loop.Body); !ok {
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
		}
	}
}

// rename substitutes parameter names (the Oak fresh symbols for the
// coupled registers').
func rename(t *term, sigma map[string]string) *term {
	if t == nil {
		return nil
	}
	switch t.kind {
	case termConst:
		return t
	case termParam:
		if to, renamed := sigma[t.name]; renamed {
			return &term{kind: termParam, width: t.width, name: to}
		}
		return t
	}
	out := *t
	out.cond = rename(t.cond, sigma)
	out.left = rename(t.left, sigma)
	out.right = rename(t.right, sigma)
	return &out
}

// bitEqual decides two terms equal at a common width by bit-blasting;
// decided is false past the node budget.
func bitEqual(a, b *term, widthOf func(string) int) (equal bool, decided bool) {
	width := a.width
	if b.width > width {
		width = b.width
	}
	a, b = adaptWidth(a, width), adaptWidth(b, width)
	mentioned := map[string]bool{}
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
	aBits, bBits := bl.blast(a), bl.blast(b)
	if aBits == nil || bBits == nil || bl.bdd.exceeded {
		return false, false
	}
	for i := 0; i < width; i++ {
		if aBits[i] != bBits[i] {
			return false, true
		}
	}
	return true, true
}

// loopWitnessInputs are small concrete inputs: under them the loops
// unroll within budget. Scalars and span lengths vary; elements come from
// the fixed memory.
func loopWitnessInputs(sig *ast.FunctionStatement) []map[string]uint64 {
	var names []string
	for _, param := range sig.Parameters {
		if _, _, isSpan := spanShape(param.Type); isSpan {
			names = append(names, spanLenName(param.Name.Value))
			continue
		}
		names = append(names, param.Name.Value)
	}
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

// verifyLoops is the loop-mode verdict: witnesses, then the coupling proof.
func verifyLoops(fn *Function, sig *ast.FunctionStatement, oakBody ast.Expression, exec *pathExecutor, lowering *oakLowering, asmTerm, oakTerm *term, width int) Verdict {
	trusted := func(reason string) Verdict {
		return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (%s) — trusted per docs/spec/94-assembler.md §5", fn.Name, reason)}
	}
	switch {
	case exec.loop == nil:
		return trusted("the Oak body has a data-dependent loop but the asm body does not")
	case lowering.loop == nil:
		return trusted("the asm body has a data-dependent loop but the Oak body does not")
	}
	// Witnesses: concrete inputs decide both loops.
	checked := 0
	for _, env := range loopWitnessInputs(sig) {
		asmValue, _, _, okA := executeBody(fn, sig, env)
		concrete := newLowering(sig)
		concrete.concrete = env
		oakValue, _, okO := concrete.lower(oakBody, width)
		if !okA || !okO {
			continue // beyond the unrolling budget on this input
		}
		got, want := truncate(asmValue, width).eval(env), oakValue.eval(env)
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
	// Coupling: pair each Oak loop-carried local with a register whose
	// header value is the same.
	asmLoop, oakLoop := exec.loop, lowering.loop
	widthOfName := func(name string) int {
		if w, isFresh := asmLoop.width[strings.TrimPrefix(name, "loop.")]; isFresh && strings.HasPrefix(name, "loop.r") {
			return w
		}
		return lowering.declaredWidth(name)
	}
	// Candidates: registers of the local's width whose header value is the
	// local's. Several locals may start alike (two zeroed counters), so the
	// pairing is a small search: an assignment is accepted when the
	// continue conditions agree and one iteration preserves every pair.
	candidates := map[string][]string{}
	for _, local := range oakLoop.vars {
		for _, reg := range asmLoop.vars {
			if asmLoop.width[reg] != oakLoop.width[local] {
				continue
			}
			if equal, decided := bitEqual(oakLoop.header[local], asmLoop.header[reg], widthOfName); decided && equal {
				candidates[local] = append(candidates[local], reg)
			}
		}
		if len(candidates[local]) == 0 {
			return evidence(fmt.Sprintf("no register carries the loop variable %s at the loop header", local))
		}
	}
	sigma := map[string]string{}
	used := map[string]bool{}
	var pairs []string
	var failure string
	var search func(i int) bool
	search = func(i int) bool {
		if i == len(oakLoop.vars) {
			if equal, decided := bitEqual(rename(oakLoop.cond, sigma), asmLoop.cond, widthOfName); !decided || !equal {
				failure = "the loops' continue conditions were not proven equal"
				return false
			}
			for _, local := range oakLoop.vars {
				reg := strings.TrimPrefix(sigma["loop."+local], "loop.")
				if equal, decided := bitEqual(rename(oakLoop.next[local], sigma), asmLoop.next[reg], widthOfName); !decided || !equal {
					failure = fmt.Sprintf("one iteration was not proven to preserve %s↔%s", local, reg)
					return false
				}
			}
			return true
		}
		local := oakLoop.vars[i]
		for _, reg := range candidates[local] {
			if used[reg] {
				continue
			}
			used[reg] = true
			sigma["loop."+local] = "loop." + reg
			if search(i + 1) {
				return true
			}
			delete(used, reg)
			delete(sigma, "loop."+local)
		}
		return false
	}
	if !search(0) {
		return evidence(failure)
	}
	for _, local := range oakLoop.vars {
		pairs = append(pairs, local+"↔"+strings.TrimPrefix(sigma["loop."+local], "loop."))
	}
	// The fresh symbols are free parameters of the final comparison. A
	// result reading a loop-carried register no Oak variable is coupled to
	// is beyond the method (its exit value has no Oak counterpart).
	mentioned := map[string]bool{}
	collectParams(asmTerm, mentioned)
	for name := range mentioned {
		if reg := strings.TrimPrefix(name, "loop."); strings.HasPrefix(name, "loop.r") && !used[reg] {
			return evidence(fmt.Sprintf("the result reads loop-carried register %s, which no Oak variable is coupled to", reg))
		}
	}
	for reg, w := range asmLoop.width {
		lowering.fresh["loop."+reg] = w
	}
	verdict := decideEqual(fn, lowering, asmTerm, rename(oakTerm, sigma), width, fmt.Sprintf(" — data-dependent loop coupled inductively (%s), %d concrete inputs agree", strings.Join(pairs, ", "), checked))
	if verdict.Kind == VerdictWitnessed {
		return evidence("the results after the loops exceeded the bit-level budget")
	}
	return verdict
}
