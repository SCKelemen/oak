package asm

// Semantic verification of straight-line bodies (docs/spec/94-assembler.md
// §8, first increment). The Oak fallback body is the specification. A
// straight-line asm body is executed symbolically over a term language
// transliterating Oak.AssemblerSemantics (registers as 64-bit values, wN
// writes zero-extend, wN reads truncate); the Oak expression lowers to the
// same language under Oak's total wrapping arithmetic; then:
//
//   - equal canonical LINEAR normal forms (sums of parameters and constants
//     modulo 2^width; lsl by a constant is multiplication) are a PROOF for
//     that subset;
//   - otherwise both terms are evaluated on a deterministic witness set;
//     disagreement is a definite mismatch (a hard error), agreement is
//     EVIDENCE and is labeled so;
//   - anything the executor or the lowering cannot express (labels, calls,
//     memory, system instructions, non-constant shift counts, unsupported
//     operators) is TRUSTED per §5 and labeled so.
//
// The verifier only tightens: it never admits a body the seam checker
// rejected, and its verdicts are labeled proof / evidence / trusted.

import (
	"fmt"
	"sort"
	"strconv"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// Verdict is the outcome of verifying one asm function against its Oak body.
type Verdict struct {
	Kind    VerdictKind
	Message string
}

type VerdictKind int

const (
	VerdictTrusted   VerdictKind = iota // not verified; trusted per §5
	VerdictProven                       // canonical normal forms agree
	VerdictWitnessed                    // witnesses agree; no proof
	VerdictMismatch                     // a witness disagrees: definite bug
)

func (k VerdictKind) String() string {
	switch k {
	case VerdictProven:
		return "proven"
	case VerdictWitnessed:
		return "witness-checked"
	case VerdictMismatch:
		return "mismatch"
	}
	return "trusted"
}

// --- terms ---------------------------------------------------------------

type termKind int

const (
	termParam termKind = iota
	termConst
	termBinary
	termCmp // a condition code over two operands; the value is 1 or 0
	termIte // cond ? left : right
)

// term is a fixed-width bitvector expression. Width is 32 or 64.
type term struct {
	kind  termKind
	width int
	name  string // termParam
	value uint64 // termConst (already masked to width)
	op    string // termBinary: add sub and or xor shl shr; termCmp: condition code
	left  *term
	right *term
	cond  *term // termIte
}

// conditionHolds is the ARM condition-code semantics over the NZCV flags
// of `left - right` (Oak.AssemblerSemantics.condHolds), stated as the
// comparisons those flags encode: eq/ne on equality, hs/lo/hi/ls unsigned,
// ge/lt/gt/le signed. mi/pl/vs/vc read a single flag and are outside the
// verified subset.
var verifiableConditions = map[string]bool{"eq": true, "ne": true, "hs": true, "cs": true, "lo": true, "cc": true, "hi": true, "ls": true, "ge": true, "lt": true, "gt": true, "le": true}

func conditionHolds(code string, left, right uint64, width int) bool {
	m := mask(width)
	l, r := left&m, right&m
	shift := uint(64 - width)
	sl, sr := int64(l<<shift)>>shift, int64(r<<shift)>>shift
	switch code {
	case "eq":
		return l == r
	case "ne":
		return l != r
	case "hs", "cs":
		return l >= r
	case "lo", "cc":
		return l < r
	case "hi":
		return l > r
	case "ls":
		return l <= r
	case "ge":
		return sl >= sr
	case "lt":
		return sl < sr
	case "gt":
		return sl > sr
	case "le":
		return sl <= sr
	}
	return false
}

// The constructors fold constants: a term over constants is the constant
// its total evaluation yields. Folding is what lets a counted loop decide
// its own exit (the counter's comparison becomes a constant) on both sides.
func cmpTerm(code string, left, right *term) *term {
	t := &term{kind: termCmp, width: left.width, op: code, left: left, right: right}
	if left.kind == termConst && right.kind == termConst {
		return constTerm(t.eval(nil), left.width)
	}
	return t
}

func iteTerm(cond, left, right *term) *term {
	if cond.kind == termConst {
		if cond.value != 0 {
			return left
		}
		return right
	}
	return &term{kind: termIte, width: left.width, cond: cond, left: left, right: right}
}

func mask(width int) uint64 {
	if width >= 64 {
		return ^uint64(0)
	}
	return (uint64(1) << uint(width)) - 1
}

func constTerm(value uint64, width int) *term {
	return &term{kind: termConst, width: width, value: value & mask(width)}
}

func paramTerm(name string, width int) *term {
	return &term{kind: termParam, width: width, name: name}
}

func binaryTerm(op string, left, right *term) *term {
	t := &term{kind: termBinary, width: left.width, op: op, left: left, right: right}
	if left.kind == termConst && right.kind == termConst {
		return constTerm(t.eval(nil), left.width)
	}
	return t
}

// adaptWidth views a term at another width: a narrower term zero-extends,
// a wider one truncates (the machine's and Oak's conversions alike).
func adaptWidth(t *term, width int) *term {
	if t.width < width {
		return zeroExtend(t, width)
	}
	return truncate(t, width)
}

// eval computes the term for a parameter assignment (Oak.AssemblerSemantics
// transliterated: every operation is total and wraps to the width).
func (t *term) eval(env map[string]uint64) uint64 {
	m := mask(t.width)
	switch t.kind {
	case termParam:
		return env[t.name] & m
	case termConst:
		return t.value & m
	case termCmp:
		// The comparison happens at the operands' width; t.width is only
		// the width the 1/0 result is used at.
		if conditionHolds(t.op, t.left.eval(env), t.right.eval(env), t.left.width) {
			return 1
		}
		return 0
	case termIte:
		if t.cond.eval(env) != 0 {
			return t.left.eval(env) & m
		}
		return t.right.eval(env) & m
	}
	// Operands evaluate at their own widths (a mask node's inner term keeps
	// its width and modulus); the operation wraps to this term's width.
	l := t.left.eval(env) & m
	r := t.right.eval(env) & m
	switch t.op {
	case "add":
		return (l + r) & m
	case "sub":
		return (l - r) & m
	case "and":
		return (l & r) & m
	case "or":
		return (l | r) & m
	case "xor":
		return (l ^ r) & m
	case "shl":
		return (l << (r % uint64(t.width))) & m
	case "shr":
		return (l >> (r % uint64(t.width))) & m
	}
	return 0
}

func (t *term) String() string {
	switch t.kind {
	case termParam:
		return t.name
	case termConst:
		return fmt.Sprintf("%d", t.value)
	case termCmp:
		return fmt.Sprintf("(%s %s %s)", t.left, t.op, t.right)
	case termIte:
		return fmt.Sprintf("(%s ? %s : %s)", t.cond, t.left, t.right)
	}
	return fmt.Sprintf("(%s %s %s)", t.left, t.op, t.right)
}

// --- linear normal form ------------------------------------------------

// linearForm is Σ coeff·param + constant modulo 2^width; nil when the term
// is not linear (and, or, xor, shr, or a non-constant shift).
type linearForm struct {
	width    int
	coeffs   map[string]uint64
	constant uint64
}

// linearAt computes the form modulo 2^w. A mask by at least w bits is
// transparent modulo 2^w, which is how the wN write/read discipline's
// masks disappear from a 32-bit result; a narrower mask is not linear.
func (t *term) linearAt(w int) *linearForm {
	m := mask(w)
	switch t.kind {
	case termParam:
		return &linearForm{width: w, coeffs: map[string]uint64{t.name: 1}}
	case termConst:
		return &linearForm{width: w, constant: t.value & m}
	case termCmp, termIte:
		return nil
	}
	switch t.op {
	case "and":
		if t.right.kind == termConst && t.right.value&m == m {
			return t.left.linearAt(w)
		}
		if t.left.kind == termConst && t.left.value&m == m {
			return t.right.linearAt(w)
		}
		return nil
	case "add", "sub":
		l, r := t.left.linearAt(w), t.right.linearAt(w)
		if l == nil || r == nil {
			return nil
		}
		out := &linearForm{width: w, coeffs: map[string]uint64{}}
		for name, c := range l.coeffs {
			out.coeffs[name] = c
		}
		for name, c := range r.coeffs {
			if t.op == "add" {
				out.coeffs[name] = (out.coeffs[name] + c) & m
			} else {
				out.coeffs[name] = (out.coeffs[name] - c) & m
			}
		}
		if t.op == "add" {
			out.constant = (l.constant + r.constant) & m
		} else {
			out.constant = (l.constant - r.constant) & m
		}
		return out.trim()
	case "shl":
		if t.right.kind != termConst || t.width < w {
			return nil
		}
		l := t.left.linearAt(w)
		if l == nil {
			return nil
		}
		factor := uint64(1) << (t.right.value % uint64(t.width))
		out := &linearForm{width: w, coeffs: map[string]uint64{}, constant: (l.constant * factor) & m}
		for name, c := range l.coeffs {
			out.coeffs[name] = (c * factor) & m
		}
		return out.trim()
	}
	return nil
}

func (f *linearForm) trim() *linearForm {
	for name, c := range f.coeffs {
		if c == 0 {
			delete(f.coeffs, name)
		}
	}
	return f
}

func (f *linearForm) String() string {
	names := make([]string, 0, len(f.coeffs))
	for name := range f.coeffs {
		names = append(names, name)
	}
	sort.Strings(names)
	parts := make([]string, 0, len(names)+1)
	for _, name := range names {
		parts = append(parts, fmt.Sprintf("%d*%s", f.coeffs[name], name))
	}
	parts = append(parts, strconv.FormatUint(f.constant, 10))
	return strings.Join(parts, " + ") + fmt.Sprintf(" (mod 2^%d)", f.width)
}

func (f *linearForm) equal(g *linearForm) bool {
	if f.width != g.width || f.constant != g.constant || len(f.coeffs) != len(g.coeffs) {
		return false
	}
	for name, c := range f.coeffs {
		if g.coeffs[name] != c {
			return false
		}
	}
	return true
}

// --- symbolic execution of the asm body ------------------------------------

type symbolicState struct {
	regs  map[int]*term // physical register -> 64-bit term
	flags *flagsFact    // NZCV as the operands that produced them; nil until set
	// Loop accounting along this path: the step at which each label was
	// last passed and the step of the last fork. A backward branch whose
	// target was passed before the last fork closes a loop containing a
	// data-dependent exit — its trip count is not constant.
	labelStep map[int]int
	forkStep  int
}

// flagsFact records what produced the flags: cmp/subs leave NZCV as the
// flags of `left - right` at width, which every condition code reads as a
// comparison of the two operands. adds sets flags the comparison reading
// does not describe (unknown).
type flagsFact struct {
	left, right *term
	width       int
	unknown     bool
}

func (s *symbolicState) read(reg Register) (*term, bool) {
	if reg.ZeroRegister() {
		return constTerm(0, widthOf(reg.Class)), true
	}
	value, ok := s.regs[reg.Num]
	if !ok {
		return nil, false
	}
	if reg.Class == ClassW {
		return truncate(value, 32), true
	}
	return value, true
}

func (s *symbolicState) write(reg Register, value *term) {
	if reg.ZeroRegister() {
		return
	}
	if reg.Class == ClassW {
		value = zeroExtend(value, 64) // AArch64: a 32-bit write zeroes the upper half
	}
	s.regs[reg.Num] = value
}

func widthOf(class RegClass) int {
	if class == ClassW {
		return 32
	}
	return 64
}

// truncate/zeroExtend realize the width views of Oak.AssemblerSemantics
// explicitly: a value never changes meaning, only the mask applied to it.
// Parameters and constants are the same number at either width (parameter
// values are bounded by their declared width); a computed term is wrapped
// in an explicit and-mask, so the inner operation keeps its own width and
// modulus and eval never reinterprets it.
func truncate(t *term, width int) *term {
	if t.width == width {
		return t
	}
	switch t.kind {
	case termConst:
		return constTerm(t.value, width)
	case termParam:
		return &term{kind: termParam, width: width, name: t.name}
	case termCmp:
		return &term{kind: termCmp, width: width, op: t.op, left: t.left, right: t.right}
	}
	return &term{kind: termBinary, width: width, op: "and", left: t, right: constTerm(mask(width), width)}
}

func zeroExtend(t *term, width int) *term {
	if t.width == width {
		return t
	}
	switch t.kind {
	case termConst:
		return constTerm(t.value&mask(t.width), width)
	case termParam:
		return &term{kind: termParam, width: width, name: t.name}
	case termCmp:
		return &term{kind: termCmp, width: width, op: t.op, left: t.left, right: t.right}
	}
	// The narrow computation's wrap is preserved by masking to its width.
	return &term{kind: termBinary, width: width, op: "and", left: t, right: constTerm(mask(t.width), width)}
}

var verifiableOps = map[string]string{"add": "add", "sub": "sub", "adds": "add", "subs": "sub", "and": "and", "orr": "or", "eor": "xor", "lsl": "shl", "lsr": "shr"}

// executeBody symbolically executes the body along every path; reports (result
// term, "", true) or ("", reason, false) when the body is outside the
// verified subset.
func executeBody(fn *Function, sig *ast.FunctionStatement) (*term, string, bool) {
	state := &symbolicState{regs: map[int]*term{}}
	params := map[string]RegClass{}
	spans := map[string]int64{} // span/view parameter -> element size in bytes
	for _, param := range sig.Parameters {
		if elem, _, isSpan := spanShape(param.Type); isSpan {
			spans[param.Name.Value] = elem
			continue
		}
		class, ok := contractClass(param.Type)
		if !ok || class == ClassV {
			return nil, "vector or non-integer parameters", false
		}
		params[param.Name.Value] = class
	}
	for _, binding := range fn.Bindings {
		if binding.Length != nil {
			// A span arrives as its {base, len} pair: the base is the opaque
			// address term `&v` (memory through it resolves to element
			// parameters), the length the 32-bit parameter len(v).
			if _, isSpan := spans[binding.Param]; !isSpan {
				return nil, "span binding of a non-span parameter", false
			}
			state.regs[binding.Register.Num] = paramTerm(spanBaseName(binding.Param), 64)
			state.regs[binding.Length.Num] = zeroExtend(paramTerm(spanLenName(binding.Param), 32), 64)
			continue
		}
		class := params[binding.Param]
		state.regs[binding.Register.Num] = zeroExtend(paramTerm(binding.Param, widthOf(class)), 64)
		if class == ClassX {
			state.regs[binding.Register.Num] = paramTerm(binding.Param, 64)
		}
	}
	resultClass, hasResult := contractClass(sig.ReturnType)
	if !hasResult || resultClass == ClassV {
		return nil, "no integer result", false
	}
	labels := map[string]int{}
	for index, item := range fn.Items {
		switch it := item.(type) {
		case Label:
			labels[it.Name] = index
		case Align:
			return nil, "alignment directives", false
		}
	}
	exec := &pathExecutor{items: fn.Items, labels: labels, resultClass: resultClass, spans: spans}
	return exec.run(0, state)
}

// Span parameters appear in terms under three names: the opaque base
// address `&v`, the length `len(v)`, and the elements `v[k]`. The Oak
// lowering produces the same names for len(v) and v[k]; the base has no
// Oak spelling (a result depending on it can never match).
func spanBaseName(param string) string          { return "&" + param }
func spanLenName(param string) string           { return "len(" + param + ")" }
func spanElemName(param string, k int64) string { return fmt.Sprintf("%s[%d]", param, k) }

// pathBudget bounds the number of paths a body may unfold into; stepBudget
// bounds the instructions executed across all paths, which is what bounds
// the unrolling of counted loops.
const (
	pathBudget = 256
	stepBudget = 1 << 16
)

// pathExecutor unfolds a body into its paths: a conditional branch forks
// the state, the taken path continuing at the label under the branch's
// condition and the fall-through under its negation, and the two results
// meet as a select. A branch whose condition folds to a constant follows
// only the decided path — which is how a counted loop unrolls: its
// backward branch compares a counter that is a constant on every
// iteration. A backward branch whose condition is not constant is a loop
// with a data-dependent trip count, outside the subset. The path and step
// budgets bound the unfolding.
type pathExecutor struct {
	items       []Item
	labels      map[string]int
	resultClass RegClass
	spans       map[string]int64 // span parameter -> element size in bytes
	paths       int
	steps       int
}

func (s *symbolicState) clone() *symbolicState {
	regs := make(map[int]*term, len(s.regs))
	for reg, value := range s.regs {
		regs[reg] = value
	}
	labels := make(map[int]int, len(s.labelStep))
	for label, step := range s.labelStep {
		labels[label] = step
	}
	return &symbolicState{regs: regs, flags: s.flags, labelStep: labels, forkStep: s.forkStep}
}

// backward reports whether a branch to target from pc closes a loop the
// path can unroll: the target lies behind, and no fork happened since the
// path last passed it.
func (s *symbolicState) backwardAllowed(target, pc int) (backward bool, allowed bool) {
	if target > pc {
		return false, true
	}
	passed, seen := s.labelStep[target]
	return true, seen && passed >= s.forkStep
}

// run executes from item index pc to a ret on every path.
func (x *pathExecutor) run(pc int, state *symbolicState) (*term, string, bool) {
	x.paths++
	if x.paths > pathBudget {
		return nil, "more paths than the verifier's budget", false
	}
	if state.labelStep == nil {
		state.labelStep = map[int]int{}
	}
	for ; pc < len(x.items); pc++ {
		instr, isInstr := x.items[pc].(Instruction)
		if !isInstr {
			state.labelStep[pc] = x.steps // a label is a position
			continue
		}
		x.steps++
		if x.steps > stepBudget {
			return nil, "more instructions than the verifier's unrolling budget", false
		}
		switch instr.Mnemonic {
		case "ret":
			result, ok := state.read(Register{Class: x.resultClass, Num: 0})
			if !ok {
				return nil, "result register never written", false
			}
			return result, "", true
		case "b":
			target, ok := x.labels[instr.Operands[0].(Symbol).Name]
			if !ok {
				return nil, "a branch to an unknown label", false
			}
			if _, allowed := state.backwardAllowed(target, pc); !allowed {
				return nil, "a loop whose trip count depends on the inputs", false
			}
			pc = target - 1
			continue
		case "b.":
			if state.flags == nil || state.flags.unknown {
				return nil, "b.cond reading flags not produced by cmp/subs", false
			}
			if !verifiableConditions[instr.Cond] {
				return nil, fmt.Sprintf("condition code %s", instr.Cond), false
			}
			target, ok := x.labels[instr.Operands[0].(Symbol).Name]
			if !ok {
				return nil, "a branch to an unknown label", false
			}
			cond := cmpTerm(instr.Cond, state.flags.left, state.flags.right)
			if cond.kind == termConst {
				// Decided: one continuation. A counted loop's backward
				// branch always lands here — on every path, since the
				// counter it compares is constant whatever the inputs did
				// inside the loop; the path and step budgets bound the
				// unfolding of forks inside it.
				if cond.value != 0 {
					pc = target - 1
				}
				continue
			}
			if backward, _ := state.backwardAllowed(target, pc); backward {
				return nil, "a loop whose trip count depends on the inputs", false
			}
			state.forkStep = x.steps
			taken, reason, ok := x.run(target, state.clone())
			if !ok {
				return nil, reason, false
			}
			fallThrough, reason, ok := x.run(pc+1, state)
			if !ok {
				return nil, reason, false
			}
			return iteTerm(cond, taken, fallThrough), "", true
		}
		if instr.Mnemonic == "ldr" {
			if reason, ok := x.load(instr, state); !ok {
				return nil, reason, false
			}
			continue
		}
		if reason, ok := step(instr, state); !ok {
			return nil, reason, false
		}
	}
	return nil, "no ret reached", false
}

// load executes `ldr rD, [xB, #off]` through a span base: the seam checker
// has already placed the access under a dominating length guard, so the
// verifier's only question is which element it reads. The offset must be a
// whole element and the register width the element's width; loads from the
// frame, stores, and moving bases are outside the subset.
func (x *pathExecutor) load(instr Instruction, state *symbolicState) (string, bool) {
	dest := instr.Operands[0].(Register)
	mem := instr.Operands[1].(Memory)
	if mem.Base.Class == ClassSP {
		return "frame memory", false
	}
	base, bound := state.regs[mem.Base.Num]
	if !bound || base.kind != termParam || !strings.HasPrefix(base.name, "&") {
		return "a load through a register that is not a span base", false
	}
	param := strings.TrimPrefix(base.name, "&")
	elem := x.spans[param]
	if mem.Mode != MemOffset {
		return "a span base moved by pre/post-index", false
	}
	if int64(widthOf(dest.Class)/8) != elem {
		return fmt.Sprintf("a %d-bit load over %d-byte elements", widthOf(dest.Class), elem), false
	}
	if mem.Offset < 0 || mem.Offset%elem != 0 {
		return "a load not aligned to an element", false
	}
	state.write(dest, paramTerm(spanElemName(param, mem.Offset/elem), widthOf(dest.Class)))
	return "", true
}

// step executes one data-processing instruction on the state.
func step(instr Instruction, state *symbolicState) (string, bool) {
	{
		switch instr.Mnemonic {
		case "mov":
			dest := instr.Operands[0].(Register)
			value, ok := operandTerm(state, instr.Operands[1], widthOf(dest.Class))
			if !ok {
				return "unbound register read", false
			}
			state.write(dest, value)
		case "cmp":
			left := instr.Operands[0].(Register)
			width := widthOf(left.Class)
			l, okL := operandTerm(state, left, width)
			r, okR := operandTerm(state, instr.Operands[1], width)
			if !okL || !okR {
				return "unbound register read", false
			}
			state.flags = &flagsFact{left: l, right: r, width: width}
		case "csel", "cset":
			// The select reads the flags as the comparison that produced them.
			if state.flags == nil || state.flags.unknown {
				return fmt.Sprintf("%s reading flags not produced by cmp/subs", instr.Mnemonic), false
			}
			code := instr.Operands[len(instr.Operands)-1].(Condition).Code
			if !verifiableConditions[code] {
				return fmt.Sprintf("condition code %s", code), false
			}
			dest := instr.Operands[0].(Register)
			width := widthOf(dest.Class)
			cond := cmpTerm(code, state.flags.left, state.flags.right)
			whenTrue, whenFalse := constTerm(1, width), constTerm(0, width)
			if instr.Mnemonic == "csel" {
				var okT, okF bool
				whenTrue, okT = operandTerm(state, instr.Operands[1], width)
				whenFalse, okF = operandTerm(state, instr.Operands[2], width)
				if !okT || !okF {
					return "unbound register read", false
				}
			}
			state.write(dest, iteTerm(cond, whenTrue, whenFalse))
		default:
			op, verifiable := verifiableOps[instr.Mnemonic]
			if !verifiable || len(instr.Operands) != 3 {
				return fmt.Sprintf("instruction %s", instr.Mnemonic), false
			}
			dest := instr.Operands[0].(Register)
			if dest.Class == ClassSP {
				return "stack pointer arithmetic", false
			}
			left, okL := operandTerm(state, instr.Operands[1], widthOf(dest.Class))
			right, okR := operandTerm(state, instr.Operands[2], widthOf(dest.Class))
			if !okL || !okR {
				return "unbound register read", false
			}
			switch instr.Mnemonic {
			case "subs":
				state.flags = &flagsFact{left: left, right: right, width: widthOf(dest.Class)}
			case "adds":
				state.flags = &flagsFact{unknown: true}
			}
			state.write(dest, binaryTerm(op, left, right))
		}
	}
	return "", true
}

func operandTerm(state *symbolicState, operand Operand, width int) (*term, bool) {
	switch o := operand.(type) {
	case Register:
		return state.read(o)
	case Immediate:
		return constTerm(uint64(o.Value), width), true
	}
	return nil, false
}

// --- the Oak specification ----------------------------------------------

var oakOps = map[string]string{"+": "add", "-": "sub", "&": "and", "|": "or", "^": "xor", "<<": "shl", ">>": "shr"}

// oakComparisons maps Oak's comparison operators to the condition code
// whose flag reading is that comparison, per signedness of the operands.
var oakComparisons = map[string][2]string{
	"==": {"eq", "eq"}, "!=": {"ne", "ne"},
	"<": {"lo", "lt"}, "<=": {"ls", "le"}, ">": {"hi", "gt"}, ">=": {"hs", "ge"},
}

// oakLowering carries the parameter contract: declared widths and
// signedness (i8/i16/i32/i64 compare signed, everything else unsigned),
// and the span/view parameters with their element widths.
type oakLowering struct {
	params map[string]int
	signed map[string]bool
	spans  map[string]spanContract
	locals map[string]*oakLocal // statement-body locals, in declaration scope
}

// oakLocal is a typed local of a statement body: its current symbolic
// value (assignments replace it) at its declared width and signedness.
type oakLocal struct {
	value  *term
	width  int
	signed bool
}

// loopBudget bounds the iterations a `while` may unroll.
const loopBudget = 4096

// lowerBlock executes a statement body symbolically: typed local
// declarations and assignments update the locals, a `while` whose
// condition folds to a constant unrolls (a data-dependent condition is
// outside the subset), and the final expression statement is the result.
func (lo *oakLowering) lowerBlock(block *ast.BlockStatement, width int) (*term, string, bool) {
	if block == nil || len(block.Statements) == 0 {
		return nil, "an empty block", false
	}
	if lo.locals == nil {
		lo.locals = map[string]*oakLocal{}
	}
	for i, stmt := range block.Statements {
		last := i == len(block.Statements)-1
		switch s := stmt.(type) {
		case *ast.ExpressionStatement:
			if !last {
				return nil, "an expression statement before the end of a block", false
			}
			return lo.lower(s.Expression, width)
		case *ast.VariableDeclaration:
			if s.Value == nil || s.Type == nil {
				return nil, "a local without both a type and an initializer", false
			}
			w, signed, ok := scalarType(s.Type)
			if !ok {
				return nil, fmt.Sprintf("a local of type %s", typeText(s.Type)), false
			}
			value, reason, ok := lo.lower(s.Value, w)
			if !ok {
				return nil, reason, false
			}
			lo.locals[s.Name.Value] = &oakLocal{value: value, width: w, signed: signed}
		case *ast.AssignmentStatement:
			local, isLocal := lo.locals[s.Name.Value]
			if !isLocal {
				return nil, fmt.Sprintf("an assignment to %s (not a local)", s.Name.Value), false
			}
			value, reason, ok := lo.lower(s.Value, local.width)
			if !ok {
				return nil, reason, false
			}
			local.value = value
		case *ast.WhileStatement:
			if reason, ok := lo.lowerWhile(s); !ok {
				return nil, reason, false
			}
		default:
			return nil, fmt.Sprintf("%T", stmt), false
		}
	}
	return nil, "a block that does not end in an expression", false
}

// lowerWhile unrolls a counted loop: the condition must fold to a
// constant before every iteration.
func (lo *oakLowering) lowerWhile(loop *ast.WhileStatement) (string, bool) {
	for iteration := 0; ; iteration++ {
		if iteration > loopBudget {
			return "a loop beyond the verifier's unrolling budget", false
		}
		cond, reason, ok := lo.lowerCondition(loop.Condition)
		if !ok {
			return reason, false
		}
		if cond.kind != termConst {
			return "a loop whose trip count depends on the inputs", false
		}
		if cond.value == 0 {
			return "", true
		}
		for _, stmt := range loop.Body.Statements {
			switch s := stmt.(type) {
			case *ast.AssignmentStatement:
				local, isLocal := lo.locals[s.Name.Value]
				if !isLocal {
					return fmt.Sprintf("an assignment to %s (not a local)", s.Name.Value), false
				}
				value, reason, ok := lo.lower(s.Value, local.width)
				if !ok {
					return reason, false
				}
				local.value = value
			case *ast.WhileStatement:
				if reason, ok := lo.lowerWhile(s); !ok {
					return reason, false
				}
			default:
				return fmt.Sprintf("%T in a loop body", stmt), false
			}
		}
	}
}

// scalarType reads a local's declared fixed-width integer type.
func scalarType(expr ast.Expression) (width int, signed bool, ok bool) {
	switch typeText(expr) {
	case "u8", "u16", "u32", "Bool", "byte", "rune":
		return 32, false, true
	case "i8", "i16", "i32":
		return 32, true, true
	case "u64":
		return 64, false, true
	case "i64":
		return 64, true, true
	}
	return 0, false, false
}

type spanContract struct {
	elemWidth int
	signed    bool
}

// spanElement recognizes v[k] over a span parameter with a constant index
// (a literal, or a primitive constructor over one: v[u32(1)]).
func (lo *oakLowering) spanElement(expr ast.Expression) (name string, contract spanContract, ok bool) {
	index, isIndex := expr.(*ast.IndexExpression)
	if !isIndex || index.Dot {
		return "", spanContract{}, false
	}
	ident, isIdent := index.Left.(*ast.Identifier)
	if !isIdent {
		return "", spanContract{}, false
	}
	contract, isSpan := lo.spans[ident.Value]
	if !isSpan {
		return "", spanContract{}, false
	}
	k, isConst := constantIndexValue(index.Index)
	if !isConst || k < 0 {
		return "", spanContract{}, false
	}
	return spanElemName(ident.Value, k), contract, true
}

func constantIndexValue(expr ast.Expression) (int64, bool) {
	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		return e.Value, true
	case *ast.InvocationExpression:
		if ident, isIdent := e.Function.(*ast.Identifier); isIdent && len(e.Arguments) == 1 {
			switch ident.Value {
			case "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64":
				return constantIndexValue(e.Arguments[0])
			}
		}
	}
	return 0, false
}

// spanLength recognizes len(v) over a span parameter.
func (lo *oakLowering) spanLength(expr ast.Expression) (string, bool) {
	call, isCall := expr.(*ast.InvocationExpression)
	if !isCall || len(call.Arguments) != 1 {
		return "", false
	}
	fn, isIdent := call.Function.(*ast.Identifier)
	arg, argIsIdent := call.Arguments[0].(*ast.Identifier)
	if !isIdent || !argIsIdent || fn.Value != "len" {
		return "", false
	}
	if _, isSpan := lo.spans[arg.Value]; !isSpan {
		return "", false
	}
	return spanLenName(arg.Value), true
}

// lower turns a pure expression over the parameters into a term of the
// result width; reports the construct it cannot express.
func (lo *oakLowering) lower(expr ast.Expression, width int) (*term, string, bool) {
	switch e := expr.(type) {
	case *ast.Identifier:
		if local, isLocal := lo.locals[e.Value]; isLocal {
			return adaptWidth(local.value, width), "", true
		}
		if w, isParam := lo.params[e.Value]; isParam {
			return truncate(paramTerm(e.Value, w), width), "", true
		}
		return nil, fmt.Sprintf("identifier %s (not a parameter)", e.Value), false
	case *ast.IntegerLiteral:
		return constTerm(uint64(e.Value), width), "", true
	case *ast.Boolean:
		// Bool lowers to its C representation: 1 or 0 at the result width.
		if e.Value {
			return constTerm(1, width), "", true
		}
		return constTerm(0, width), "", true
	case *ast.IndexExpression:
		if name, contract, isElem := lo.spanElement(e); isElem {
			return truncate(paramTerm(name, contract.elemWidth), width), "", true
		}
		return nil, "an index that is not a constant element of a span parameter", false
	case *ast.InvocationExpression:
		if name, isLen := lo.spanLength(e); isLen {
			return zeroExtend(truncate(paramTerm(name, 32), width), width), "", true
		}
		// Primitive constructors over constants: u32(15).
		ident, isIdent := e.Function.(*ast.Identifier)
		if !isIdent || len(e.Arguments) != 1 {
			return nil, "a call", false
		}
		switch ident.Value {
		case "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64":
			return lo.lower(e.Arguments[0], width)
		}
		return nil, fmt.Sprintf("call to %s", ident.Value), false
	case *ast.InfixExpression:
		// A comparison or a condition in value position is a Bool result:
		// 1 or 0 at the result width (`is_zero: (v: u64) -> Bool = v == 0`).
		if _, isComparison := oakComparisons[e.Operator]; isComparison || e.Operator == "&&" || e.Operator == "||" {
			cond, reason, ok := lo.lowerCondition(e)
			if !ok {
				return nil, reason, false
			}
			return zeroExtend(truncate(cond, width), width), "", true
		}
		op, ok := oakOps[e.Operator]
		if !ok {
			return nil, fmt.Sprintf("operator %s", e.Operator), false
		}
		left, reason, okL := lo.lower(e.Left, width)
		if !okL {
			return nil, reason, false
		}
		right, reason, okR := lo.lower(e.Right, width)
		if !okR {
			return nil, reason, false
		}
		if (op == "shl" || op == "shr") && right.kind != termConst {
			// Oak traps at the width; the machine wraps the count.
			return nil, "a non-constant shift count", false
		}
		return binaryTerm(op, left, right), "", true
	case *ast.BlockExpression:
		return lo.lowerBlock(e.Block, width)
	case *ast.MatchExpression:
		// A value-position Bool conditional over a comparison of parameters:
		// `a < b ? b | a`. The comparison happens at the operands' own width
		// and signedness; the arms are lowered at the result width.
		whenTrue, whenFalse, isBool := boolConditional(e)
		if !isBool {
			return nil, "a match that is not a two-armed Bool conditional", false
		}
		cond, reason, ok := lo.lowerCondition(e.Scrutinee)
		if !ok {
			return nil, reason, false
		}
		left, reason, okL := lo.lower(whenTrue, width)
		if !okL {
			return nil, reason, false
		}
		right, reason, okR := lo.lower(whenFalse, width)
		if !okR {
			return nil, reason, false
		}
		return iteTerm(cond, left, right), "", true
	}
	return nil, fmt.Sprintf("%T", expr), false
}

// lowerCondition lowers a Bool condition — a comparison, or comparisons
// joined by && and || — to a 0/1 term. Oak's && and || short-circuit, but
// over pure comparisons of parameters evaluation order is unobservable, so
// the strict and/or is the same function.
func (lo *oakLowering) lowerCondition(expr ast.Expression) (*term, string, bool) {
	infix, isInfix := expr.(*ast.InfixExpression)
	if !isInfix {
		return nil, fmt.Sprintf("a condition that is not a comparison (%T)", expr), false
	}
	if infix.Operator == "&&" || infix.Operator == "||" {
		left, reason, okL := lo.lowerCondition(infix.Left)
		if !okL {
			return nil, reason, false
		}
		right, reason, okR := lo.lowerCondition(infix.Right)
		if !okR {
			return nil, reason, false
		}
		op := "and"
		if infix.Operator == "||" {
			op = "or"
		}
		return binaryTerm(op, truncate(left, 1), truncate(right, 1)), "", true
	}
	codes, isComparison := oakComparisons[infix.Operator]
	if !isComparison {
		return nil, fmt.Sprintf("condition operator %s", infix.Operator), false
	}
	width, signed, ok := lo.operandContract(infix)
	if !ok {
		return nil, "a comparison with no parameter operand (its width is unknown)", false
	}
	left, reason, okL := lo.lower(infix.Left, width)
	if !okL {
		return nil, reason, false
	}
	right, reason, okR := lo.lower(infix.Right, width)
	if !okR {
		return nil, reason, false
	}
	code := codes[0]
	if signed {
		code = codes[1]
	}
	return cmpTerm(code, left, right), "", true
}

// operandContract finds the width and signedness of a comparison from the
// parameters it mentions (Oak's type checker has already made both sides
// one type; the verifier only needs to read it off a parameter).
func (lo *oakLowering) operandContract(expr ast.Expression) (int, bool, bool) {
	switch e := expr.(type) {
	case *ast.Identifier:
		if local, isLocal := lo.locals[e.Value]; isLocal {
			return local.width, local.signed, true
		}
		if w, isParam := lo.params[e.Value]; isParam {
			return w, lo.signed[e.Value], true
		}
	case *ast.IndexExpression:
		if _, contract, isElem := lo.spanElement(e); isElem {
			return contract.elemWidth, contract.signed, true
		}
	case *ast.InfixExpression:
		if w, s, ok := lo.operandContract(e.Left); ok {
			return w, s, true
		}
		return lo.operandContract(e.Right)
	case *ast.InvocationExpression:
		if _, isLen := lo.spanLength(e); isLen {
			return 32, false, true
		}
		if len(e.Arguments) == 1 {
			return lo.operandContract(e.Arguments[0])
		}
	}
	return 0, false, false
}

// boolConditional recognizes the two-armed Bool match the front end
// produces for `cond ? a | b`: literal true/false patterns, or one literal
// and a trailing wildcard.
func boolConditional(match *ast.MatchExpression) (whenTrue, whenFalse ast.Expression, ok bool) {
	if match.Scrutinee == nil || len(match.Arms) != 2 {
		return nil, nil, false
	}
	for i, arm := range match.Arms {
		switch pattern := arm.Pattern.(type) {
		case *ast.LiteralPattern:
			boolLit, isBool := pattern.Value.(*ast.Boolean)
			if !isBool {
				return nil, nil, false
			}
			if boolLit.Value {
				whenTrue = arm.Body
			} else {
				whenFalse = arm.Body
			}
		case *ast.WildcardPattern:
			if i != 1 {
				return nil, nil, false
			}
			if whenTrue == nil {
				whenTrue = arm.Body
			} else {
				whenFalse = arm.Body
			}
		default:
			return nil, nil, false
		}
	}
	return whenTrue, whenFalse, whenTrue != nil && whenFalse != nil
}

// --- witnesses -----------------------------------------------------------

// witnessInputs is the deterministic evaluation set: boundary values and a
// seeded generator, at full width, over every parameter.
func witnessInputs(params []string, widths map[string]int) []map[string]uint64 {
	var inputs []map[string]uint64
	boundary := func(w int) []uint64 {
		m := mask(w)
		return []uint64{0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 127, 128, 255, 256, m - 1, m, m >> 1, (m >> 1) + 1}
	}
	if len(params) == 0 {
		return []map[string]uint64{{}}
	}
	first := boundary(widths[params[0]])
	for _, a := range first {
		if len(params) == 1 {
			inputs = append(inputs, map[string]uint64{params[0]: a})
			continue
		}
		for _, b := range boundary(widths[params[1]]) {
			env := map[string]uint64{params[0]: a, params[1]: b}
			for _, extra := range params[2:] {
				env[extra] = a ^ b
			}
			inputs = append(inputs, env)
		}
	}
	seed := uint64(0x9E3779B97F4A7C15)
	for i := 0; i < 256; i++ {
		env := map[string]uint64{}
		for _, name := range params {
			seed ^= seed << 13
			seed ^= seed >> 7
			seed ^= seed << 17
			env[name] = seed & mask(widths[name])
		}
		inputs = append(inputs, env)
	}
	return inputs
}

// Verify checks one asm function against its Oak fallback body.
func Verify(fn *Function, sig *ast.FunctionStatement, oakBody ast.Expression) Verdict {
	asmTerm, reason, ok := executeBody(fn, sig)
	if !ok {
		return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (%s) — trusted per docs/spec/94-assembler.md §5", fn.Name, reason)}
	}
	lowering := &oakLowering{params: map[string]int{}, signed: map[string]bool{}, spans: map[string]spanContract{}}
	for _, param := range sig.Parameters {
		if elem, _, isSpan := spanShape(param.Type); isSpan {
			elemType := typeText(param.Type.(*ast.IndexExpression).Left)
			lowering.spans[param.Name.Value] = spanContract{elemWidth: int(elem) * 8, signed: strings.HasPrefix(elemType, "i")}
			continue
		}
		class, _ := contractClass(param.Type)
		lowering.params[param.Name.Value] = widthOf(class)
		lowering.signed[param.Name.Value] = strings.HasPrefix(typeText(param.Type), "i")
	}
	resultClass, _ := contractClass(sig.ReturnType)
	width := widthOf(resultClass)
	oakTerm, reason, ok := lowering.lower(oakBody, width)
	if !ok {
		return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (the Oak body contains %s) — trusted per docs/spec/94-assembler.md §5", fn.Name, reason)}
	}
	asmTerm = truncate(asmTerm, width)

	// The unknowns are every parameter either side mentions: scalars, span
	// lengths, span elements, and span bases — at the width each is
	// declared (a span element's width is its element type's).
	mentioned := map[string]bool{}
	collectParams(asmTerm, mentioned)
	collectParams(oakTerm, mentioned)
	params := map[string]int{}
	names := make([]string, 0, len(mentioned))
	for name := range mentioned {
		names = append(names, name)
		params[name] = lowering.declaredWidth(name)
	}
	sort.Strings(names)

	// Witnesses first: a disagreement is a definite mismatch regardless of
	// what normalization would say.
	for _, env := range witnessInputs(names, params) {
		got := asmTerm.eval(env)
		want := oakTerm.eval(env)
		if got != want {
			return Verdict{Kind: VerdictMismatch, Message: fmt.Sprintf("asm unit %s disagrees with its Oak body at %s: asm yields %d, Oak yields %d (asm term %s; Oak term %s)", fn.Name, describeEnv(names, env), got, want, asmTerm, oakTerm)}
		}
	}
	if a, o := asmTerm.linearAt(width), oakTerm.linearAt(width); a != nil && o != nil && a.equal(o) {
		return Verdict{Kind: VerdictProven, Message: fmt.Sprintf("asm unit %s: proven equal to its Oak body (linear normal form %s)", fn.Name, a)}
	}

	// Beyond the linear form: bit-blast both sides. Equal canonical nodes
	// for every bit is a proof at the bit level; a differing bit gives a
	// concrete counterexample; exceeding the node budget keeps the labeled
	// evidence verdict.
	bl := newBlaster(names, params)
	asmBits := bl.blast(asmTerm)
	oakBits := bl.blast(oakTerm)
	if asmBits == nil || oakBits == nil || bl.bdd.exceeded {
		return Verdict{Kind: VerdictWitnessed, Message: fmt.Sprintf("asm unit %s: agrees with its Oak body on every witness input (evidence, not proof: the bit-level decision exceeded its node budget)", fn.Name)}
	}
	for i := 0; i < width; i++ {
		if asmBits[i] != oakBits[i] {
			env := bl.counterexample(asmBits[i], oakBits[i])
			return Verdict{Kind: VerdictMismatch, Message: fmt.Sprintf("asm unit %s disagrees with its Oak body at %s (bit %d differs): asm yields %d, Oak yields %d (asm term %s; Oak term %s)", fn.Name, describeEnv(names, env), i, asmTerm.eval(env), oakTerm.eval(env), asmTerm, oakTerm)}
		}
	}
	return Verdict{Kind: VerdictProven, Message: fmt.Sprintf("asm unit %s: proven equal to its Oak body at the bit level (%d-bit result, %d BDD nodes)", fn.Name, width, len(bl.bdd.nodes))}
}

// collectParams gathers every parameter name a term mentions. Widths come
// from the declaration (declaredWidth), never from the use: truncation and
// zero-extension copy a parameter node at the use width while the value
// stays bounded by its declared width.
func collectParams(t *term, into map[string]bool) {
	if t == nil {
		return
	}
	switch t.kind {
	case termParam:
		into[t.name] = true
		return
	case termConst:
		return
	}
	collectParams(t.cond, into)
	collectParams(t.left, into)
	collectParams(t.right, into)
}

// declaredWidth is the width a parameter's values are bounded by: a scalar
// parameter's contract width, 64 for a span base, 32 for a span length, the
// element width for a span element.
func (lo *oakLowering) declaredWidth(name string) int {
	if w, isScalar := lo.params[name]; isScalar {
		return w
	}
	if strings.HasPrefix(name, "&") {
		return 64
	}
	if strings.HasPrefix(name, "len(") {
		return 32
	}
	if bracket := strings.IndexByte(name, '['); bracket > 0 {
		if contract, isSpan := lo.spans[name[:bracket]]; isSpan {
			return contract.elemWidth
		}
	}
	return 64
}

func describeEnv(names []string, env map[string]uint64) string {
	parts := make([]string, 0, len(names))
	for _, name := range names {
		parts = append(parts, fmt.Sprintf("%s=%d", name, env[name]))
	}
	return strings.Join(parts, ", ")
}
