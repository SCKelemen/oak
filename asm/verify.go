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
	"math/bits"
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
	termCmp    // a condition code over two operands; the value is 1 or 0
	termIte    // cond ? left : right
	termSelect // name[left]: a span element at a symbolic 32-bit index
)

// selectTerm is the element of span at index: a constant index is the
// element parameter v[k]; a symbolic one is a select node, evaluated
// through the fixed element-content function and blasted as an
// uninterpreted value shared by selects with the same index.
func selectTerm(span string, index *term, width int) *term {
	if index.kind == termConst {
		return paramTerm(spanElemName(span, int64(index.value&mask(32))), width)
	}
	return &term{kind: termSelect, width: width, name: span, left: truncate(index, 32)}
}

// elementValue is the witness evaluator's fixed memory: element k of span
// name, a deterministic mix so that v[k] and v[i] agree whenever i = k.
func elementValue(span string, k uint64, width int) uint64 {
	h := uint64(1469598103934665603)
	for i := 0; i < len(span); i++ {
		h = (h ^ uint64(span[i])) * 1099511628211
	}
	h ^= (k + 1) * 0x9E3779B97F4A7C15
	h ^= h >> 29
	h *= 0xBF58476D1CE4E5B9
	h ^= h >> 32
	return h & mask(width)
}

// elementParam decodes an element parameter name v[k].
func elementParam(name string) (span string, k uint64, ok bool) {
	open := strings.IndexByte(name, '[')
	if open <= 0 || !strings.HasSuffix(name, "]") {
		return "", 0, false
	}
	index, err := strconv.ParseUint(name[open+1:len(name)-1], 10, 64)
	if err != nil {
		return "", 0, false
	}
	return name[:open], index, true
}

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
// (Oak.AssemblerSemantics.Cond.holds). The flags come from a subtraction
// (`cmp`/`subs`: the flags of left - right) or, when the code carries the
// `add:` prefix, from an addition (`adds`: the flags of left + right): N is
// the result's sign, Z its zero test, C the carry out (for a subtraction,
// "no borrow"), V the signed overflow. Every code reads those four bits.
var verifiableConditions = map[string]bool{"eq": true, "ne": true, "hs": true, "cs": true, "lo": true, "cc": true, "hi": true, "ls": true, "ge": true, "lt": true, "gt": true, "le": true, "mi": true, "pl": true, "vs": true, "vc": true}

// negatedCondition is the code that holds exactly when its argument does not.
var negatedCondition = map[string]string{"eq": "ne", "ne": "eq", "hs": "lo", "cs": "lo", "lo": "hs", "cc": "hs", "hi": "ls", "ls": "hi", "ge": "lt", "lt": "ge", "gt": "le", "le": "gt", "mi": "pl", "pl": "mi", "vs": "vc", "vc": "vs"}

// splitFlagsKind separates the `add:` prefix from a condition code.
func splitFlagsKind(code string) (add bool, bare string) {
	if strings.HasPrefix(code, "add:") {
		return true, code[4:]
	}
	return false, code
}

func conditionHolds(code string, left, right uint64, width int) bool {
	add, bare := splitFlagsKind(code)
	m := mask(width)
	l, r := left&m, right&m
	top := uint(width - 1)
	var result uint64
	var c bool
	if add {
		sum, carry := bits.Add64(l, r, 0)
		result = sum & m
		if width < 64 {
			c = sum>>uint(width)&1 == 1
		} else {
			c = carry == 1
		}
	} else {
		result = (l - r) & m
		c = l >= r // no borrow
	}
	n := result>>top&1 == 1
	z := result == 0
	lm, rm, resm := l>>top&1, r>>top&1, result>>top&1
	var v bool
	if add {
		v = lm == rm && resm != lm
	} else {
		v = lm != rm && resm != lm
	}
	return conditionFromFlags(bare, n, z, c, v)
}

// conditionFromFlags is the ARM condition table.
func conditionFromFlags(code string, n, z, c, v bool) bool {
	switch code {
	case "eq":
		return z
	case "ne":
		return !z
	case "hs", "cs":
		return c
	case "lo", "cc":
		return !c
	case "mi":
		return n
	case "pl":
		return !n
	case "vs":
		return v
	case "vc":
		return !v
	case "hi":
		return c && !z
	case "ls":
		return !c || z
	case "ge":
		return n == v
	case "lt":
		return n != v
	case "gt":
		return !z && n == v
	case "le":
		return z || n != v
	}
	return false
}

// flagsCondition is the condition term for a code read from the flags a
// cmp/subs (subtraction) or adds (addition) produced.
func flagsCondition(code string, flags *flagsFact) *term {
	if flags.add {
		code = "add:" + code
	}
	return cmpTerm(code, flags.left, flags.right)
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
	// Additive identities: x + 0, x - 0, 0 + x are x (at the same width).
	if right.kind == termConst && right.value == 0 && (op == "add" || op == "sub") && left.width == t.width {
		return left
	}
	if left.kind == termConst && left.value == 0 && op == "add" && right.width == t.width {
		return right
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
		if value, bound := env[t.name]; bound {
			return value & m
		}
		// An element parameter outside the witness environment reads the
		// fixed memory, consistently with symbolic selects.
		if span, k, isElement := elementParam(t.name); isElement {
			return elementValue(span, k, t.width) & m
		}
		return 0
	case termConst:
		return t.value & m
	case termSelect:
		return elementValue(t.name, t.left.eval(env)&mask(32), t.width) & m
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
	case termSelect:
		return fmt.Sprintf("%s[%s]", t.name, t.left)
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
	case termCmp, termIte, termSelect:
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
}

// flagsFact records what produced the flags: cmp/subs leave NZCV as the
// flags of `left - right` at width, which every condition code reads as a
// comparison of the two operands. adds sets flags the comparison reading
// does not describe (unknown).
type flagsFact struct {
	left, right *term
	width       int
	add         bool // adds: the flags of left + right rather than left - right
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
func executeBody(fn *Function, sig *ast.FunctionStatement, concrete map[string]uint64) (*term, *pathExecutor, string, bool) {
	state := &symbolicState{regs: map[int]*term{}}
	params := map[string]RegClass{}
	spans := map[string]int64{} // span/view parameter -> element size in bytes
	declared := map[string]int{}
	for _, param := range sig.Parameters {
		if elem, _, isSpan := spanShape(param.Type); isSpan {
			spans[param.Name.Value] = elem
			declared[spanLenName(param.Name.Value)] = 32
			declared[spanBaseName(param.Name.Value)] = 64
			continue
		}
		class, ok := contractClass(param.Type)
		if !ok || class == ClassV {
			return nil, nil, "vector or non-integer parameters", false
		}
		params[param.Name.Value] = class
		declared[param.Name.Value] = widthOf(class)
	}
	// input is a parameter's entry term: symbolic, or the witness value in
	// a concrete run (which is what lets a data-dependent loop unroll).
	input := func(name string, width int) *term {
		if value, isConcrete := concrete[name]; isConcrete {
			return constTerm(value, width)
		}
		return paramTerm(name, width)
	}
	for _, binding := range fn.Bindings {
		if binding.Length != nil {
			// A span arrives as its {base, len} pair: the base is the opaque
			// address term `&v` (memory through it resolves to element
			// parameters), the length the 32-bit parameter len(v).
			if _, isSpan := spans[binding.Param]; !isSpan {
				return nil, nil, "span binding of a non-span parameter", false
			}
			state.regs[binding.Register.Num] = paramTerm(spanBaseName(binding.Param), 64)
			state.regs[binding.Length.Num] = zeroExtend(input(spanLenName(binding.Param), 32), 64)
			continue
		}
		class := params[binding.Param]
		state.regs[binding.Register.Num] = zeroExtend(input(binding.Param, widthOf(class)), 64)
		if class == ClassX {
			state.regs[binding.Register.Num] = input(binding.Param, 64)
		}
	}
	resultClass, hasResult := contractClass(sig.ReturnType)
	if !hasResult || resultClass == ClassV {
		return nil, nil, "no integer result", false
	}
	labels := map[string]int{}
	for index, item := range fn.Items {
		switch it := item.(type) {
		case Label:
			labels[it.Name] = index
		case Align:
			return nil, nil, "alignment directives", false
		}
	}
	exec := &pathExecutor{items: fn.Items, labels: labels, resultClass: resultClass, spans: spans, declared: declared, concrete: concrete != nil}
	exec.loopExits = findLoops(fn.Items, labels)
	result, reason, ok := exec.run(0, state)
	return result, exec, reason, ok
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
	declared    map[string]int   // parameter -> declared width
	concrete    bool             // a witness run: every input is a constant
	loopExits   map[int]loopShape
	loops       []*loopEvent // data-dependent loops met, in creation order
	loopStack   []int        // indices of the loops whose bodies are being executed
	paths       int
	steps       int
}

func (s *symbolicState) clone() *symbolicState {
	regs := make(map[int]*term, len(s.regs))
	for reg, value := range s.regs {
		regs[reg] = value
	}
	return &symbolicState{regs: regs, flags: s.flags}
}

// run executes from item index pc to a ret on every path.
func (x *pathExecutor) run(pc int, state *symbolicState) (*term, string, bool) {
	x.paths++
	if x.paths > pathBudget {
		return nil, "more paths than the verifier's budget (a loop whose trip count depends on the inputs, or too many forks)", false
	}
	for ; pc < len(x.items); pc++ {
		instr, isInstr := x.items[pc].(Instruction)
		if !isInstr {
			continue // a label is a position
		}
		x.steps++
		if x.steps > stepBudget {
			return nil, "more instructions than the verifier's unrolling budget (a loop whose trip count depends on the inputs)", false
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
			pc = target - 1 // backward: a loop, bounded by the budgets
			continue
		case "b.", "cbz", "cbnz", "tbz", "tbnz":
			cond, reason, ok := branchCondition(instr, state)
			if !ok {
				return nil, reason, false
			}
			target, ok := x.labels[instr.Operands[len(instr.Operands)-1].(Symbol).Name]
			if !ok {
				return nil, "a branch to an unknown label", false
			}
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
			// The exit branch of a recognized loop with an undecided
			// condition: a data-dependent loop, summarized as a loop event
			// and continued past its exit on fresh loop-carried symbols.
			if shape, isLoopExit := x.loopExits[pc]; isLoopExit {
				return x.loopEvent(shape, instr, state)
			}
			// Any other undecided branch forks; backward or forward alike —
			// an unrecognized loop unfolds until the budgets stop it.
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
	if mem.Index != nil {
		// [base, wI, uxtw #s]: element wI. Along an unrolled counted loop the
		// index register is a constant on every iteration; a data-dependent
		// index names no single element.
		if int64(1)<<uint(mem.Shift) != elem {
			return "an indexed load whose scale is not the element size", false
		}
		index, ok := state.read(*mem.Index)
		if !ok {
			return "unbound register read", false
		}
		state.write(dest, x.element(param, index, widthOf(dest.Class)))
		return "", true
	}
	if mem.Offset < 0 || mem.Offset%elem != 0 {
		return "a load not aligned to an element", false
	}
	state.write(dest, x.element(param, constTerm(uint64(mem.Offset/elem), 32), widthOf(dest.Class)))
	return "", true
}

// element is the span element at an index term; in a concrete run the
// witness memory's value.
func (x *pathExecutor) element(span string, index *term, width int) *term {
	if x.concrete && index.kind == termConst {
		return constTerm(elementValue(span, index.value&mask(32), width), width)
	}
	return selectTerm(span, index, width)
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
			cond := flagsCondition(code, state.flags)
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
				state.flags = &flagsFact{left: left, right: right, width: widthOf(dest.Class), add: true}
			}
			state.write(dest, binaryTerm(op, left, right))
		}
	}
	return "", true
}

// branchCondition is the taken-condition of a conditional branch: b.cond
// reads the flags; cbz/cbnz compare a register with zero; tbz/tbnz test one
// bit (Oak.AssemblerSemantics.cbz, tbz).
func branchCondition(instr Instruction, state *symbolicState) (*term, string, bool) {
	switch instr.Mnemonic {
	case "b.":
		if state.flags == nil || state.flags.unknown {
			return nil, "b.cond reading flags no cmp/subs/adds produced", false
		}
		if !verifiableConditions[instr.Cond] {
			return nil, fmt.Sprintf("condition code %s", instr.Cond), false
		}
		return flagsCondition(instr.Cond, state.flags), "", true
	case "cbz", "cbnz":
		reg := instr.Operands[0].(Register)
		value, ok := state.read(reg)
		if !ok {
			return nil, "unbound register read", false
		}
		code := "eq"
		if instr.Mnemonic == "cbnz" {
			code = "ne"
		}
		return cmpTerm(code, value, constTerm(0, widthOf(reg.Class))), "", true
	case "tbz", "tbnz":
		reg := instr.Operands[0].(Register)
		value, ok := state.read(reg)
		if !ok {
			return nil, "unbound register read", false
		}
		bit := instr.Operands[1].(Immediate).Value
		width := widthOf(reg.Class)
		if bit < 0 || bit >= int64(width) {
			return nil, "a bit test past the register width", false
		}
		code := "eq"
		if instr.Mnemonic == "tbnz" {
			code = "ne"
		}
		masked := binaryTerm("and", value, constTerm(uint64(1)<<uint(bit), width))
		return cmpTerm(code, masked, constTerm(0, width)), "", true
	}
	return nil, fmt.Sprintf("instruction %s", instr.Mnemonic), false
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
	params    map[string]int
	signed    map[string]bool
	spans     map[string]spanContract
	locals    map[string]*oakLocal // statement-body locals, in declaration scope
	concrete  map[string]uint64    // a witness run: parameters are these constants
	loops     []*loopEvent         // data-dependent loops met, in creation order
	loopStack []int                // indices of the loops whose bodies are being lowered
	fresh     map[string]int       // loop-carried fresh symbols -> width
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
				// A statement-level conditional: `c ? { x = e } | { }`.
				if match, isMatch := s.Expression.(*ast.MatchExpression); isMatch {
					if reason, ok := lo.lowerConditionalStatement(match); !ok {
						return nil, reason, false
					}
					continue
				}
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
			// Data-dependent: summarize the loop once and continue after it
			// on fresh loop-carried symbols.
			return lo.loopEvent(loop)
		}
		if cond.value == 0 {
			return "", true
		}
		if reason, ok := lo.lowerLoopBody(loop.Body); !ok {
			return reason, false
		}
	}
}

// lowerLoopBody executes one iteration of a loop body.
func (lo *oakLowering) lowerLoopBody(body *ast.BlockStatement) (string, bool) {
	for _, stmt := range body.Statements {
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
		case *ast.VariableDeclaration:
			// A body-local (the inner loop's counter), redeclared each iteration.
			if s.Value == nil || s.Type == nil {
				return "a local without both a type and an initializer", false
			}
			w, signed, ok := scalarType(s.Type)
			if !ok {
				return fmt.Sprintf("a local of type %s", typeText(s.Type)), false
			}
			value, reason, ok := lo.lower(s.Value, w)
			if !ok {
				return reason, false
			}
			lo.locals[s.Name.Value] = &oakLocal{value: value, width: w, signed: signed}
		case *ast.ExpressionStatement:
			match, isMatch := s.Expression.(*ast.MatchExpression)
			if !isMatch {
				return "an expression statement in a loop body", false
			}
			if reason, ok := lo.lowerConditionalStatement(match); !ok {
				return reason, false
			}
		default:
			return fmt.Sprintf("%T in a loop body", stmt), false
		}
	}
	return "", true
}

// lowerConditionalStatement executes `cond ? { ... } | { ... }` in
// statement position: each arm runs on a snapshot of the locals, and every
// local either arm assigns becomes a select on the condition — the
// statement-level counterpart of the value-position conditional, and of a
// branch that rejoins inside an asm loop body.
func (lo *oakLowering) lowerConditionalStatement(match *ast.MatchExpression) (string, bool) {
	whenTrue, whenFalse, isBool := boolConditional(match)
	if !isBool {
		return "a statement-level match that is not a two-armed Bool conditional", false
	}
	cond, reason, ok := lo.lowerCondition(match.Scrutinee)
	if !ok {
		return reason, false
	}
	before := lo.snapshotLocals()
	if reason, ok := lo.lowerArm(whenTrue); !ok {
		return reason, false
	}
	afterTrue := lo.snapshotLocals()
	lo.restoreLocals(before)
	if reason, ok := lo.lowerArm(whenFalse); !ok {
		return reason, false
	}
	for name, local := range lo.locals {
		t, f := afterTrue[name], local.value
		if t != f {
			local.value = iteTerm(truncate(cond, 1), t, f)
		}
	}
	return "", true
}

// lowerArm executes a conditional arm as statements: a block of
// assignments (possibly empty), or nothing.
func (lo *oakLowering) lowerArm(arm ast.Expression) (string, bool) {
	block, isBlock := arm.(*ast.BlockExpression)
	if !isBlock {
		return "a conditional arm in statement position that is not a block", false
	}
	if block.Block == nil {
		return "", true
	}
	return lo.lowerLoopBody(block.Block)
}

func (lo *oakLowering) snapshotLocals() map[string]*term {
	out := make(map[string]*term, len(lo.locals))
	for name, local := range lo.locals {
		out[name] = local.value
	}
	return out
}

func (lo *oakLowering) restoreLocals(values map[string]*term) {
	for name, value := range values {
		lo.locals[name].value = value
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
	k, isConst := lo.constantIndexValue(index.Index)
	if !isConst || k < 0 {
		return "", spanContract{}, false
	}
	return spanElemName(ident.Value, k), contract, true
}

// spanElementTerm lowers v[e] over a span parameter with any index
// expression: a constant index is the element parameter, a symbolic one a
// select (the loop-carried counter of a data-dependent loop).
func (lo *oakLowering) spanElementTerm(index *ast.IndexExpression) (*term, spanContract, string, bool) {
	if name, contract, isConst := lo.spanElement(index); isConst {
		if lo.concrete != nil {
			_, k, _ := elementParam(name)
			return constTerm(elementValue(index.Left.(*ast.Identifier).Value, k, contract.elemWidth), contract.elemWidth), contract, "", true
		}
		return paramTerm(name, contract.elemWidth), contract, "", true
	}
	ident, isIdent := index.Left.(*ast.Identifier)
	if !isIdent || index.Dot {
		return nil, spanContract{}, "an index that is not into a span parameter", false
	}
	contract, isSpan := lo.spans[ident.Value]
	if !isSpan {
		return nil, spanContract{}, fmt.Sprintf("an index into %s (not a span parameter)", ident.Value), false
	}
	idx, reason, ok := lo.lower(index.Index, 32)
	if !ok {
		return nil, spanContract{}, reason, false
	}
	if lo.concrete != nil && idx.kind == termConst {
		return constTerm(elementValue(ident.Value, idx.value, contract.elemWidth), contract.elemWidth), contract, "", true
	}
	return selectTerm(ident.Value, idx, contract.elemWidth), contract, "", true
}

// constantIndexValue reads a constant index: a literal, a primitive
// constructor over one, or a local whose value has folded to a constant
// (the counter of an unrolled loop).
func (lo *oakLowering) constantIndexValue(expr ast.Expression) (int64, bool) {
	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		return e.Value, true
	case *ast.Identifier:
		if local, isLocal := lo.locals[e.Value]; isLocal && local.value.kind == termConst {
			return int64(local.value.value), true
		}
	case *ast.InvocationExpression:
		if ident, isIdent := e.Function.(*ast.Identifier); isIdent && len(e.Arguments) == 1 {
			switch ident.Value {
			case "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64":
				return lo.constantIndexValue(e.Arguments[0])
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
			if value, isConcrete := lo.concrete[e.Value]; isConcrete {
				return constTerm(value&mask(w), width), "", true
			}
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
		element, _, reason, ok := lo.spanElementTerm(e)
		if !ok {
			return nil, reason, false
		}
		return adaptWidth(element, width), "", true
	case *ast.InvocationExpression:
		if name, isLen := lo.spanLength(e); isLen {
			if value, isConcrete := lo.concrete[name]; isConcrete {
				return constTerm(value, width), "", true
			}
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
		if ident, isIdent := e.Left.(*ast.Identifier); isIdent && !e.Dot {
			if contract, isSpan := lo.spans[ident.Value]; isSpan {
				return contract.elemWidth, contract.signed, true
			}
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
	asmTerm, exec, reason, ok := executeBody(fn, sig, nil)
	if !ok {
		return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (%s) — trusted per docs/spec/94-assembler.md §5", fn.Name, reason)}
	}
	lowering := newLowering(sig)
	resultClass, _ := contractClass(sig.ReturnType)
	width := widthOf(resultClass)
	oakTerm, reason, ok := lowering.lower(oakBody, width)
	if !ok {
		return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (the Oak body contains %s) — trusted per docs/spec/94-assembler.md §5", fn.Name, reason)}
	}
	if len(exec.loops) > 0 || len(lowering.loops) > 0 {
		return verifyLoops(fn, sig, oakBody, exec, lowering, asmTerm, oakTerm, width)
	}
	return decideEqual(fn, lowering, asmTerm, oakTerm, width, "")
}

// newLowering builds the Oak-side contract from the signature.
func newLowering(sig *ast.FunctionStatement) *oakLowering {
	lowering := &oakLowering{params: map[string]int{}, signed: map[string]bool{}, spans: map[string]spanContract{}, fresh: map[string]int{}}
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
	return lowering
}

// decideEqual is the equality decision for two lowered terms: witnesses,
// the linear normal form, then the bit level. note is appended to a proof.
func decideEqual(fn *Function, lowering *oakLowering, asmTerm, oakTerm *term, width int, note string) Verdict {
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
		return Verdict{Kind: VerdictProven, Message: fmt.Sprintf("asm unit %s: proven equal to its Oak body (linear normal form %s)%s", fn.Name, a, note)}
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
	return Verdict{Kind: VerdictProven, Message: fmt.Sprintf("asm unit %s: proven equal to its Oak body at the bit level (%d-bit result, %d BDD nodes)%s", fn.Name, width, len(bl.bdd.nodes), note)}
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
	if w, isFresh := lo.fresh[name]; isFresh {
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
