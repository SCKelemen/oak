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
)

// term is a fixed-width bitvector expression. Width is 32 or 64.
type term struct {
	kind  termKind
	width int
	name  string // termParam
	value uint64 // termConst (already masked to width)
	op    string // termBinary: add sub and or xor shl shr
	left  *term
	right *term
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
	return &term{kind: termBinary, width: left.width, op: op, left: left, right: right}
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
	regs map[int]*term // physical register -> 64-bit term
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
	}
	// The narrow computation's wrap is preserved by masking to its width.
	return &term{kind: termBinary, width: width, op: "and", left: t, right: constTerm(mask(t.width), width)}
}

var verifiableOps = map[string]string{"add": "add", "sub": "sub", "and": "and", "orr": "or", "eor": "xor", "lsl": "shl", "lsr": "shr"}

// executeStraightLine symbolically executes the body; reports (result
// term, "", true) or ("", reason, false) when the body is outside the
// verified subset.
func executeStraightLine(fn *Function, sig *ast.FunctionStatement) (*term, string, bool) {
	state := &symbolicState{regs: map[int]*term{}}
	params := map[string]RegClass{}
	for _, param := range sig.Parameters {
		class, ok := contractClass(param.Type)
		if !ok || class == ClassV {
			return nil, "vector or non-integer parameters", false
		}
		params[param.Name.Value] = class
	}
	for _, binding := range fn.Bindings {
		if binding.Length != nil {
			return nil, "span parameters (memory)", false
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
	for _, item := range fn.Items {
		instr, ok := item.(Instruction)
		if !ok {
			return nil, "labels or alignment directives", false
		}
		switch instr.Mnemonic {
		case "ret":
			result, ok := state.read(Register{Class: resultClass, Num: 0})
			if !ok {
				return nil, "result register never written", false
			}
			return result, "", true
		case "mov":
			dest := instr.Operands[0].(Register)
			value, ok := operandTerm(state, instr.Operands[1], widthOf(dest.Class))
			if !ok {
				return nil, "unbound register read", false
			}
			state.write(dest, value)
		default:
			op, verifiable := verifiableOps[instr.Mnemonic]
			if !verifiable || len(instr.Operands) != 3 {
				return nil, fmt.Sprintf("instruction %s", instr.Mnemonic), false
			}
			dest := instr.Operands[0].(Register)
			if dest.Class == ClassSP {
				return nil, "stack pointer arithmetic", false
			}
			left, okL := operandTerm(state, instr.Operands[1], widthOf(dest.Class))
			right, okR := operandTerm(state, instr.Operands[2], widthOf(dest.Class))
			if !okL || !okR {
				return nil, "unbound register read", false
			}
			state.write(dest, binaryTerm(op, left, right))
		}
	}
	return nil, "no ret reached", false
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

// lowerOakExpression turns a pure expression over the parameters into a
// term of the result width; reports the construct it cannot express.
func lowerOakExpression(expr ast.Expression, params map[string]int, width int) (*term, string, bool) {
	switch e := expr.(type) {
	case *ast.Identifier:
		if w, isParam := params[e.Value]; isParam {
			return truncate(paramTerm(e.Value, w), width), "", true
		}
		return nil, fmt.Sprintf("identifier %s (not a parameter)", e.Value), false
	case *ast.IntegerLiteral:
		return constTerm(uint64(e.Value), width), "", true
	case *ast.InvocationExpression:
		// Primitive constructors over constants: u32(15).
		ident, isIdent := e.Function.(*ast.Identifier)
		if !isIdent || len(e.Arguments) != 1 {
			return nil, "a call", false
		}
		switch ident.Value {
		case "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64":
			return lowerOakExpression(e.Arguments[0], params, width)
		}
		return nil, fmt.Sprintf("call to %s", ident.Value), false
	case *ast.InfixExpression:
		op, ok := oakOps[e.Operator]
		if !ok {
			return nil, fmt.Sprintf("operator %s", e.Operator), false
		}
		left, reason, okL := lowerOakExpression(e.Left, params, width)
		if !okL {
			return nil, reason, false
		}
		right, reason, okR := lowerOakExpression(e.Right, params, width)
		if !okR {
			return nil, reason, false
		}
		if (op == "shl" || op == "shr") && right.kind != termConst {
			// Oak traps at the width; the machine wraps the count.
			return nil, "a non-constant shift count", false
		}
		return binaryTerm(op, left, right), "", true
	case *ast.BlockExpression:
		if e.Block == nil || len(e.Block.Statements) != 1 {
			return nil, "a block with statements", false
		}
		if stmt, isExpr := e.Block.Statements[0].(*ast.ExpressionStatement); isExpr {
			return lowerOakExpression(stmt.Expression, params, width)
		}
		return nil, "a block with statements", false
	}
	return nil, fmt.Sprintf("%T", expr), false
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
	asmTerm, reason, ok := executeStraightLine(fn, sig)
	if !ok {
		return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (%s) — trusted per docs/spec/94-assembler.md §5", fn.Name, reason)}
	}
	params := map[string]int{}
	var names []string
	for _, param := range sig.Parameters {
		class, _ := contractClass(param.Type)
		params[param.Name.Value] = widthOf(class)
		names = append(names, param.Name.Value)
	}
	resultClass, _ := contractClass(sig.ReturnType)
	width := widthOf(resultClass)
	oakTerm, reason, ok := lowerOakExpression(oakBody, params, width)
	if !ok {
		return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (the Oak body contains %s) — trusted per docs/spec/94-assembler.md §5", fn.Name, reason)}
	}
	asmTerm = truncate(asmTerm, width)

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
	return Verdict{Kind: VerdictWitnessed, Message: fmt.Sprintf("asm unit %s: agrees with its Oak body on every witness input (evidence, not proof: the terms are outside the linear normal form)", fn.Name)}
}

func describeEnv(names []string, env map[string]uint64) string {
	parts := make([]string, 0, len(names))
	for _, name := range names {
		parts = append(parts, fmt.Sprintf("%s=%d", name, env[name]))
	}
	return strings.Join(parts, ", ")
}
