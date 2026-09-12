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
	"github.com/SCKelemen/oak/typechecker"
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
func splitFlagsKind(code string) (kind string, bare string) {
	if colon := strings.IndexByte(code, ':'); colon > 0 {
		return code[:colon], code[colon+1:]
	}
	return "", code
}

func conditionHolds(code string, left, right uint64, width int) bool {
	kind, bare := splitFlagsKind(code)
	m := mask(width)
	l, r := left&m, right&m
	top := uint(width - 1)
	var result uint64
	var c, v bool
	lm, rm := l>>top&1, r>>top&1
	switch kind {
	case "add":
		sum, carry := bits.Add64(l, r, 0)
		result = sum & m
		if width < 64 {
			c = sum>>uint(width)&1 == 1
		} else {
			c = carry == 1
		}
		v = lm == rm && result>>top&1 != lm
	case "and":
		result = l & r // tst: C and V are cleared
	default:
		result = (l - r) & m
		c = l >= r // no borrow
		v = lm != rm && result>>top&1 != lm
	}
	n := result>>top&1 == 1
	z := result == 0
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
	bare := code
	if flags.kind != "" {
		code = flags.kind + ":" + code
	}
	compared := cmpTerm(code, flags.left, flags.right)
	if flags.cond == nil {
		return compared
	}
	// ccmp: under the prior condition the flags are the comparison's,
	// otherwise the immediate pattern N=bit3 Z=bit2 C=bit1 V=bit0.
	imm := flags.elseNZCV
	otherwise := conditionFromFlags(bare, imm>>3&1 == 1, imm>>2&1 == 1, imm>>1&1 == 1, imm&1 == 1)
	other := constTerm(0, compared.width)
	if otherwise {
		other = constTerm(1, compared.width)
	}
	return iteTerm(flags.cond, compared, other)
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
// eval computes the term for a parameter assignment (Oak.AssemblerSemantics
// transliterated: every operation is total and wraps to the width). Shared
// subterms are evaluated once per call.
func (t *term) eval(env map[string]uint64) uint64 {
	return t.evalMemo(env, map[*term]uint64{})
}

func (t *term) evalMemo(env map[string]uint64, memo map[*term]uint64) uint64 {
	if cached, seen := memo[t]; seen {
		return cached
	}
	value := t.evalUncached(env, memo)
	memo[t] = value
	return value
}

func (t *term) evalUncached(env map[string]uint64, memo map[*term]uint64) uint64 {
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
		return elementValue(t.name, t.left.evalMemo(env, memo)&mask(32), t.width) & m
	case termCmp:
		// The comparison happens at the operands' width; t.width is only
		// the width the 1/0 result is used at.
		if conditionHolds(t.op, t.left.evalMemo(env, memo), t.right.evalMemo(env, memo), t.left.width) {
			return 1
		}
		return 0
	case termIte:
		if t.cond.evalMemo(env, memo) != 0 {
			return t.left.evalMemo(env, memo) & m
		}
		return t.right.evalMemo(env, memo) & m
	}
	// Operands evaluate at their own widths (a mask node's inner term keeps
	// its width and modulus); the operation wraps to this term's width.
	l := t.left.evalMemo(env, memo) & m
	r := t.right.evalMemo(env, memo) & m
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
	case "sar":
		shift := uint(64 - t.width)
		return uint64(int64(l<<shift)>>shift>>(r%uint64(t.width))) & m
	case "mul":
		return (l * r) & m
	case "rev", "rev16", "rev32", "rbit", "clz", "cls", "cnt":
		return evalUnary(t.op, l, t.width) & m
	}
	if value, ok := evalBinaryExtra(t.op, l, r, t.width); ok {
		return value & m
	}
	return 0
}

// String prints a term for diagnostics, bounded: a DAG's expansion can be
// exponential in its depth, so the print stops after a few hundred nodes.
func (t *term) String() string {
	budget := 400
	return t.stringBounded(&budget)
}

func (t *term) stringBounded(budget *int) string {
	*budget--
	if *budget < 0 {
		return "…"
	}
	switch t.kind {
	case termParam:
		return t.name
	case termConst:
		return fmt.Sprintf("%d", t.value)
	case termCmp:
		return fmt.Sprintf("(%s %s %s)", t.left.stringBounded(budget), t.op, t.right.stringBounded(budget))
	case termIte:
		return fmt.Sprintf("(%s ? %s : %s)", t.cond.stringBounded(budget), t.left.stringBounded(budget), t.right.stringBounded(budget))
	case termSelect:
		return fmt.Sprintf("%s[%s]", t.name, t.left.stringBounded(budget))
	}
	return fmt.Sprintf("(%s %s %s)", t.left.stringBounded(budget), t.op, t.right.stringBounded(budget))
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
	return t.linearAtMemo(w, map[*term]*linearForm{}, map[*term]bool{})
}

// linearAtMemo shares the normalization of shared subterms (terms are
// DAGs); seen records subterms already normalized, nil results included.
func (t *term) linearAtMemo(w int, memo map[*term]*linearForm, seen map[*term]bool) *linearForm {
	if seen[t] {
		return memo[t]
	}
	form := t.linearAtUncached(w, memo, seen)
	seen[t] = true
	memo[t] = form
	return form
}

func (t *term) linearAtUncached(w int, memo map[*term]*linearForm, seen map[*term]bool) *linearForm {
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
			return t.left.linearAtMemo(w, memo, seen)
		}
		if t.left.kind == termConst && t.left.value&m == m {
			return t.right.linearAtMemo(w, memo, seen)
		}
		return nil
	case "add", "sub":
		l, r := t.left.linearAtMemo(w, memo, seen), t.right.linearAtMemo(w, memo, seen)
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
	case "mul":
		// Scaling by a constant keeps the form linear.
		if t.width < w {
			return nil
		}
		variable, factor := t.left, t.right
		if variable.kind == termConst {
			variable, factor = t.right, t.left
		}
		if factor.kind != termConst {
			return nil
		}
		l := variable.linearAtMemo(w, memo, seen)
		if l == nil {
			return nil
		}
		out := &linearForm{width: w, coeffs: map[string]uint64{}, constant: (l.constant * factor.value) & m}
		for name, c := range l.coeffs {
			out.coeffs[name] = (c * factor.value) & m
		}
		return out.trim()
	case "shl":
		if t.right.kind != termConst || t.width < w {
			return nil
		}
		l := t.left.linearAtMemo(w, memo, seen)
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
	arch  string        // the lane: ArchArm64 or ArchRV64 (callee-saved numbering)
	regs  map[int]*term // physical register -> 64-bit term
	flags *flagsFact    // NZCV as the operands that produced them; nil until set
	// The frame: sp's displacement below its entry value (the seam checker
	// tracks the same number exactly) and the slots written so far, keyed
	// by entry-relative address. A load reads back exactly the term a store
	// of the same width put there; anything else is outside the subset.
	disp  int64
	frame map[int64]frameSlot
}

type frameSlot struct {
	value *term
	width int // bytes
}

// flagsFact records what produced the flags: cmp/subs leave NZCV as the
// flags of `left - right` at width, which every condition code reads as a
// comparison of the two operands. adds sets flags the comparison reading
// does not describe (unknown).
type flagsFact struct {
	left, right *term
	width       int
	kind        string // "" (cmp/subs: left - right), "add" (adds: left + right), "and" (tst: left & right)
	unknown     bool
	// ccmp: the comparison's flags when cond holds, else the immediate NZCV.
	cond     *term
	elseNZCV int64
}

func (s *symbolicState) read(reg Register) (*term, bool) {
	if reg.ZeroRegister() {
		return constTerm(0, widthOf(reg.Class)), true
	}
	value, ok := s.regs[reg.Num]
	if !ok && ((s.arch == ArchRV64 && rv64Preserved(reg.Num)) || (s.arch != ArchRV64 && calleeSavedRegister(reg.Num))) {
		// A callee-saved register carries the caller's value on entry: an
		// opaque symbol, which a save/restore pair round-trips unchanged.
		value = paramTerm(fmt.Sprintf("entry.x%d", reg.Num), 64)
		s.regs[reg.Num] = value
		ok = true
	}
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

var verifiableOps = map[string]string{"add": "add", "sub": "sub", "adds": "add", "subs": "sub", "and": "and", "orr": "or", "eor": "xor", "lsl": "shl", "lsr": "shr", "asr": "sar", "mul": "mul"}

// executeBody symbolically executes the body along every path; reports (result
// term, "", true) or ("", reason, false) when the body is outside the
// verified subset.
func executeBody(fn *Function, sig *ast.FunctionStatement, concrete map[string]uint64) (*term, *pathExecutor, string, bool) {
	state := &symbolicState{arch: fn.Arch, regs: map[int]*term{}}
	params := map[string]RegClass{}
	spans := map[string]int64{} // span/view parameter -> element size in bytes
	declared := map[string]int{}
	composites := map[string]compositeArg{}
	boolParams := map[string]bool{}
	// input is a parameter's entry term: symbolic, or the witness value in
	// a concrete run (which is what lets a data-dependent loop unroll).
	input := func(name string, width int) *term {
		if value, isConcrete := concrete[name]; isConcrete {
			return constTerm(value, width)
		}
		return paramTerm(name, width)
	}
	if fn.Arch == ArchRV64 {
		// The RV64 lane binds under the LP64 psABI (asm/rv64_verify.go).
		if reason, ok := bindRV64Params(fn, sig, state, input, spans, declared); !ok {
			return nil, nil, reason, false
		}
	}
	for _, param := range sig.Parameters {
		if fn.Arch == ArchRV64 {
			break
		}
		if comp, isComposite := fn.Composites[typeText(param.Type)]; isComposite && len(comp.Fields) > 0 {
			// A record or tagged union: its scalar leaves are the parameters
			// (p.f, p.a.x, p.buf[2], p.tag, p.Circle); it arrives as x-register
			// chunks assembled from them, or by reference to a copy.
			leaves, reason, ok := compositeLeaves(fn.Composites, typeText(param.Type), param.Name.Value, 0, nil)
			if !ok {
				return nil, nil, reason, false
			}
			for _, leaf := range leaves {
				declared[leaf.name] = leaf.width
			}
			composites[param.Name.Value] = compositeArg{leaves: leaves, size: comp.Size}
			continue
		}
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
		bits, _, _ := contractBits(param.Type)
		declared[param.Name.Value] = bits
		if typeText(param.Type) == "Bool" {
			// A Bool crosses the boundary as the C enum: an int holding 0 or
			// 1, every bit of the low word defined.
			boolParams[param.Name.Value] = true
		} else if bits < 32 {
			// AAPCS64 leaves the register bits above a narrow argument
			// unspecified: they are a fresh unknown the body must not depend on.
			declared[upperBitsName(param.Name.Value)] = 32 - bits
		}
	}
	for _, binding := range fn.Bindings {
		if fn.Arch == ArchRV64 {
			break
		}
		if cp, isComposite := composites[binding.Param]; isComposite {
			if cp.size > 16 {
				// By reference: loads through the base at a leaf's exact
				// offset and width read that leaf.
				state.regs[binding.Register.Num] = paramTerm(spanBaseName(binding.Param), 64)
				continue
			}
			state.regs[binding.Register.Num] = chunkTerm(cp.leaves, 0, input)
			if binding.Length != nil {
				state.regs[binding.Length.Num] = chunkTerm(cp.leaves, 1, input)
			}
			continue
		}
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
		bits := declared[binding.Param]
		switch {
		case class == ClassX:
			state.regs[binding.Register.Num] = input(binding.Param, 64)
		case boolParams[binding.Param]:
			state.regs[binding.Register.Num] = zeroExtend(input(binding.Param, 1), 64)
		case bits < 32:
			// The narrow value in the low bits, unspecified bits above it.
			low := zeroExtend(input(binding.Param, bits), 32)
			high := binaryTerm("shl", zeroExtend(input(upperBitsName(binding.Param), 32-bits), 32), constTerm(uint64(bits), 32))
			state.regs[binding.Register.Num] = zeroExtend(binaryTerm("or", high, low), 64)
		default:
			state.regs[binding.Register.Num] = zeroExtend(input(binding.Param, 32), 64)
		}
	}
	resultClass, hasResult := contractClass(sig.ReturnType)
	if comp, isComposite := fn.Composites[typeText(sig.ReturnType)]; isComposite && len(comp.Fields) > 0 {
		// A record result of one chunk comes back in x0; larger ones (two
		// chunks, or the area addressed by x8) are outside the subset.
		if comp.Size > 8 {
			return nil, nil, "a record result beyond one register chunk", false
		}
		resultClass, hasResult = ClassX, true
	}
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
	exec := &pathExecutor{items: fn.Items, labels: labels, resultClass: resultClass, spans: spans, declared: declared, concrete: concrete != nil, env: concrete, records: composites, arch: fn.Arch}
	exec.resultReg = Register{Class: resultClass, Num: 0}
	if fn.Arch == ArchRV64 {
		exec.resultReg = rv64ResultRegister
	}
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
	arch        string   // the lane
	resultReg   Register // the register ret delivers: w0/x0, or a0 on rv64
	resultClass RegClass
	spans       map[string]int64 // span parameter -> element size in bytes
	declared    map[string]int   // parameter -> declared width
	concrete    bool             // a witness run: every input is a constant
	loopExits   map[int]loopShape
	loops       []*loopEvent // data-dependent loops met, in creation order
	loopStack   []int        // indices of the loops whose bodies are being executed
	paths       int
	steps       int
	// records: record and union parameters by name (their leaves), env the
	// concrete inputs of a witness run (nil when symbolic).
	records map[string]compositeArg
	env     map[string]uint64
}

// compositeArg is a record or union parameter: its scalar leaves and size
// (chunks up to 16 bytes, by reference beyond).
type compositeArg struct {
	leaves []compositeLeaf
	size   int64
}

// compositeLeaf is one scalar member of a composite, named by its access
// path from the parameter (the Oak side spells the same names).
type compositeLeaf struct {
	name   string
	offset int64
	width  int
	signed bool
	// guards: the union tags that must hold for this leaf to be live (a
	// payload of a tagged union overlaps the other variants' payloads; in
	// memory only the active one is there).
	guards []leafGuard
}

type leafGuard struct {
	tag   string // the tag leaf's name
	value int64
}

// guarded selects the leaf's term when every guarding tag holds, zero
// otherwise (the value the other variants' bytes take in the model and in
// constructed values).
func (leaf compositeLeaf) guarded(t *term, tagTerm func(name string) *term) *term {
	for _, guard := range leaf.guards {
		cond := truncate(cmpTerm("eq", tagTerm(guard.tag), constTerm(uint64(guard.value), 32)), 1)
		t = iteTerm(cond, t, constTerm(0, t.width))
	}
	return t
}

// compositeLeaves flattens a composite type (asm.Function.Composites) into
// its scalar leaves at their offsets: fields, nested composites, array
// elements. Bool fields (the 4-byte C enum whose upper bits the model
// cannot constrain) and floating-point fields are outside the subset.
func compositeLeaves(comps map[string]Composite, typeName, prefix string, base int64, guards []leafGuard) ([]compositeLeaf, string, bool) {
	comp, known := comps[typeName]
	if !known {
		return nil, fmt.Sprintf("the composite %s (no layout)", typeName), false
	}
	var out []compositeLeaf
	for _, field := range comp.Fields {
		at := base + field.Offset
		fieldGuards := guards
		if comp.Variants != nil && field.Name != "tag" {
			fieldGuards = append(append([]leafGuard{}, guards...), leafGuard{tag: prefix + ".tag", value: comp.Variants[field.Name]})
		}
		switch {
		case field.Scalar != "":
			// A Bool field is the 4-byte C enum holding 0 or 1: a 1-bit leaf
			// whose zero-extension is the field's whole word.
			width, signed, ok := contractBits(&ast.Identifier{Value: field.Scalar})
			if !ok || (int64(width) != field.Size*8 && field.Scalar != "Bool") {
				return nil, fmt.Sprintf("a field of type %s at the boundary", field.Scalar), false
			}
			out = append(out, compositeLeaf{name: prefix + "." + field.Name, offset: at, width: width, signed: signed, guards: fieldGuards})
		case field.Type != "":
			nested, reason, ok := compositeLeaves(comps, field.Type, prefix+"."+field.Name, at, fieldGuards)
			if !ok {
				return nil, reason, false
			}
			out = append(out, nested...)
		case field.Length > 0:
			stride := field.Size / field.Length
			for k := int64(0); k < field.Length; k++ {
				elemName := fmt.Sprintf("%s.%s[%d]", prefix, field.Name, k)
				if field.ElemType != "" {
					nested, reason, ok := compositeLeaves(comps, field.ElemType, elemName, at+k*stride, fieldGuards)
					if !ok {
						return nil, reason, false
					}
					out = append(out, nested...)
					continue
				}
				width, signed, ok := contractBits(&ast.Identifier{Value: field.Elem})
				if !ok || (int64(width) != stride*8 && field.Elem != "Bool") {
					return nil, fmt.Sprintf("an array of %s at the boundary", field.Elem), false
				}
				out = append(out, compositeLeaf{name: elemName, offset: at + k*stride, width: width, signed: signed, guards: fieldGuards})
			}
		default:
			return nil, "a composite field of unknown shape", false
		}
	}
	return out, "", true
}

// chunkTerm assembles register chunk k of a composite from its leaves: each
// leaf zero-extended and shifted to its byte offset within the chunk
// (little-endian); padding bytes are zero in the model, which the Oak body
// never reads.
func chunkTerm(leaves []compositeLeaf, k int64, input func(name string, width int) *term) *term {
	var chunk *term
	tagTerm := func(name string) *term { return input(name, 32) }
	for _, leaf := range leaves {
		if leaf.offset < 8*k || leaf.offset >= 8*k+8 {
			continue
		}
		placed := zeroExtend(leaf.guarded(input(leaf.name, leaf.width), tagTerm), 64)
		if shift := (leaf.offset - 8*k) * 8; shift > 0 {
			placed = binaryTerm("shl", placed, constTerm(uint64(shift), 64))
		}
		if chunk == nil {
			chunk = placed
		} else {
			chunk = binaryTerm("or", chunk, placed)
		}
	}
	if chunk == nil {
		return constTerm(0, 64)
	}
	return chunk
}

// leafMask is the bit mask of the leaves inside chunk k (the bytes a
// comparison of chunks may look at).
func leafMask(leaves []compositeLeaf, k int64) uint64 {
	var m uint64
	for _, leaf := range leaves {
		if leaf.offset < 8*k || leaf.offset >= 8*k+8 {
			continue
		}
		m |= mask(leaf.width) << uint((leaf.offset-8*k)*8)
	}
	return m
}

func (s *symbolicState) clone() *symbolicState {
	regs := make(map[int]*term, len(s.regs))
	for reg, value := range s.regs {
		regs[reg] = value
	}
	frame := make(map[int64]frameSlot, len(s.frame))
	for addr, slot := range s.frame {
		frame[addr] = slot
	}
	return &symbolicState{arch: s.arch, regs: regs, flags: s.flags, disp: s.disp, frame: frame}
}

// frameAccess executes a load or store through the sp frame: the address
// is entry-relative (-disp + offset), pre-index moves sp first and
// post-index after, exactly as the seam checker computes it. Stores record
// the term at the slot; loads read back a slot stored with the same width.
func (x *pathExecutor) frameAccess(instr Instruction, state *symbolicState) (string, bool) {
	mem := instr.Operands[len(instr.Operands)-1].(Memory)
	if mem.Index != nil {
		return "indexed frame access", false
	}
	var addr int64
	switch mem.Mode {
	case MemPreIndex:
		state.disp -= mem.Offset
		addr = -state.disp
	case MemPostIndex:
		addr = -state.disp
		defer func() { state.disp -= mem.Offset }()
	default:
		addr = -state.disp + mem.Offset
	}
	return x.frameAccessAt(instr, state, addr)
}

// frameAccessAt executes a load or store of the frame at an entry-relative
// address. Stores tile the frame: a slot records the term stored at its
// width, and a store over part of an older slot keeps the untouched bytes
// as aligned pieces. A load reads back one slot, a sub-range of it, or the
// exact concatenation of adjacent pieces (Oak.AssemblerSemantics.storeSlot
// / loadSlot_storeSlot, extended byte-wise), zero- or sign-extending into
// its register as the mnemonic says.
func (x *pathExecutor) frameAccessAt(instr Instruction, state *symbolicState, addr int64) (string, bool) {
	regs := registerOperands(instr.Operands[:len(instr.Operands)-1])
	if len(regs) == 0 || isAtomic(instr.Mnemonic) || isExclusiveStore(instr.Mnemonic) || instr.Mnemonic == "ldpsw" {
		return "a frame access outside the modeled subset (" + instr.Mnemonic + ")", false
	}
	for _, reg := range regs {
		if reg.Class == ClassV {
			return "a vector-register frame access", false
		}
	}
	size := memorySize(instr.Mnemonic, regs[0].Class)
	if len(regs) == 2 {
		size /= 2 // ldp/stp: one slot per register
	}
	if state.frame == nil {
		state.frame = map[int64]frameSlot{}
	}
	if isStoreMnemonic(instr.Mnemonic) {
		for i, reg := range regs {
			value, ok := state.read(reg)
			if !ok {
				return "unbound register read", false
			}
			state.storeSlot(addr+int64(i)*size, truncate(value, int(size)*8), size)
		}
		return "", true
	}
	for i, reg := range regs {
		value, ok := state.loadSlot(addr+int64(i)*size, size)
		if !ok {
			return "a load from a frame slot never stored on this path", false
		}
		if isSignExtendingLoad(instr.Mnemonic) {
			state.write(reg, extendTerm(value, int(size)*8, widthOf(reg.Class), true))
		} else {
			state.write(reg, zeroExtend(value, widthOf(reg.Class)))
		}
	}
	return "", true
}

// storeSlot records size bytes at addr, splitting any older slot the store
// partly covers into its untouched aligned pieces (little-endian: the low
// bytes of a slot's term are the lower addresses).
func (s *symbolicState) storeSlot(addr int64, value *term, size int64) {
	for start, slot := range s.frame {
		end := start + int64(slot.width)
		if end <= addr || start >= addr+size {
			continue
		}
		delete(s.frame, start)
		if start < addr {
			s.storePieces(start, addr-start, slot.value)
		}
		if end > addr+size {
			skip := addr + size - start
			s.storePieces(addr+size, end-(addr+size), truncate(binaryTerm("shr", slot.value, constTerm(uint64(skip*8), slot.value.width)), int(end-(addr+size))*8))
		}
	}
	s.frame[addr] = frameSlot{value: value, width: int(size)}
}

// storePieces stores a byte range as maximal naturally aligned power-of-two
// pieces of a term whose low byte is the range's first byte.
func (s *symbolicState) storePieces(addr, size int64, value *term) {
	off := int64(0)
	for off < size {
		piece := int64(8)
		for piece > 1 && ((addr+off)%piece != 0 || off+piece > size) {
			piece /= 2
		}
		part := truncate(binaryTerm("shr", value, constTerm(uint64(off*8), value.width)), int(piece)*8)
		s.frame[addr+off] = frameSlot{value: part, width: int(piece)}
		off += piece
	}
}

// loadSlot reads size bytes at addr: a stored slot, a sub-range of one, or
// the concatenation of the pieces tiling the range exactly.
func (s *symbolicState) loadSlot(addr, size int64) (*term, bool) {
	if slot, exact := s.frame[addr]; exact && int64(slot.width) == size {
		return slot.value, true
	}
	var result *term
	cursor := addr
	for cursor < addr+size {
		found := false
		for start, slot := range s.frame {
			end := start + int64(slot.width)
			if start <= cursor && cursor < end {
				take := end - cursor
				if take > addr+size-cursor {
					take = addr + size - cursor
				}
				piece := truncate(binaryTerm("shr", slot.value, constTerm(uint64((cursor-start)*8), slot.value.width)), int(take)*8)
				placed := zeroExtend(piece, int(size)*8)
				if cursor > addr {
					placed = binaryTerm("shl", placed, constTerm(uint64((cursor-addr)*8), int(size)*8))
				}
				if result == nil {
					result = placed
				} else {
					result = binaryTerm("or", result, placed)
				}
				cursor += take
				found = true
				break
			}
		}
		if !found {
			return nil, false
		}
	}
	return result, true
}

// frameAddressOf reads a term as an entry-relative frame address: the
// reserved parameter `sp#A` (what `add xN, sp, #imm` yields), or such a
// term plus constants (an element or field offset that folded).
func frameAddressOf(t *term) (int64, bool) {
	switch t.kind {
	case termParam:
		if strings.HasPrefix(t.name, "sp#") {
			addr, err := strconv.ParseInt(strings.TrimPrefix(t.name, "sp#"), 10, 64)
			return addr, err == nil
		}
	case termBinary:
		if t.op != "add" {
			return 0, false
		}
		if base, ok := frameAddressOf(t.left); ok && t.right.kind == termConst {
			return base + int64(t.right.value), true
		}
		if base, ok := frameAddressOf(t.right); ok && t.left.kind == termConst {
			return base + int64(t.left.value), true
		}
	}
	return 0, false
}

// frameAddressTerm names a frame address.
func frameAddressTerm(addr int64) *term { return paramTerm(fmt.Sprintf("sp#%d", addr), 64) }

// registerFrameAccess executes a load or store whose base register holds a
// frame address (an array or record element in the frame): the address is
// the base's plus the offset, or plus a constant index scaled — a symbolic
// index names no single slot and leaves the body outside the subset.
func (x *pathExecutor) registerFrameAccess(instr Instruction, state *symbolicState, mem Memory, base int64) (string, bool) {
	if mem.Mode != MemOffset {
		return "a frame address moved by pre/post-index", false
	}
	addr := base + mem.Offset
	if mem.Index != nil {
		index, ok := state.read(*mem.Index)
		if !ok {
			return "unbound register read", false
		}
		if index.kind != termConst {
			return "a frame access at a data-dependent index", false
		}
		addr += int64(index.value&mask(32)) << uint(mem.Shift)
	}
	return x.frameAccessAt(instr, state, addr)
}

// trapPath marks a path that ends in a trap (brk): it yields no result and
// is dropped from the fork that reached it. A body that traps on every
// path has no result to verify.
var trapPath = &term{kind: termConst, width: 64}

// registerFrameMemory reports a load or store whose base register holds a
// frame address term, with the address.
func registerFrameMemory(instr Instruction, state *symbolicState) (Memory, int64, bool) {
	if len(instr.Operands) == 0 || !(isStoreMnemonic(instr.Mnemonic) || isPlainLoad(instr.Mnemonic) || isSignExtendingLoad(instr.Mnemonic)) {
		return Memory{}, 0, false
	}
	mem, isMem := instr.Operands[len(instr.Operands)-1].(Memory)
	if !isMem || mem.Base.Class != ClassX {
		return Memory{}, 0, false
	}
	base, bound := state.regs[mem.Base.Num]
	if !bound {
		return Memory{}, 0, false
	}
	addr, isFrame := frameAddressOf(base)
	return mem, addr, isFrame
}

// isFrameMemory reports a memory instruction through sp.
func isFrameMemory(instr Instruction) bool {
	if len(instr.Operands) == 0 {
		return false
	}
	mem, isMem := instr.Operands[len(instr.Operands)-1].(Memory)
	return isMem && mem.Base.Class == ClassSP
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
			result, ok := state.read(x.resultReg)
			if !ok {
				return nil, "result register never written", false
			}
			if x.arch == ArchRV64 {
				// a0 holds the widened result; the contract width reads it.
				result = truncate(result, widthOf(x.resultClass))
			}
			return result, "", true
		case "brk", "ebreak":
			// A trap: this path delivers no result. The Oak body traps on
			// the same inputs (a failed bounds check, division by zero, an
			// overflowing shift, a failed assert), so the path is outside
			// the equivalence and drops from the fork it came from.
			return trapPath, "", true
		case "b", "j":
			target, ok := x.labels[instr.Operands[0].(Symbol).Name]
			if !ok {
				return nil, "a branch to an unknown label", false
			}
			pc = target - 1 // backward: a loop, bounded by the budgets
			continue
		case "b.", "cbz", "cbnz", "tbz", "tbnz", "beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz", "bnez", "bgez", "bltz", "blez", "bgtz":
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
			switch {
			case taken == trapPath:
				return fallThrough, "", true
			case fallThrough == trapPath:
				return taken, "", true
			}
			return iteTerm(cond, taken, fallThrough), "", true
		}
		if x.arch == ArchRV64 {
			if reason, ok := x.stepRV64(instr, state); !ok {
				return nil, reason, false
			}
			continue
		}
		if isFrameMemory(instr) {
			if reason, ok := x.frameAccess(instr, state); !ok {
				return nil, reason, false
			}
			continue
		}
		if mem, base, isFrame := registerFrameMemory(instr, state); isFrame {
			if reason, ok := x.registerFrameAccess(instr, state, mem, base); !ok {
				return nil, reason, false
			}
			continue
		}
		if isLoad(instr.Mnemonic) {
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
	dest, isReg := instr.Operands[0].(Register)
	if !isReg || dest.Class == ClassV {
		return "a vector-register load", false
	}
	mem := instr.Operands[1].(Memory)
	if mem.Base.Class == ClassSP {
		return "frame memory", false
	}
	base, bound := state.regs[mem.Base.Num]
	if !bound {
		return "a load through a register that is not a span base", false
	}
	param, baseOffset, isSpan := spanBaseOf(base)
	if !isSpan {
		return "a load through a register that is not a span base", false
	}
	if record, isRecord := x.records[param]; isRecord {
		// The caller's copy of a record argument: a load at a leaf's exact
		// offset and width is that leaf.
		if mem.Index != nil {
			return "an indexed load through a record argument", false
		}
		size := memorySize(instr.Mnemonic, dest.Class)
		value, ok := x.recordBytes(record.leaves, baseOffset+mem.Offset, size)
		if !ok {
			return "a load from a record argument cutting through a field", false
		}
		if isSignExtendingLoad(instr.Mnemonic) {
			state.write(dest, extendTerm(value, int(size)*8, widthOf(dest.Class), true))
		} else {
			state.write(dest, zeroExtend(value, widthOf(dest.Class)))
		}
		return "", true
	}
	elem := x.spans[param]
	if mem.Mode != MemOffset {
		return "a span base moved by pre/post-index", false
	}
	if elem == 0 || baseOffset%elem != 0 {
		return "a derived span base not aligned to an element", false
	}
	baseIndex := baseOffset / elem
	// The access size is the element size; a narrower load extends the
	// element into its register — zero-extending, or sign-extending for
	// the ldrs* family.
	size := memorySize(instr.Mnemonic, dest.Class)
	if size != elem {
		return fmt.Sprintf("a %d-byte load over %d-byte elements", size, elem), false
	}
	extend := func(element *term) *term {
		if isSignExtendingLoad(instr.Mnemonic) {
			return extendTerm(element, int(elem)*8, widthOf(dest.Class), true)
		}
		return zeroExtend(element, widthOf(dest.Class))
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
		if baseIndex != 0 {
			index = binaryTerm("add", truncate(index, 32), constTerm(uint64(baseIndex), 32))
		}
		state.write(dest, extend(x.element(param, index, int(elem)*8)))
		return "", true
	}
	if mem.Offset < 0 || mem.Offset%elem != 0 {
		return "a load not aligned to an element", false
	}
	state.write(dest, extend(x.element(param, constTerm(uint64(mem.Offset/elem+baseIndex), 32), int(elem)*8)))
	return "", true
}

// leafInput is a leaf parameter's term: its witness value in a concrete
// run, else the parameter.
func (x *pathExecutor) leafInput(name string, width int) *term {
	if x.env != nil {
		if concrete, isConcrete := x.env[name]; isConcrete {
			return constTerm(concrete&mask(width), width)
		}
	}
	return paramTerm(name, width)
}

// recordBytes assembles size bytes at offset of a by-reference record
// argument from the leaves inside the range (padding zero); a leaf the
// range cuts through is outside the subset.
func (x *pathExecutor) recordBytes(leaves []compositeLeaf, offset, size int64) (*term, bool) {
	var value *term
	for _, leaf := range leaves {
		end := leaf.offset + int64(leaf.width)/8
		if end <= offset || leaf.offset >= offset+size {
			continue
		}
		if leaf.offset < offset || end > offset+size {
			return nil, false
		}
		t := leaf.guarded(x.leafInput(leaf.name, leaf.width), func(name string) *term { return x.leafInput(name, 32) })
		placed := zeroExtend(t, int(size)*8)
		if shift := (leaf.offset - offset) * 8; shift > 0 {
			placed = binaryTerm("shl", placed, constTerm(uint64(shift), int(size)*8))
		}
		if value == nil {
			value = placed
		} else {
			value = binaryTerm("or", value, placed)
		}
	}
	if value == nil {
		value = constTerm(0, int(size)*8)
	}
	return value, true
}

// spanBaseOf reads a term as a span base: the parameter `&v`, or `&v` plus a
// constant byte offset (a subslice with a constant start).
func spanBaseOf(t *term) (param string, offset int64, ok bool) {
	switch t.kind {
	case termParam:
		if strings.HasPrefix(t.name, "&") {
			return strings.TrimPrefix(t.name, "&"), 0, true
		}
	case termBinary:
		if t.op != "add" {
			return "", 0, false
		}
		if name, base, isSpan := spanBaseOf(t.left); isSpan && t.right.kind == termConst {
			return name, base + int64(t.right.value), true
		}
		if name, base, isSpan := spanBaseOf(t.right); isSpan && t.left.kind == termConst {
			return name, base + int64(t.left.value), true
		}
	}
	return "", 0, false
}

// isLoad reports the load mnemonics the executor resolves through a span.
func isLoad(mnemonic string) bool { return isPlainLoad(mnemonic) }

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
	for _, reg := range registerOperands(instr.Operands) {
		if reg.Class == ClassV {
			return "a floating-point or vector instruction (" + instr.Mnemonic + ")", false
		}
	}
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
		case "tst":
			left := instr.Operands[0].(Register)
			width := widthOf(left.Class)
			l, okL := operandTerm(state, left, width)
			r, okR := operandTerm(state, instr.Operands[1], width)
			if !okL || !okR {
				return "unbound register read", false
			}
			state.flags = &flagsFact{left: l, right: r, width: width, kind: "and"}
		case "bfc":
			// Clear the field: the destination with a hole.
			dest := instr.Operands[0].(Register)
			width := widthOf(dest.Class)
			lsb := instr.Operands[1].(Immediate).Value
			fieldWidth := instr.Operands[2].(Immediate).Value
			if lsb < 0 || fieldWidth < 1 || lsb+fieldWidth > int64(width) {
				return "a bit field outside the register", false
			}
			current, ok := state.read(dest)
			if !ok {
				return "unbound register read", false
			}
			hole := constTerm(^(mask(int(fieldWidth))<<uint(lsb))&mask(width), width)
			state.write(dest, binaryTerm("and", current, hole))
		case "ubfx", "ubfiz", "sbfx", "sbfiz", "bfi", "bfxil":
			dest := instr.Operands[0].(Register)
			width := widthOf(dest.Class)
			source, ok := operandTerm(state, instr.Operands[1], width)
			if !ok {
				return "unbound register read", false
			}
			lsb := instr.Operands[2].(Immediate).Value
			fieldWidth := instr.Operands[3].(Immediate).Value
			if lsb < 0 || fieldWidth < 1 || lsb+fieldWidth > int64(width) {
				return "a bit field outside the register", false
			}
			fieldMask := constTerm(mask(int(fieldWidth)), width)
			switch instr.Mnemonic {
			case "ubfx":
				state.write(dest, binaryTerm("and", binaryTerm("shr", source, constTerm(uint64(lsb), width)), fieldMask))
			case "ubfiz":
				state.write(dest, binaryTerm("shl", binaryTerm("and", source, fieldMask), constTerm(uint64(lsb), width)))
			case "sbfx":
				// Shift the field to the top, then arithmetic-shift it down.
				up := constTerm(uint64(int64(width)-lsb-fieldWidth), width)
				down := constTerm(uint64(int64(width)-fieldWidth), width)
				state.write(dest, binaryTerm("sar", binaryTerm("shl", source, up), down))
			case "sbfiz":
				// The field to the top, then arithmetic-shift it down to lsb.
				up := constTerm(uint64(int64(width)-fieldWidth), width)
				down := constTerm(uint64(int64(width)-fieldWidth-lsb), width)
				state.write(dest, binaryTerm("sar", binaryTerm("shl", source, up), down))
			case "bfi":
				current, ok := state.read(dest)
				if !ok {
					return "unbound register read", false
				}
				placed := binaryTerm("shl", binaryTerm("and", source, fieldMask), constTerm(uint64(lsb), width))
				hole := constTerm(^(mask(int(fieldWidth))<<uint(lsb))&mask(width), width)
				state.write(dest, binaryTerm("or", binaryTerm("and", current, hole), placed))
			case "bfxil":
				// Extract the field at lsb and insert it at the bottom.
				current, ok := state.read(dest)
				if !ok {
					return "unbound register read", false
				}
				extracted := binaryTerm("and", binaryTerm("shr", source, constTerm(uint64(lsb), width)), fieldMask)
				hole := constTerm(^mask(int(fieldWidth))&mask(width), width)
				state.write(dest, binaryTerm("or", binaryTerm("and", current, hole), extracted))
			}
		case "madd", "msub":
			dest := instr.Operands[0].(Register)
			width := widthOf(dest.Class)
			n, okN := operandTerm(state, instr.Operands[1], width)
			m, okM := operandTerm(state, instr.Operands[2], width)
			a, okA := operandTerm(state, instr.Operands[3], width)
			if !okN || !okM || !okA {
				return "unbound register read", false
			}
			product := binaryTerm("mul", n, m)
			if instr.Mnemonic == "madd" {
				state.write(dest, binaryTerm("add", a, product))
			} else {
				state.write(dest, binaryTerm("sub", a, product))
			}
		case "cinc", "cneg":
			if state.flags == nil || state.flags.unknown {
				return fmt.Sprintf("%s reading flags not produced by cmp/subs", instr.Mnemonic), false
			}
			code := instr.Operands[2].(Condition).Code
			if !verifiableConditions[code] {
				return fmt.Sprintf("condition code %s", code), false
			}
			dest := instr.Operands[0].(Register)
			width := widthOf(dest.Class)
			source, ok := operandTerm(state, instr.Operands[1], width)
			if !ok {
				return "unbound register read", false
			}
			changed := binaryTerm("add", source, constTerm(1, width))
			if instr.Mnemonic == "cneg" {
				changed = binaryTerm("sub", constTerm(0, width), source)
			}
			state.write(dest, iteTerm(flagsCondition(code, state.flags), changed, source))
		case "ccmp":
			if state.flags == nil || state.flags.unknown {
				return "ccmp reading flags not produced by cmp/subs", false
			}
			code := instr.Operands[3].(Condition).Code
			if !verifiableConditions[code] {
				return fmt.Sprintf("condition code %s", code), false
			}
			left := instr.Operands[0].(Register)
			width := widthOf(left.Class)
			l, okL := operandTerm(state, left, width)
			r, okR := operandTerm(state, instr.Operands[1], width)
			if !okL || !okR {
				return "unbound register read", false
			}
			prior := flagsCondition(code, state.flags)
			state.flags = &flagsFact{left: l, right: r, width: width, cond: prior, elseNZCV: instr.Operands[2].(Immediate).Value}
		case "neg", "mvn":
			dest := instr.Operands[0].(Register)
			width := widthOf(dest.Class)
			source, ok := operandTerm(state, instr.Operands[1], width)
			if !ok {
				return "unbound register read", false
			}
			if instr.Mnemonic == "neg" {
				state.write(dest, binaryTerm("sub", constTerm(0, width), source))
			} else {
				state.write(dest, binaryTerm("xor", source, constTerm(mask(width), width)))
			}
		default:
			if handled, reason, ok := stepISA(instr, state); handled {
				return reason, ok
			}
			op, verifiable := verifiableOps[instr.Mnemonic]
			if !verifiable || len(instr.Operands) != 3 {
				return fmt.Sprintf("instruction %s", instr.Mnemonic), false
			}
			dest := instr.Operands[0].(Register)
			if dest.Class == ClassSP {
				// sub/add sp, sp, #imm moves the frame (the checker keeps it
				// inside the declared frame and 16-byte aligned).
				imm, isImm := instr.Operands[2].(Immediate)
				if !isImm || (instr.Mnemonic != "add" && instr.Mnemonic != "sub") {
					return "stack pointer arithmetic that is not an immediate add/sub", false
				}
				if instr.Mnemonic == "sub" {
					state.disp += imm.Value
				} else {
					state.disp -= imm.Value
				}
				return "", true
			}
			if src, isReg := instr.Operands[1].(Register); isReg && src.Class == ClassSP && instr.Mnemonic == "add" {
				// add xN, sp, #imm: the frame address of an array or record.
				imm, isImm := instr.Operands[2].(Immediate)
				if !isImm {
					return "a frame address with a register offset", false
				}
				state.write(dest, frameAddressTerm(-state.disp+imm.Value))
				return "", true
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
				state.flags = &flagsFact{left: left, right: right, width: widthOf(dest.Class), kind: "add"}
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
	if rv64ConditionalBranches[instr.Mnemonic] {
		return rv64BranchCondition(instr, state)
	}
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
		return constTerm(uint64(o.Value)<<uint(o.Shift), width), true
	case Shifted:
		value, ok := state.read(o.Reg)
		if !ok {
			return nil, false
		}
		op := map[string]string{"lsl": "shl", "lsr": "shr", "asr": "sar", "ror": "ror"}[o.Kind]
		return binaryTerm(op, value, constTerm(uint64(o.Amount), value.width)), true
	case Extended:
		value, ok := state.read(o.Reg)
		if !ok {
			return nil, false
		}
		from := map[string]int{"uxtb": 8, "sxtb": 8, "uxth": 16, "sxth": 16, "uxtw": 32, "sxtw": 32, "uxtx": 64, "sxtx": 64}[o.Kind]
		extended := extendTerm(value, from, width, o.Kind[0] == 's')
		if o.Amount == 0 {
			return extended, true
		}
		return binaryTerm("shl", extended, constTerm(uint64(o.Amount), width)), true
	}
	return nil, false
}

// --- the Oak specification ----------------------------------------------

var oakOps = map[string]string{"+": "add", "-": "sub", "*": "mul", "&": "and", "|": "or", "^": "xor", "<<": "shl", ">>": "shr"}

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
	// functions are the program's functions a body may call; a call to one
	// in the subset is inlined (inlineCall). Nil outside the theorem decider.
	functions map[string]*ast.FunctionStatement
	inlining  map[string]bool // callees on the inlining stack, against recursion
	// guards are the program's refinements (Guard); a construction lowers
	// to its argument with the predicate as a trap obligation. Nil outside
	// the theorem decider.
	guards map[string]Guard
	// trapsTracked lets a body contain a construct that traps on some
	// inputs — a variable shift count reaching the width — by recording
	// the trap condition in traps instead of refusing the body; the
	// theorem decider proves every recorded condition impossible. The asm
	// verifier leaves it off: there the machine wraps where Oak traps.
	trapsTracked bool
	traps        []*term
	// floats names the parameters and locals of f32/f64 type (their width),
	// whose operations and comparisons are IEEE (asm/floats_lowering.go).
	floats      map[string]int
	freshFloats int
	// path is the condition under which the construct being lowered runs
	// (nil: always) — the branches of conditionals and the right operands
	// of the short-circuit operators taken so far — so a recorded trap is
	// an obligation only where the program reaches it.
	path *term
	// The program's record and tagged-union declarations (asm.Function
	// Records/ADTs) and the shapes resolved from them.
	records map[string]*ast.RecordLiteral
	adts    map[string]*ast.ADTType
	types   map[string]*oakType
}

// oakLocal is a typed local of a statement body: its current symbolic
// value (assignments replace it) at its declared width and signedness — or,
// for a record, tagged union, or owned array, the aggregate holding a term
// per scalar leaf.
type oakLocal struct {
	value  *term
	width  int
	signed bool
	agg    *oakValue
}

// oakType is the shape of a local: a scalar, a declared record, a tagged
// union (the u32 tag and one payload per carrying variant), or an owned
// array of a fixed length.
type oakType struct {
	kind     oakKind
	width    int
	signed   bool
	name     string
	fields   []oakField   // record
	variants []oakVariant // adt
	elem     *oakType     // array
	length   int64
}

type oakKind int

const (
	oakScalar oakKind = iota
	oakRecord
	oakADT
	oakArray
)

type oakField struct {
	name string
	typ  *oakType
}

type oakVariant struct {
	name    string
	tag     int64
	payload *oakType // nil for a bare variant
}

// oakValue is a value of an oakType: a term at a scalar leaf, the fields
// of a record (an ADT's "tag" leaf and payload fields named by variant), or
// the elements of an array. Aggregates are trees of leaves, so every
// operation on them is a copy, a leaf read, or a leaf write.
type oakValue struct {
	typ    *oakType
	scalar *term
	fields map[string]*oakValue
	elems  []*oakValue
}

func (v *oakValue) copy() *oakValue {
	if v == nil {
		return nil
	}
	out := &oakValue{typ: v.typ, scalar: v.scalar}
	if v.fields != nil {
		out.fields = make(map[string]*oakValue, len(v.fields))
		for name, field := range v.fields {
			out.fields[name] = field.copy()
		}
	}
	if v.elems != nil {
		out.elems = make([]*oakValue, len(v.elems))
		for i, elem := range v.elems {
			out.elems[i] = elem.copy()
		}
	}
	return out
}

// leaves visits every scalar leaf of two values of one type in step.
func leaves(a, b *oakValue, visit func(a, b *oakValue)) {
	if a.scalar != nil || b.scalar != nil {
		visit(a, b)
		return
	}
	for name, field := range a.fields {
		leaves(field, b.fields[name], visit)
	}
	for i, elem := range a.elems {
		leaves(elem, b.elems[i], visit)
	}
}

// oakTypeOf resolves a local's declared type expression.
func (lo *oakLowering) oakTypeOf(expr ast.Expression) (*oakType, bool) {
	if width, signed, ok := contractBits(expr); ok {
		return &oakType{kind: oakScalar, width: width, signed: signed}, true
	}
	switch e := expr.(type) {
	case *ast.Identifier:
		return lo.namedType(e.Value)
	case *ast.IndexExpression:
		if e.Dot {
			return nil, false
		}
		if length, isLit := e.Index.(*ast.IntegerLiteral); isLit && length.Value > 0 {
			if elem, ok := lo.oakTypeOf(e.Left); ok {
				return &oakType{kind: oakArray, elem: elem, length: length.Value}, true
			}
		}
		// An instantiation (Option[u32]): the specialized declaration under
		// its mangled name.
		if name, ok := TypeApplicationName(expr); ok {
			return lo.namedType(name)
		}
	}
	return nil, false
}

// namedType resolves a declared record or tagged union (cached; a type
// containing itself fails).
func (lo *oakLowering) namedType(name string) (*oakType, bool) {
	if typ, done := lo.types[name]; done {
		return typ, typ != nil
	}
	if lo.types == nil {
		lo.types = map[string]*oakType{}
	}
	lo.types[name] = nil // placing: a cycle resolves to failure
	if literal, isRecord := lo.records[name]; isRecord {
		typ := &oakType{kind: oakRecord, name: name}
		for _, field := range literal.FieldOrder {
			fieldType, ok := lo.oakTypeOf(field.Value)
			if !ok {
				return nil, false
			}
			typ.fields = append(typ.fields, oakField{name: field.Name, typ: fieldType})
		}
		lo.types[name] = typ
		return typ, true
	}
	if adt, isADT := lo.adts[name]; isADT {
		typ := &oakType{kind: oakADT, name: name}
		for i, variant := range adt.Variants {
			v := oakVariant{name: variant.Name.Value, tag: int64(i)}
			if i < len(adt.TagValues) {
				v.tag = int64(adt.TagValues[i])
			}
			if variant.Payload != nil {
				payload, ok := lo.oakTypeOf(variant.Payload)
				if !ok {
					return nil, false
				}
				v.payload = payload
			}
			typ.variants = append(typ.variants, v)
		}
		lo.types[name] = typ
		return typ, true
	}
	return nil, false
}

func (t *oakType) variant(name string) (oakVariant, bool) {
	for _, v := range t.variants {
		if v.name == name {
			return v, true
		}
	}
	return oakVariant{}, false
}

func (t *oakType) field(name string) (*oakType, bool) {
	for _, f := range t.fields {
		if f.name == name {
			return f.typ, true
		}
	}
	return nil, false
}

// zeroValue is the all-zero value of a type (a value-less array local).
func zeroValue(typ *oakType) *oakValue {
	switch typ.kind {
	case oakScalar:
		return &oakValue{typ: typ, scalar: constTerm(0, typ.width)}
	case oakRecord:
		out := &oakValue{typ: typ, fields: map[string]*oakValue{}}
		for _, f := range typ.fields {
			out.fields[f.name] = zeroValue(f.typ)
		}
		return out
	case oakADT:
		out := &oakValue{typ: typ, fields: map[string]*oakValue{"tag": {typ: &oakType{kind: oakScalar, width: 32}, scalar: constTerm(0, 32)}}}
		for _, v := range typ.variants {
			if v.payload != nil {
				out.fields[v.name] = zeroValue(v.payload)
			}
		}
		return out
	default:
		out := &oakValue{typ: typ}
		for i := int64(0); i < typ.length; i++ {
			out.elems = append(out.elems, zeroValue(typ.elem))
		}
		return out
	}
}

// aggregateValue lowers an expression of an aggregate type: a typed record
// literal, a variant, an array literal, or a copy of a place.
func (lo *oakLowering) aggregateValue(expr ast.Expression, typ *oakType) (*oakValue, string, bool) {
	switch e := expr.(type) {
	case *ast.RecordLiteral:
		if typ.kind != oakRecord {
			return nil, "a record literal for a non-record", false
		}
		if e.TypeName != nil && e.TypeName.Value != typ.name {
			return nil, fmt.Sprintf("a %s literal where %s is expected", e.TypeName.Value, typ.name), false
		}
		out := &oakValue{typ: typ, fields: map[string]*oakValue{}}
		for _, f := range typ.fields {
			value, given := e.Fields[f.name]
			if !given {
				return nil, fmt.Sprintf("a %s literal without the field %s", typ.name, f.name), false
			}
			fieldValue, reason, ok := lo.valueOf(value, f.typ)
			if !ok {
				return nil, reason, false
			}
			out.fields[f.name] = fieldValue
		}
		return out, "", true
	case *ast.VariantExpression:
		if typ.kind != oakADT {
			return nil, "a variant for a non-union", false
		}
		if e.TypeName != nil && e.TypeName.Value != typ.name {
			return nil, fmt.Sprintf("a %s variant where %s is expected", e.TypeName.Value, typ.name), false
		}
		variant, known := typ.variant(e.Variant.Value)
		if !known {
			return nil, fmt.Sprintf("the variant %s of %s", e.Variant.Value, typ.name), false
		}
		out := zeroValue(typ)
		out.fields["tag"].scalar = constTerm(uint64(variant.tag), 32)
		if (e.Payload == nil) != (variant.payload == nil) {
			return nil, fmt.Sprintf("the variant %s.%s with the wrong payload shape", typ.name, e.Variant.Value), false
		}
		if e.Payload != nil {
			payload, reason, ok := lo.valueOf(e.Payload, variant.payload)
			if !ok {
				return nil, reason, false
			}
			out.fields[variant.name] = payload
		}
		return out, "", true
	case *ast.ArrayLiteral:
		if typ.kind != oakArray || int64(len(e.Elements)) != typ.length {
			return nil, "an array literal of the wrong shape", false
		}
		out := &oakValue{typ: typ}
		for _, element := range e.Elements {
			value, reason, ok := lo.valueOf(element, typ.elem)
			if !ok {
				return nil, reason, false
			}
			out.elems = append(out.elems, value)
		}
		return out, "", true
	case *ast.Identifier, *ast.IndexExpression:
		place, reason, ok := lo.placeOf(expr)
		if !ok {
			return nil, reason, false
		}
		if place.typ != typ {
			return nil, fmt.Sprintf("%s is not a %s", expr.String(), typ.name), false
		}
		return place.copy(), "", true
	case *ast.InvocationExpression:
		// A call to a program function returning a record or sum type is
		// inlined as an aggregate value.
		if ident, isIdent := e.Function.(*ast.Identifier); isIdent {
			if callee, known := lo.functions[ident.Value]; known {
				return lo.inlineCallValue(callee, e, typ)
			}
		}
		return nil, fmt.Sprintf("the call %s as an aggregate value", e.String()), false
	case *ast.BlockExpression:
		if e.Block == nil || len(e.Block.Statements) == 0 {
			return nil, "an empty block as an aggregate value", false
		}
		stmts := e.Block.Statements
		for _, stmt := range stmts[:len(stmts)-1] {
			if reason, ok := lo.runStatement(stmt); !ok {
				return nil, reason, false
			}
		}
		last, isExpr := stmts[len(stmts)-1].(*ast.ExpressionStatement)
		if !isExpr {
			return nil, "a block that does not end in an expression", false
		}
		return lo.aggregateValue(last.Expression, typ)
	case *ast.MatchExpression:
		if whenTrue, whenFalse, isBool := boolConditional(e); isBool {
			cond, reason, ok := lo.lowerCondition(e.Scrutinee)
			if !ok {
				return nil, reason, false
			}
			restore := lo.underPath(cond)
			t, reason, ok := lo.aggregateValue(whenTrue, typ)
			restore()
			if !ok {
				return nil, reason, false
			}
			restore = lo.underPath(notTerm(cond))
			f, reason, ok := lo.aggregateValue(whenFalse, typ)
			restore()
			if !ok {
				return nil, reason, false
			}
			return mergeValues(cond, t, f), "", true
		}
		return lo.selectMatch(e, func(body ast.Expression) (*oakValue, string, bool) { return lo.aggregateValue(body, typ) })
	}
	return nil, fmt.Sprintf("%T as an aggregate value", expr), false
}

// runStatement executes one statement of a block (not its result).
func (lo *oakLowering) runStatement(stmt ast.Statement) (string, bool) {
	switch s := stmt.(type) {
	case *ast.VariableDeclaration:
		return lo.declareLocal(s)
	case *ast.AssignmentStatement:
		return lo.assignLocal(s)
	case *ast.IndexAssignmentStatement:
		return lo.assignIndexed(s)
	case *ast.WhileStatement:
		return lo.lowerWhile(s)
	case *ast.ExpressionStatement:
		if match, isMatch := s.Expression.(*ast.MatchExpression); isMatch {
			return lo.lowerConditionalStatement(match)
		}
		if reason, isAssert, ok := lo.lowerAssert(s.Expression); isAssert {
			return reason, ok
		}
		return "an expression statement before the end of a block", false
	}
	return fmt.Sprintf("%T", stmt), false
}

// addTrap records a trap condition under the current path condition.
func (lo *oakLowering) addTrap(t *term) {
	t = truncate(t, 1)
	if lo.path != nil {
		t = binaryTerm("and", lo.path, t)
	}
	lo.traps = append(lo.traps, t)
}

// underPath narrows the path condition for the construct lowered next and
// returns the restore.
func (lo *oakLowering) underPath(cond *term) func() {
	saved := lo.path
	cond = truncate(cond, 1)
	if saved == nil {
		lo.path = cond
	} else {
		lo.path = binaryTerm("and", saved, cond)
	}
	return func() { lo.path = saved }
}

func notTerm(t *term) *term { return binaryTerm("xor", truncate(t, 1), constTerm(1, 1)) }

// lowerAssert records `assert(cond)` as a trap obligation under the
// theorem decider (docs/spec/85-discipline.md section 5: an assert is
// never elided; here the decider proves it cannot fire), and refuses it
// where traps are not tracked.
func (lo *oakLowering) lowerAssert(expr ast.Expression) (reason string, isAssert bool, ok bool) {
	call, isCall := expr.(*ast.InvocationExpression)
	if !isCall || len(call.Arguments) != 1 {
		return "", false, false
	}
	if fn, isIdent := call.Function.(*ast.Identifier); !isIdent || fn.Value != "assert" {
		return "", false, false
	}
	if !lo.trapsTracked {
		return "an assert", true, false
	}
	cond, reason, ok := lo.lowerCondition(call.Arguments[0])
	if !ok {
		return reason, true, false
	}
	lo.addTrap(binaryTerm("xor", truncate(cond, 1), constTerm(1, 1)))
	return "", true, true
}

// valueOf lowers an expression at a type: a scalar term or an aggregate.
func (lo *oakLowering) valueOf(expr ast.Expression, typ *oakType) (*oakValue, string, bool) {
	if typ.kind == oakScalar {
		t, reason, ok := lo.lower(expr, typ.width)
		if !ok {
			return nil, reason, false
		}
		return &oakValue{typ: typ, scalar: t}, "", true
	}
	return lo.aggregateValue(expr, typ)
}

// placeOf resolves an access chain over aggregate locals: a local, `p.f`,
// `arr[k]` with a constant index.
func (lo *oakLowering) placeOf(expr ast.Expression) (*oakValue, string, bool) {
	switch e := expr.(type) {
	case *ast.Identifier:
		local, isLocal := lo.locals[e.Value]
		if !isLocal || local.agg == nil {
			return nil, fmt.Sprintf("%s is not an aggregate local", e.Value), false
		}
		return local.agg, "", true
	case *ast.IndexExpression:
		base, reason, ok := lo.placeOf(e.Left)
		if !ok {
			return nil, reason, false
		}
		if e.Dot {
			name, isName := e.Index.(*ast.Identifier)
			if !isName || base.fields == nil {
				return nil, fmt.Sprintf("the field access %s", e.String()), false
			}
			field, has := base.fields[name.Value]
			if !has {
				return nil, fmt.Sprintf("the field %s of %s", name.Value, base.typ.name), false
			}
			return field, "", true
		}
		if base.typ.kind != oakArray {
			return nil, fmt.Sprintf("an index into %s (not an array)", e.Left.String()), false
		}
		k, isConst := lo.constantIndexValue(e.Index)
		if !isConst {
			return nil, "an array element at a data-dependent index", false
		}
		if k < 0 || k >= base.typ.length {
			return nil, fmt.Sprintf("the index %d past [%d]", k, base.typ.length), false
		}
		return base.elems[k], "", true
	}
	return nil, fmt.Sprintf("%T as a place", expr), false
}

// paramAggregate builds a record or union parameter's aggregate: every
// scalar leaf the parameter term named by its access path (the executor's
// compositeLeaves spelling), a concrete value in a witness run.
func (lo *oakLowering) paramAggregate(typ *oakType, prefix string) (*oakValue, bool) {
	switch typ.kind {
	case oakScalar:
		lo.params[prefix] = typ.width
		lo.signed[prefix] = typ.signed
		if value, isConcrete := lo.concrete[prefix]; isConcrete {
			return &oakValue{typ: typ, scalar: constTerm(value&mask(typ.width), typ.width)}, true
		}
		return &oakValue{typ: typ, scalar: paramTerm(prefix, typ.width)}, true
	case oakRecord:
		out := &oakValue{typ: typ, fields: map[string]*oakValue{}}
		for _, f := range typ.fields {
			value, ok := lo.paramAggregate(f.typ, prefix+"."+f.name)
			if !ok {
				return nil, false
			}
			out.fields[f.name] = value
		}
		return out, true
	case oakADT:
		out := &oakValue{typ: typ, fields: map[string]*oakValue{}}
		tag, ok := lo.paramAggregate(&oakType{kind: oakScalar, width: 32}, prefix+".tag")
		if !ok {
			return nil, false
		}
		out.fields["tag"] = tag
		for _, v := range typ.variants {
			if v.payload != nil {
				value, ok := lo.paramAggregate(v.payload, prefix+"."+v.name)
				if !ok {
					return nil, false
				}
				out.fields[v.name] = value
			}
		}
		return out, true
	default:
		out := &oakValue{typ: typ}
		for k := int64(0); k < typ.length; k++ {
			value, ok := lo.paramAggregate(typ.elem, fmt.Sprintf("%s[%d]", prefix, k))
			if !ok {
				return nil, false
			}
			out.elems = append(out.elems, value)
		}
		return out, true
	}
}

// bindAggregateParams binds every record or union parameter as an
// aggregate local of leaf parameters (the declarations must be set).
func (lo *oakLowering) bindAggregateParams(sig *ast.FunctionStatement) {
	for _, param := range sig.Parameters {
		if width, isScalar := lo.params[param.Name.Value]; isScalar && width > 0 {
			continue
		}
		if _, isSpan := lo.spans[param.Name.Value]; isSpan {
			continue
		}
		typ, ok := lo.oakTypeOf(param.Type)
		if !ok || typ.kind == oakScalar {
			continue
		}
		if agg, ok := lo.paramAggregate(typ, param.Name.Value); ok {
			if lo.locals == nil {
				lo.locals = map[string]*oakLocal{}
			}
			lo.locals[param.Name.Value] = &oakLocal{agg: agg}
		}
	}
}

// leafTerms lists an aggregate's scalar leaves by access path.
func leafTerms(v *oakValue, prefix string, into map[string]*term) {
	if v.scalar != nil {
		into[prefix] = v.scalar
		return
	}
	for name, field := range v.fields {
		leafTerms(field, prefix+"."+name, into)
	}
	for k, elem := range v.elems {
		leafTerms(elem, fmt.Sprintf("%s[%d]", prefix, k), into)
	}
}

// packAggregate lays an aggregate's leaves into register chunk 0 as the
// executor assembles a composite (chunkTerm), for a one-chunk result.
func packAggregate(v *oakValue, leaves []compositeLeaf) (*term, bool) {
	terms := map[string]*term{}
	leafTerms(v, "", terms)
	tagTerm := func(name string) *term {
		if t, has := terms[name]; has {
			return adaptWidth(t, 32)
		}
		return constTerm(0, 32)
	}
	var chunk *term
	for _, leaf := range leaves {
		t, has := terms[leaf.name]
		if !has {
			return nil, false
		}
		placed := zeroExtend(leaf.guarded(adaptWidth(t, leaf.width), tagTerm), 64)
		if leaf.offset > 0 {
			placed = binaryTerm("shl", placed, constTerm(uint64(leaf.offset*8), 64))
		}
		if chunk == nil {
			chunk = placed
		} else {
			chunk = binaryTerm("or", chunk, placed)
		}
	}
	if chunk == nil {
		chunk = constTerm(0, 64)
	}
	return chunk, true
}

// mergeValues joins two values of one type leaf-wise under a condition.
func mergeValues(cond *term, whenTrue, whenFalse *oakValue) *oakValue {
	out := whenFalse.copy()
	leaves(whenTrue, out, func(t, f *oakValue) {
		if t.scalar != f.scalar {
			f.scalar = iteTerm(truncate(cond, 1), t.scalar, f.scalar)
		}
	})
	return out
}

// matchArm is one arm of a decided-by-condition match: cond selects it.
type matchArm struct {
	cond  *term
	index int
}

// matchArms walks a match's arms in order, computing each arm's condition
// — the union's tag or the scalar scrutinee equal to the pattern — binding
// a payload before visiting the arm's body, and stopping at the wildcard
// arm, which becomes the fallback. Without a wildcard the checker proved
// the arms exhaustive, so the last arm is the fallback. A scrutinee that
// folds decides statically through the same chain.
func (lo *oakLowering) matchArms(match *ast.MatchExpression, visit func(index int, body ast.Expression) (string, bool)) (cases []matchArm, fallback int, reason string, ok bool) {
	fallback = -1
	place, _, isAggregate := lo.placeOf(match.Scrutinee)
	var tag, scrutinee *term
	var width int
	if isAggregate && place.typ.kind == oakADT {
		tag = place.fields["tag"].scalar
	} else {
		w, _, isScalar := lo.operandContract(match.Scrutinee)
		if !isScalar {
			return nil, -1, "a match scrutinee outside the subset", false
		}
		width = w
		value, reason, ok := lo.lower(match.Scrutinee, width)
		if !ok {
			return nil, -1, reason, false
		}
		scrutinee = value
	}
	taken := constTerm(0, 1)
	for i, arm := range match.Arms {
		var cond *term
		switch pattern := arm.Pattern.(type) {
		case *ast.VariantPattern:
			if tag == nil {
				return nil, -1, "a variant pattern over a scalar", false
			}
			variant, known := place.typ.variant(pattern.Variant.Value)
			if !known {
				return nil, -1, fmt.Sprintf("the variant %s in a pattern", pattern.Variant.Value), false
			}
			binding, isBinding := pattern.Payload.(*ast.BindingPattern)
			switch {
			case isBinding && binding.Name != nil && binding.Name.Value != "_":
				if variant.payload == nil {
					return nil, -1, "a binding on a bare variant", false
				}
				payload := place.fields[variant.name].copy()
				if payload.typ.kind == oakScalar {
					lo.locals[binding.Name.Value] = &oakLocal{value: payload.scalar, width: payload.typ.width, signed: payload.typ.signed}
				} else {
					lo.locals[binding.Name.Value] = &oakLocal{agg: payload}
				}
			case pattern.Payload == nil, isBinding:
			default:
				if _, isWild := pattern.Payload.(*ast.WildcardPattern); !isWild {
					return nil, -1, fmt.Sprintf("the payload pattern %s", pattern.Payload.String()), false
				}
			}
			cond = truncate(cmpTerm("eq", tag, constTerm(uint64(variant.tag), 32)), 1)
		case *ast.LiteralPattern:
			if scrutinee == nil {
				return nil, -1, "a literal pattern over a tagged union", false
			}
			lit, reason, ok := lo.lower(pattern.Value, width)
			if !ok {
				return nil, -1, reason, false
			}
			cond = truncate(cmpTerm("eq", scrutinee, lit), 1)
		case *ast.WildcardPattern:
		case *ast.BindingPattern:
			if pattern.Name != nil && pattern.Name.Value != "_" {
				if tag == nil {
					return nil, -1, "a binding pattern over a scalar", false
				}
				lo.locals[pattern.Name.Value] = &oakLocal{agg: place.copy()}
			}
		default:
			return nil, -1, fmt.Sprintf("the pattern %s", arm.Pattern.String()), false
		}
		// The arm runs when its pattern matches and no earlier one did.
		armPath := notTerm(taken)
		if cond != nil {
			armPath = binaryTerm("and", armPath, cond)
			taken = binaryTerm("or", taken, cond)
		}
		restore := lo.underPath(armPath)
		reason, ok := visit(i, arm.Body)
		restore()
		if !ok {
			return nil, -1, reason, false
		}
		if cond == nil {
			fallback = i
			break
		}
		cases = append(cases, matchArm{cond: cond, index: i})
	}
	if fallback < 0 {
		if len(cases) == 0 {
			return nil, -1, "a match without arms", false
		}
		fallback = cases[len(cases)-1].index
		cases = cases[:len(cases)-1]
	}
	return cases, fallback, "", true
}

// selectMatch lowers a match to a value: each arm's body under its
// condition, merged leaf-wise into the fallback.
func (lo *oakLowering) selectMatch(match *ast.MatchExpression, body func(ast.Expression) (*oakValue, string, bool)) (*oakValue, string, bool) {
	values := map[int]*oakValue{}
	cases, fallback, reason, ok := lo.matchArms(match, func(index int, armBody ast.Expression) (string, bool) {
		value, reason, ok := body(armBody)
		if !ok {
			return reason, false
		}
		values[index] = value
		return "", true
	})
	if !ok {
		return nil, reason, false
	}
	result := values[fallback]
	for i := len(cases) - 1; i >= 0; i-- {
		result = mergeValues(cases[i].cond, values[cases[i].index], result)
	}
	return result, "", true
}

// aggregateChain reports an access chain rooted at an aggregate local.
func (lo *oakLowering) aggregateChain(expr ast.Expression) bool {
	switch e := expr.(type) {
	case *ast.Identifier:
		return lo.aggregateLocal(e.Value)
	case *ast.IndexExpression:
		return lo.aggregateChain(e.Left)
	}
	return false
}

// aggregateLocal reports a local holding an aggregate.
func (lo *oakLowering) aggregateLocal(name string) bool {
	local, isLocal := lo.locals[name]
	return isLocal && local.agg != nil
}

// hasAggregates reports an aggregate local in scope (the loop machinery
// carries scalars only).
func (lo *oakLowering) hasAggregates() bool {
	for _, local := range lo.locals {
		if local.agg != nil {
			return true
		}
	}
	return false
}

// declareLocal binds a declaration: a scalar at its width, or an aggregate
// from its initializer (an array without one is zero-filled, as both
// backends fill it).
func (lo *oakLowering) declareLocal(s *ast.VariableDeclaration) (string, bool) {
	if s.Type == nil {
		return "a local without a type", false
	}
	typ, ok := lo.oakTypeOf(s.Type)
	if !ok {
		return fmt.Sprintf("a local of type %s", typeText(s.Type)), false
	}
	if typ.kind == oakScalar {
		if s.Value == nil {
			return "a local without both a type and an initializer", false
		}
		if text := typeText(s.Type); text == "f32" || text == "f64" {
			lo.floats[s.Name.Value] = typ.width
		} else {
			delete(lo.floats, s.Name.Value)
		}
		value, reason, ok := lo.lower(s.Value, typ.width)
		if !ok {
			return reason, false
		}
		lo.locals[s.Name.Value] = &oakLocal{value: value, width: typ.width, signed: typ.signed}
		return "", true
	}
	if s.Value == nil {
		if typ.kind != oakArray {
			return fmt.Sprintf("the %s local %s without an initializer", typ.name, s.Name.Value), false
		}
		lo.locals[s.Name.Value] = &oakLocal{agg: zeroValue(typ)}
		return "", true
	}
	value, reason, ok := lo.aggregateValue(s.Value, typ)
	if !ok {
		return reason, false
	}
	lo.locals[s.Name.Value] = &oakLocal{agg: value}
	return "", true
}

// assignPlace stores into a place: a scalar leaf at its width, an
// aggregate by copy.
func (lo *oakLowering) assignPlace(target *oakValue, value ast.Expression) (string, bool) {
	if target.typ.kind == oakScalar {
		t, reason, ok := lo.lower(value, target.typ.width)
		if !ok {
			return reason, false
		}
		target.scalar = t
		return "", true
	}
	fresh, reason, ok := lo.aggregateValue(value, target.typ)
	if !ok {
		return reason, false
	}
	target.fields, target.elems = fresh.fields, fresh.elems
	return "", true
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
				if reason, isAssert, ok := lo.lowerAssert(s.Expression); isAssert {
					if !ok {
						return nil, reason, false
					}
					continue
				}
				return nil, "an expression statement before the end of a block", false
			}
			return lo.lower(s.Expression, width)
		case *ast.VariableDeclaration:
			if reason, ok := lo.declareLocal(s); !ok {
				return nil, reason, false
			}
		case *ast.AssignmentStatement:
			if reason, ok := lo.assignLocal(s); !ok {
				return nil, reason, false
			}
		case *ast.IndexAssignmentStatement:
			if reason, ok := lo.assignIndexed(s); !ok {
				return nil, reason, false
			}
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

// assignLocal executes `x = e`: a scalar local at its width, an aggregate
// local by copy.
func (lo *oakLowering) assignLocal(s *ast.AssignmentStatement) (string, bool) {
	local, isLocal := lo.locals[s.Name.Value]
	if !isLocal {
		return fmt.Sprintf("an assignment to %s (not a local)", s.Name.Value), false
	}
	if local.agg != nil {
		return lo.assignPlace(local.agg, s.Value)
	}
	value, reason, ok := lo.lower(s.Value, local.width)
	if !ok {
		return reason, false
	}
	local.value = value
	return "", true
}

// assignIndexed executes `p.f = e` / `arr[k] = e` / `pool[k].f = e` over
// aggregate locals.
func (lo *oakLowering) assignIndexed(s *ast.IndexAssignmentStatement) (string, bool) {
	target, reason, ok := lo.placeOf(s.Target)
	if !ok {
		return reason, false
	}
	return lo.assignPlace(target, s.Value)
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
			if reason, ok := lo.assignLocal(s); !ok {
				return reason, false
			}
		case *ast.IndexAssignmentStatement:
			if reason, ok := lo.assignIndexed(s); !ok {
				return reason, false
			}
		case *ast.WhileStatement:
			if reason, ok := lo.lowerWhile(s); !ok {
				return reason, false
			}
		case *ast.VariableDeclaration:
			// A body-local (the inner loop's counter), redeclared each iteration.
			if reason, ok := lo.declareLocal(s); !ok {
				return reason, false
			}
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
		return lo.lowerMatchStatement(match)
	}
	cond, reason, ok := lo.lowerCondition(match.Scrutinee)
	if !ok {
		return reason, false
	}
	before := lo.snapshotLocals()
	restore := lo.underPath(cond)
	reason, ok = lo.lowerArm(whenTrue)
	restore()
	if !ok {
		return reason, false
	}
	afterTrue := lo.snapshotLocals()
	lo.restoreLocals(before)
	restore = lo.underPath(notTerm(cond))
	reason, ok = lo.lowerArm(whenFalse)
	restore()
	if !ok {
		return reason, false
	}
	for name, local := range lo.locals {
		snap, seen := afterTrue[name]
		if !seen {
			continue
		}
		if local.agg != nil {
			// Merge leaf-wise: each scalar leaf a select on the condition.
			leaves(snap.agg, local.agg, func(t, f *oakValue) {
				if t.scalar != f.scalar {
					f.scalar = iteTerm(truncate(cond, 1), t.scalar, f.scalar)
				}
			})
			continue
		}
		if snap.value != local.value {
			local.value = iteTerm(truncate(cond, 1), snap.value, local.value)
		}
	}
	return "", true
}

// lowerMatchStatement executes a statement-position match: every arm runs
// on a copy of the locals before it, and the locals after the match are
// the arms' outcomes selected by the arms' conditions, the fallback arm
// standing for every remaining value.
func (lo *oakLowering) lowerMatchStatement(match *ast.MatchExpression) (string, bool) {
	before := lo.snapshotLocals()
	outcomes := map[int]map[string]localSnapshot{}
	cases, fallback, reason, ok := lo.matchArms(match, func(index int, body ast.Expression) (string, bool) {
		lo.restoreLocals(before)
		if reason, ok := lo.lowerArm(body); !ok {
			return reason, false
		}
		outcomes[index] = lo.snapshotLocals()
		return "", true
	})
	if !ok {
		return reason, false
	}
	lo.restoreLocals(before)
	for name, local := range lo.locals {
		if _, existed := before[name]; !existed {
			continue
		}
		if local.agg != nil {
			merged := outcomes[fallback][name].agg
			for i := len(cases) - 1; i >= 0; i-- {
				merged = mergeValues(cases[i].cond, outcomes[cases[i].index][name].agg, merged)
			}
			local.agg = merged
			continue
		}
		merged := outcomes[fallback][name].value
		for i := len(cases) - 1; i >= 0; i-- {
			if v := outcomes[cases[i].index][name].value; v != merged {
				merged = iteTerm(cases[i].cond, v, merged)
			}
		}
		local.value = merged
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

// localSnapshot is a local's value at a program point: the scalar term, or
// a deep copy of the aggregate.
type localSnapshot struct {
	value *term
	agg   *oakValue
}

func (lo *oakLowering) snapshotLocals() map[string]localSnapshot {
	out := make(map[string]localSnapshot, len(lo.locals))
	for name, local := range lo.locals {
		out[name] = localSnapshot{value: local.value, agg: local.agg.copy()}
	}
	return out
}

func (lo *oakLowering) restoreLocals(values map[string]localSnapshot) {
	for name, snap := range values {
		local := lo.locals[name]
		local.value = snap.value
		if snap.agg != nil {
			local.agg = snap.agg.copy()
		}
	}
}

// scalarType reads a local's declared fixed-width integer type.
func scalarType(expr ast.Expression) (width int, signed bool, ok bool) {
	return contractBits(expr)
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

// inlineCall lowers a call to a program function: the arguments at the
// callee's parameter widths in the caller's scope, then the callee's body
// at its return width with its parameters bound as locals, the result
// adapted to the context by the callee's signedness. Methods, generics,
// foreign and definition-less functions, non-scalar parameters or results,
// and recursion fail closed.
func (lo *oakLowering) inlineCall(callee *ast.FunctionStatement, call *ast.InvocationExpression, width int) (*term, string, bool) {
	name := callee.Name.Value
	if callee.ReturnType == nil {
		return nil, fmt.Sprintf("a call to %s, which returns nothing", name), false
	}
	resultWidth, resultSigned, ok := contractBits(callee.ReturnType)
	if !ok {
		return nil, fmt.Sprintf("a call to %s returning %s in scalar position", name, typeText(callee.ReturnType)), false
	}
	restore, reason, ok := lo.enterCall(callee, call)
	if !ok {
		return nil, reason, false
	}
	defer restore()
	// A tail-recursive callee is the loop it compiles to
	// (docs/spec/85-discipline.md), over its parameters as locals.
	body := callee.Body
	if loop, isTail := tailRecursionAsLoop(callee, body); isTail {
		body = loop
	}
	result, reason, ok := lo.lower(body, resultWidth)
	if !ok {
		return nil, fmt.Sprintf("a call to %s whose body contains %s", name, reason), false
	}
	if resultWidth < width {
		return extendTerm(result, resultWidth, width, resultSigned), "", true
	}
	return truncate(result, width), "", true
}

// inlineCallValue inlines a call whose result is a record or a sum type
// (docs/spec/125-verification.md section 3): the body as an aggregate
// value, the arms of its matches merged leaf by leaf.
func (lo *oakLowering) inlineCallValue(callee *ast.FunctionStatement, call *ast.InvocationExpression, typ *oakType) (*oakValue, string, bool) {
	name := callee.Name.Value
	if callee.ReturnType == nil {
		return nil, fmt.Sprintf("a call to %s, which returns nothing", name), false
	}
	returned, ok := lo.oakTypeOf(callee.ReturnType)
	if !ok || returned != typ {
		return nil, fmt.Sprintf("a call to %s returning %s where %s is expected", name, typeText(callee.ReturnType), typ.name), false
	}
	restore, reason, ok := lo.enterCall(callee, call)
	if !ok {
		return nil, reason, false
	}
	defer restore()
	value, reason, ok := lo.aggregateValue(callee.Body, typ)
	if !ok {
		return nil, fmt.Sprintf("a call to %s whose body contains %s", name, reason), false
	}
	return value, "", true
}

// enterCall binds a callee's parameters to the call's arguments as the
// callee's locals — scalars by value, records and sum types by value
// (a copy), a span or view of a caller's aggregate array as an alias, so
// the callee's writes through it reach the caller — and returns the
// function that restores the caller's scope.
func (lo *oakLowering) enterCall(callee *ast.FunctionStatement, call *ast.InvocationExpression) (func(), string, bool) {
	name := callee.Name.Value
	if callee.Receiver != nil || len(callee.TypeParams) != 0 || callee.Body == nil || callee.ExternSymbol != "" {
		return nil, fmt.Sprintf("a call to %s (a method, generic, foreign, or definition-less function)", name), false
	}
	if len(call.Arguments) != len(callee.Parameters) {
		return nil, fmt.Sprintf("a call to %s with %d arguments", name, len(call.Arguments)), false
	}
	if lo.inlining[name] {
		return nil, fmt.Sprintf("a recursive call to %s", name), false
	}
	bound := map[string]*oakLocal{}
	calleeFloats := map[string]int{}
	// A span or view parameter borrows a caller's array: the callee works
	// on a copy and, since the conditional lowering re-points locals at
	// copies, the final contents are written back leaf by leaf on return.
	type borrow struct {
		param string
		owner *oakValue
	}
	var borrows []borrow
	for i, param := range callee.Parameters {
		if param.Variadic {
			return nil, fmt.Sprintf("a call to %s: parameter %s is variadic", name, param.Name.Value), false
		}
		arg := call.Arguments[i]
		if isBorrowType(param.Type) {
			owner := addressOfOperand(arg)
			local, isLocal := lo.locals[owner]
			if !isLocal || local.agg == nil || local.agg.typ.kind != oakArray {
				return nil, fmt.Sprintf("a call to %s: the span argument %s is not a borrow of an aggregate local", name, arg.String()), false
			}
			bound[param.Name.Value] = &oakLocal{agg: local.agg.copy()}
			if isWritableSpan(param.Type) {
				borrows = append(borrows, borrow{param: param.Name.Value, owner: local.agg})
			}
			continue
		}
		if w, signed, isScalar := contractBits(param.Type); isScalar {
			value, reason, ok := lo.lower(arg, w)
			if !ok {
				return nil, reason, false
			}
			bound[param.Name.Value] = &oakLocal{value: value, width: w, signed: signed}
			if text := typeText(param.Type); text == "f32" || text == "f64" {
				calleeFloats[param.Name.Value] = w
			}
			continue
		}
		typ, ok := lo.oakTypeOf(param.Type)
		if !ok || typ.kind == oakScalar {
			return nil, fmt.Sprintf("a call to %s: parameter %s is not a fixed-width scalar, record, or sum type", name, param.Name.Value), false
		}
		value, reason, ok := lo.valueOf(arg, typ)
		if !ok {
			return nil, reason, false
		}
		bound[param.Name.Value] = &oakLocal{agg: value}
	}
	saved := lo.locals
	savedFloats := lo.floats
	lo.locals = bound
	lo.floats = calleeFloats
	if lo.inlining == nil {
		lo.inlining = map[string]bool{}
	}
	lo.inlining[name] = true
	return func() {
		lo.floats = savedFloats
		for _, b := range borrows {
			if final, has := lo.locals[b.param]; has && final.agg != nil {
				leaves(final.agg, b.owner, func(from, to *oakValue) { to.scalar = from.scalar })
			}
		}
		delete(lo.inlining, name)
		lo.locals = saved
	}, "", true
}

// isWritableSpan recognizes `[*]T`, the borrow a callee may write through.
func isWritableSpan(expr ast.Expression) bool {
	index, isIndex := expr.(*ast.IndexExpression)
	if !isIndex || index.Dot {
		return false
	}
	marker, isMarker := index.Index.(*ast.Identifier)
	return isMarker && marker.Value == "*"
}

// isBorrowType recognizes a view or span type, `[]T` or `[*]T`, whatever
// the element.
func isBorrowType(expr ast.Expression) bool {
	index, isIndex := expr.(*ast.IndexExpression)
	if !isIndex || index.Dot {
		return false
	}
	marker, isMarker := index.Index.(*ast.Identifier)
	return isMarker && (marker.Value == "" || marker.Value == "*")
}

// addressOfOperand names the local a `span(&x)` / `view(&x)` argument
// borrows, or a bare span local passed on.
func addressOfOperand(arg ast.Expression) string {
	if call, isCall := arg.(*ast.InvocationExpression); isCall && len(call.Arguments) == 1 {
		if fn, isIdent := call.Function.(*ast.Identifier); isIdent && (fn.Value == "span" || fn.Value == "view") {
			if prefix, isPrefix := call.Arguments[0].(*ast.PrefixExpression); isPrefix && prefix.Operator == "&" {
				if ident, isIdent := prefix.Right.(*ast.Identifier); isIdent {
					return ident.Value
				}
			}
		}
	}
	if ident, isIdent := arg.(*ast.Identifier); isIdent {
		return ident.Value
	}
	return ""
}

// lowerGuard lowers a refinement's construction Name(e): the argument at
// the base width, the predicate over it recorded as a trap obligation (the
// construction traps when the predicate fails; the decider proves every
// recorded trap impossible, or reports the input that reaches it).
func (lo *oakLowering) lowerGuard(name string, guard Guard, arg ast.Expression, width int) (*term, string, bool) {
	if !lo.trapsTracked {
		return nil, fmt.Sprintf("a construction of %s", name), false
	}
	baseWidth, signed, ok := contractBits(guard.Base)
	if !ok {
		return nil, fmt.Sprintf("a construction of %s over %s", name, typeText(guard.Base)), false
	}
	value, reason, ok := lo.lower(arg, baseWidth)
	if !ok {
		return nil, reason, false
	}
	saved := lo.locals
	lo.locals = map[string]*oakLocal{"value": {value: value, width: baseWidth, signed: signed}}
	holds, reason, ok := lo.lowerCondition(guard.Predicate)
	lo.locals = saved
	if !ok {
		return nil, fmt.Sprintf("a construction of %s whose predicate contains %s", name, reason), false
	}
	lo.addTrap(binaryTerm("xor", truncate(holds, 1), constTerm(1, 1)))
	if baseWidth < width {
		return extendTerm(value, baseWidth, width, signed), "", true
	}
	return truncate(value, width), "", true
}

// instructionFunction recognizes a call to a scalar arm64 instruction
// function and names the verifier's term for it with its operand width.
func instructionFunction(call *ast.InvocationExpression) (op string, width int, ok bool) {
	access, isDot := call.Function.(*ast.IndexExpression)
	if !isDot || !access.Dot || len(call.Arguments) != 1 {
		return "", 0, false
	}
	library, isLibrary := access.Left.(*ast.Identifier)
	member, isMember := access.Index.(*ast.Identifier)
	if !isLibrary || !isMember || library.Value != "arm64" {
		return "", 0, false
	}
	switch member.Value {
	case "rev32":
		return "rev", 32, true
	case "rev64":
		return "rev", 64, true
	case "rbit32":
		return "rbit", 32, true
	case "rbit64":
		return "rbit", 64, true
	case "clz32":
		return "clz", 32, true
	case "clz64":
		return "clz", 64, true
	case "cnt32":
		return "cnt", 32, true
	case "cnt64":
		return "cnt", 64, true
	}
	return "", 0, false
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
			if local.agg != nil {
				return nil, fmt.Sprintf("the aggregate %s in scalar position", e.Value), false
			}
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
	case *ast.FloatLiteral:
		if t, ok := floatLiteralBits(e.Value, width); ok {
			return t, "", true
		}
		return nil, "a float literal outside a float context", false
	case *ast.PrefixExpression:
		switch e.Operator {
		case "!":
			// A negated condition in value position: 1 or 0 at the width.
			cond, reason, ok := lo.lowerCondition(e)
			if !ok {
				return nil, reason, false
			}
			return zeroExtend(truncate(cond, 1), width), "", true
		case "^":
			operand, reason, ok := lo.lower(e.Right, width)
			if !ok {
				return nil, reason, false
			}
			return binaryTerm("xor", operand, constTerm(mask(width), width)), "", true
		case "-":
			operand, reason, ok := lo.lower(e.Right, width)
			if !ok {
				return nil, reason, false
			}
			if _, isFloat := lo.floatWidthOf(e.Right); isFloat {
				// Negation of a float flips the sign bit (total, NaN included).
				return binaryTerm("xor", operand, constTerm(uint64(1)<<uint(width-1), width)), "", true
			}
			// Unary minus wraps at the width (two's complement), as the
			// backend's `neg` does.
			return binaryTerm("sub", constTerm(0, width), operand), "", true
		}
		return nil, fmt.Sprintf("prefix operator %s", e.Operator), false
	case *ast.Boolean:
		// Bool lowers to its C representation: 1 or 0 at the result width.
		if e.Value {
			return constTerm(1, width), "", true
		}
		return constTerm(0, width), "", true
	case *ast.IndexExpression:
		if lo.aggregateChain(e) {
			// A scalar leaf of an aggregate local: a field or a constant-index element.
			leaf, reason, ok := lo.placeOf(e)
			if !ok {
				return nil, reason, false
			}
			if leaf.typ.kind != oakScalar {
				return nil, fmt.Sprintf("the aggregate %s in scalar position", e.String()), false
			}
			return adaptWidth(leaf.scalar, width), "", true
		}
		element, _, reason, ok := lo.spanElementTerm(e)
		if !ok {
			return nil, reason, false
		}
		return adaptWidth(element, width), "", true
	case *ast.InvocationExpression:
		// The scalar instruction functions (docs/spec/92-ffi.md section 3.2)
		// are the verifier's own unary instruction terms — the ISA lowering
		// and the Oak lowering share their semantics (Oak.Intrinsics).
		if member, memberWidth, isInstruction := instructionFunction(e); isInstruction {
			operand, reason, ok := lo.lower(e.Arguments[0], memberWidth)
			if !ok {
				return nil, reason, false
			}
			value := binaryTerm(member, truncate(operand, memberWidth), constTerm(0, memberWidth))
			if memberWidth < width {
				return zeroExtend(value, width), "", true
			}
			return truncate(value, width), "", true
		}
		if ident, isIdent := e.Function.(*ast.Identifier); isIdent && ident.Value == "len" && len(e.Arguments) == 1 && lo.aggregateChain(e.Arguments[0]) {
			// len of an owned array: its declared length.
			place, reason, ok := lo.placeOf(e.Arguments[0])
			if !ok {
				return nil, reason, false
			}
			if place.typ.kind != oakArray {
				return nil, "len of a non-array aggregate", false
			}
			return constTerm(uint64(place.typ.length), width), "", true
		}
		if name, isLen := lo.spanLength(e); isLen {
			if value, isConcrete := lo.concrete[name]; isConcrete {
				return constTerm(value, width), "", true
			}
			return zeroExtend(truncate(paramTerm(name, 32), width), width), "", true
		}
		// A call to a program function in the subset is inlined
		// (docs/spec/125-verification.md §3).
		if ident, isIdent := e.Function.(*ast.Identifier); isIdent {
			if callee, known := lo.functions[ident.Value]; known {
				return lo.inlineCall(callee, e, width)
			}
			if guard, isGuard := lo.guards[ident.Value]; isGuard && len(e.Arguments) == 1 {
				return lo.lowerGuard(ident.Value, guard, e.Arguments[0], width)
			}
			if typechecker.FloatIntrinsicName(ident.Value) {
				return lo.lowerFloatIntrinsic(ident.Value, e, width)
			}
		}
		// Primitive constructors (u32(x), widening) and the explicit
		// conversions {target}_trunc_{source} / {target}_bits_{source}.
		ident, isIdent := e.Function.(*ast.Identifier)
		if !isIdent || len(e.Arguments) != 1 {
			return nil, "a call", false
		}
		target := ""
		switch ident.Value {
		case "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64":
			target = ident.Value
		default:
			if t, op, _, isConv := typechecker.ConversionParts(ident.Value); isConv && (op == "trunc" || op == "bits") {
				target = t
			}
		}
		if target != "" {
			targetBits, targetSigned, _ := contractBits(&ast.Identifier{Value: target})
			// The operand at its own width; widening extends by the
			// operand's signedness, narrowing keeps the low bits; then the
			// converted value sits in the context at the target's signedness.
			var converted *term
			if srcWidth, srcSigned, known := lo.operandContract(e.Arguments[0]); known {
				operand, reason, ok := lo.lower(e.Arguments[0], srcWidth)
				if !ok {
					return nil, reason, false
				}
				if srcWidth < targetBits {
					converted = extendTerm(operand, srcWidth, targetBits, srcSigned)
				} else {
					converted = truncate(operand, targetBits)
				}
			} else {
				operand, reason, ok := lo.lower(e.Arguments[0], targetBits)
				if !ok {
					return nil, reason, false
				}
				converted = operand
			}
			if targetBits < width {
				return extendTerm(converted, targetBits, width, targetSigned), "", true
			}
			return truncate(converted, width), "", true
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
		if _, isFloat := lo.floatWidthOf(e.Left); isFloat {
			return nil, fmt.Sprintf("floating-point %s (not a bit operation)", e.Operator), false
		}
		if _, isFloat := lo.floatWidthOf(e.Right); isFloat {
			return nil, fmt.Sprintf("floating-point %s (not a bit operation)", e.Operator), false
		}
		if e.Operator == "/" || e.Operator == "%" {
			// Unsigned division and remainder by a constant power of two
			// are a shift and a mask; anything else stays outside the
			// subset (the Lean projection states it).
			if _, signed, isScalar := lo.operandContract(e); isScalar && !signed {
				right, reason, okR := lo.lower(e.Right, width)
				if !okR {
					return nil, reason, false
				}
				if right.kind == termConst && right.value != 0 && right.value&(right.value-1) == 0 {
					left, reason, okL := lo.lower(e.Left, width)
					if !okL {
						return nil, reason, false
					}
					if e.Operator == "%" {
						return binaryTerm("and", left, constTerm(right.value-1, width)), "", true
					}
					return binaryTerm("shr", left, constTerm(uint64(bits.TrailingZeros64(right.value)), width)), "", true
				}
			}
			return nil, fmt.Sprintf("operator %s (only by an unsigned constant power of two)", e.Operator), false
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
			// Oak traps at the width; the machine wraps the count. Under
			// the theorem decider the trap is a recorded obligation and
			// the shift below the width is the machine's.
			if !lo.trapsTracked {
				return nil, "a non-constant shift count", false
			}
			lo.addTrap(cmpTerm("hs", right, constTerm(uint64(width), width)))
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
			value, reason, ok := lo.selectMatch(e, func(body ast.Expression) (*oakValue, string, bool) {
				t, reason, ok := lo.lower(body, width)
				if !ok {
					return nil, reason, false
				}
				return &oakValue{typ: &oakType{kind: oakScalar, width: width}, scalar: t}, "", true
			})
			if !ok {
				return nil, reason, false
			}
			return value.scalar, "", true
		}
		cond, reason, ok := lo.lowerCondition(e.Scrutinee)
		if !ok {
			return nil, reason, false
		}
		restore := lo.underPath(cond)
		left, reason, okL := lo.lower(whenTrue, width)
		restore()
		if !okL {
			return nil, reason, false
		}
		restore = lo.underPath(notTerm(cond))
		right, reason, okR := lo.lower(whenFalse, width)
		restore()
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
		// A Bool value in condition position: a parameter, local, or field
		// (its 1/0 representation), or its negation.
		if prefix, isNot := expr.(*ast.PrefixExpression); isNot && prefix.Operator == "!" {
			inner, reason, ok := lo.lowerCondition(prefix.Right)
			if !ok {
				return nil, reason, false
			}
			return binaryTerm("xor", truncate(inner, 1), constTerm(1, 1)), "", true
		}
		if width, _, isScalar := lo.operandContract(expr); isScalar && width == 1 {
			value, reason, ok := lo.lower(expr, 1)
			if !ok {
				return nil, reason, false
			}
			return value, "", true
		}
		return nil, fmt.Sprintf("a condition that is not a comparison (%T)", expr), false
	}
	if infix.Operator == "&&" || infix.Operator == "||" {
		left, reason, okL := lo.lowerCondition(infix.Left)
		if !okL {
			return nil, reason, false
		}
		// The right operand runs only when the left one did not decide.
		guard := left
		if infix.Operator == "||" {
			guard = notTerm(left)
		}
		restore := lo.underPath(guard)
		right, reason, okR := lo.lowerCondition(infix.Right)
		restore()
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
	if w, isFloat := lo.floatWidthOf(infix.Left); isFloat || func() bool { w, isFloat = lo.floatWidthOf(infix.Right); return isFloat }() {
		// IEEE comparison over the bit patterns (asm/floats_lowering.go).
		if w == 0 {
			if other, ok := lo.floatWidthOf(infix.Right); ok && other != 0 {
				w = other
			} else {
				w = 64
			}
		}
		left, reason, okL := lo.lower(infix.Left, w)
		if !okL {
			return nil, reason, false
		}
		right, reason, okR := lo.lower(infix.Right, w)
		if !okR {
			return nil, reason, false
		}
		compared, ok := floatCompare(infix.Operator, left, right, w)
		if !ok {
			return nil, fmt.Sprintf("float comparison %s", infix.Operator), false
		}
		return compared, "", true
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
		if lo.aggregateChain(e) {
			if leaf, _, ok := lo.placeOf(e); ok && leaf.typ.kind == oakScalar {
				return leaf.typ.width, leaf.typ.signed, true
			}
			return 0, false, false
		}
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
		if ident, isIdent := e.Function.(*ast.Identifier); isIdent && ident.Value == "len" && len(e.Arguments) == 1 && lo.aggregateChain(e.Arguments[0]) {
			return 32, false, true
		}
		// A call to a program function has its return type's width; an
		// instruction function its member's; a conversion or constructor
		// its target's; a float intrinsic its operands' (Bool for the
		// classifiers and total_order).
		if ident, isIdent := e.Function.(*ast.Identifier); isIdent {
			if callee, known := lo.functions[ident.Value]; known && callee.ReturnType != nil {
				if w, signed, ok := contractBits(callee.ReturnType); ok {
					return w, signed, true
				}
			}
			if _, known := lo.functions[ident.Value]; !known {
				if target, _, _, isConv := typechecker.ConversionParts(ident.Value); isConv {
					if w, signed, ok := contractBits(&ast.Identifier{Value: target}); ok {
						return w, signed, true
					}
				}
				if w, signed, ok := contractBits(ident); ok && len(e.Arguments) == 1 {
					return w, signed, true
				}
				if typechecker.FloatIntrinsicName(ident.Value) {
					switch ident.Value {
					case "is_nan", "is_finite", "is_infinite", "is_normal", "total_order":
						return 1, false, true
					}
					return lo.floatArgumentWidth(e, 0), false, true
				}
			}
		}
		if _, w, isInstruction := instructionFunction(e); isInstruction {
			return w, false, true
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
		values := []uint64{0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 127, 128, 255, 256, m - 1, m, m >> 1, (m >> 1) + 1}
		for i := range values {
			values[i] &= m // a witness is a value of the parameter's width
		}
		return values
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
				env[extra] = (a ^ b) & mask(widths[extra])
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
	if asmTerm == trapPath {
		return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (every path traps) — trusted per docs/spec/94-assembler.md §5", fn.Name)}
	}
	lowering := prepareLowering(fn, sig, nil)
	// A tail-recursive body is the loop it compiles to (docs/spec/85-discipline.md).
	if loop, isTail := tailRecursionAsLoop(sig, oakBody); isTail {
		oakBody = loop
	}
	oakTerm, width, reason, ok := lowering.resultTerm(fn, sig, oakBody)
	if !ok {
		return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (the Oak body contains %s) — trusted per docs/spec/94-assembler.md §5", fn.Name, reason)}
	}
	asmTerm = maskResult(fn, sig, asmTerm)
	if len(exec.loops) > 0 || len(lowering.loops) > 0 {
		return verifyLoops(fn, sig, oakBody, exec, lowering, asmTerm, oakTerm, width)
	}
	return decideEqual(fn, lowering, asmTerm, oakTerm, width, "")
}

// prepareLowering builds the Oak side for a function: the signature's
// contract, the program's declarations, the record and union parameters as
// aggregates, and (in a witness run) the concrete inputs.
func prepareLowering(fn *Function, sig *ast.FunctionStatement, concrete map[string]uint64) *oakLowering {
	lowering := newLowering(sig)
	lowering.records, lowering.adts = fn.Records, fn.ADTs
	lowering.concrete = concrete
	lowering.bindAggregateParams(sig)
	return lowering
}

// resultComposite is the function's record or union result when the
// executor binds it (one register chunk), with its leaves.
func resultComposite(fn *Function, sig *ast.FunctionStatement) ([]compositeLeaf, bool) {
	name := typeText(sig.ReturnType)
	comp, isComposite := fn.Composites[name]
	if !isComposite || len(comp.Fields) == 0 || comp.Size > 8 {
		return nil, false
	}
	leaves, _, ok := compositeLeaves(fn.Composites, name, "", 0, nil)
	return leaves, ok
}

// resultTerm lowers the Oak body to the term the executor's result is
// compared with: a scalar at the contract width, or a one-chunk record
// packed from its leaves (width 64).
func (lo *oakLowering) resultTerm(fn *Function, sig *ast.FunctionStatement, oakBody ast.Expression) (*term, int, string, bool) {
	if leaves, isComposite := resultComposite(fn, sig); isComposite {
		typ, ok := lo.oakTypeOf(sig.ReturnType)
		if !ok || typ.kind == oakScalar {
			return nil, 0, "a result whose type has no model", false
		}
		value, reason, ok := lo.aggregateValue(oakBody, typ)
		if !ok {
			return nil, 0, reason, false
		}
		packed, ok := packAggregate(value, leaves)
		if !ok {
			return nil, 0, "a record result with a leaf the layout lacks", false
		}
		return packed, 64, "", true
	}
	width, _, _ := contractBits(sig.ReturnType)
	t, reason, ok := lo.lower(oakBody, width)
	return t, width, reason, ok
}

// maskResult hides the padding bytes of a one-chunk record result (the Oak
// side never reads them, so the comparison is over the fields alone).
func maskResult(fn *Function, sig *ast.FunctionStatement, asmTerm *term) *term {
	leaves, isComposite := resultComposite(fn, sig)
	if !isComposite {
		return asmTerm
	}
	return binaryTerm("and", zeroExtend(asmTerm, 64), constTerm(leafMask(leaves, 0), 64))
}

// compositeParamLeaves names every leaf of the record and union
// parameters (witness runs assign them like scalars).
func compositeParamLeaves(fn *Function, sig *ast.FunctionStatement) []string {
	var names []string
	for _, param := range sig.Parameters {
		if comp, isComposite := fn.Composites[typeText(param.Type)]; isComposite && len(comp.Fields) > 0 {
			if leaves, _, ok := compositeLeaves(fn.Composites, typeText(param.Type), param.Name.Value, 0, nil); ok {
				for _, leaf := range leaves {
					names = append(names, leaf.name)
				}
			}
		}
	}
	return names
}

// tailRecursionAsLoop rewrites a tail-recursive body `c ? v | f(args)` (or
// `c ? f(args) | v`) into the loop it denotes — the parameters as locals,
// `while <continue> { fresh temporaries for the arguments; parameters =
// temporaries }`, then the value arm — so the verifier's loop machinery
// couples it with the backend's loop. Only scalar parameters qualify.
func tailRecursionAsLoop(sig *ast.FunctionStatement, body ast.Expression) (ast.Expression, bool) {
	if block, isBlock := body.(*ast.BlockExpression); isBlock {
		if block.Block == nil || len(block.Block.Statements) != 1 {
			return nil, false
		}
		es, isExpr := block.Block.Statements[0].(*ast.ExpressionStatement)
		if !isExpr {
			return nil, false
		}
		body = es.Expression
	}
	match, isMatch := body.(*ast.MatchExpression)
	if !isMatch {
		return nil, false
	}
	whenTrue, whenFalse, isBool := boolConditional(match)
	if !isBool {
		return nil, false
	}
	isSelf := func(expr ast.Expression) (*ast.InvocationExpression, bool) {
		call, isCall := expr.(*ast.InvocationExpression)
		if !isCall {
			return nil, false
		}
		ident, isIdent := call.Function.(*ast.Identifier)
		return call, isIdent && sig.Name != nil && ident.Value == sig.Name.Value && len(call.Arguments) == len(sig.Parameters)
	}
	tail, tailIsTrue := isSelf(whenTrue)
	if _, falseIsSelf := isSelf(whenFalse); falseIsSelf == tailIsTrue {
		return nil, false // both arms or neither
	}
	value := whenFalse
	if !tailIsTrue {
		tail, _ = isSelf(whenFalse)
		value = whenTrue
	}
	continueWhile := match.Scrutinee
	if !tailIsTrue {
		negated, ok := negateCondition(match.Scrutinee)
		if !ok {
			return nil, false
		}
		continueWhile = negated
	}
	var statements []ast.Statement
	var updates []ast.Statement
	for i, param := range sig.Parameters {
		if _, _, ok := contractBits(param.Type); !ok {
			return nil, false
		}
		name := param.Name
		// The parameter becomes a local of its own type, initialized from itself.
		statements = append(statements, &ast.VariableDeclaration{Token: name.Token, Name: name, Type: param.Type, Value: &ast.Identifier{Token: name.Token, Value: name.Value}})
		temp := &ast.Identifier{Token: name.Token, Value: name.Value + "#next"}
		updates = append(updates, &ast.VariableDeclaration{Token: name.Token, Name: temp, Type: param.Type, Value: tail.Arguments[i]})
	}
	for _, param := range sig.Parameters {
		name := param.Name
		updates = append(updates, &ast.AssignmentStatement{Token: name.Token, Name: name, Value: &ast.Identifier{Token: name.Token, Value: name.Value + "#next"}})
	}
	statements = append(statements, &ast.WhileStatement{Token: match.Token, Condition: continueWhile, Body: &ast.BlockStatement{Token: match.Token, Statements: updates}})
	statements = append(statements, &ast.ExpressionStatement{Token: match.Token, Expression: value})
	return &ast.BlockExpression{Token: match.Token, Block: &ast.BlockStatement{Token: match.Token, Statements: statements}}, true
}

var negatedComparison = map[string]string{"==": "!=", "!=": "==", "<": ">=", ">=": "<", "<=": ">", ">": "<="}

// negateCondition negates a condition built from comparisons with `&&`
// and `||` (De Morgan), the shapes lowerCondition reads.
func negateCondition(expr ast.Expression) (ast.Expression, bool) {
	infix, isInfix := expr.(*ast.InfixExpression)
	if !isInfix {
		return nil, false
	}
	switch infix.Operator {
	case "&&", "||":
		left, okL := negateCondition(infix.Left)
		right, okR := negateCondition(infix.Right)
		if !okL || !okR {
			return nil, false
		}
		op := "||"
		if infix.Operator == "||" {
			op = "&&"
		}
		return &ast.InfixExpression{Token: infix.Token, Left: left, Operator: op, Right: right}, true
	}
	if negated, ok := negatedComparison[infix.Operator]; ok {
		return &ast.InfixExpression{Token: infix.Token, Left: infix.Left, Operator: negated, Right: infix.Right}, true
	}
	return nil, false
}

// newLowering builds the Oak-side contract from the signature.
func newLowering(sig *ast.FunctionStatement) *oakLowering {
	lowering := &oakLowering{params: map[string]int{}, signed: map[string]bool{}, spans: map[string]spanContract{}, fresh: map[string]int{}, floats: map[string]int{}}
	for _, param := range sig.Parameters {
		if elem, _, isSpan := spanShape(param.Type); isSpan {
			elemType := typeText(param.Type.(*ast.IndexExpression).Left)
			lowering.spans[param.Name.Value] = spanContract{elemWidth: int(elem) * 8, signed: strings.HasPrefix(elemType, "i")}
			continue
		}
		bits, signed, _ := contractBits(param.Type)
		lowering.params[param.Name.Value] = bits
		lowering.signed[param.Name.Value] = signed
		if text := typeText(param.Type); text == "f32" || text == "f64" {
			lowering.floats[param.Name.Value] = bits
		}
		if bits < 32 {
			lowering.fresh[upperBitsName(param.Name.Value)] = 32 - bits
		}
	}
	return lowering
}

// contractBits is the width in bits of a scalar contract type (u8 → 8,
// Bool → 1, u32 → 32, ...) and its signedness. The verifier models a
// value at exactly its type's width; the register carrying it is wider.
func contractBits(expr ast.Expression) (bits int, signed bool, ok bool) {
	switch typeText(expr) {
	case "u8", "byte":
		return 8, false, true
	case "i8":
		return 8, true, true
	case "u16":
		return 16, false, true
	case "i16":
		return 16, true, true
	case "u32", "rune":
		return 32, false, true
	case "i32":
		return 32, true, true
	case "u64":
		return 64, false, true
	case "i64":
		return 64, true, true
	case "Bool":
		return 1, false, true
	case "f32":
		// A float is its IEEE bit pattern to the decider (asm/floats_lowering.go).
		return 32, false, true
	case "f64":
		return 64, false, true
	}
	return 0, false, false
}

// upperBitsName names the unspecified register bits above a narrow
// parameter (`a#hi`): a parameter of the verification like any other.
func upperBitsName(param string) string { return param + "#hi" }

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
	collectParamsVisited(t, into, map[*term]bool{})
}

func collectParamsVisited(t *term, into map[string]bool, visited map[*term]bool) {
	if t == nil || visited[t] {
		return
	}
	visited[t] = true // terms are DAGs: visit every shared subterm once
	switch t.kind {
	case termParam:
		into[t.name] = true
		return
	case termConst:
		return
	}
	collectParamsVisited(t.cond, into, visited)
	collectParamsVisited(t.left, into, visited)
	collectParamsVisited(t.right, into, visited)
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
