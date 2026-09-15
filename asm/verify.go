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
	"math"
	"math/bits"
	"os"
	"sort"
	"strconv"
	"strings"
	"sync/atomic"
	"time"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/semir"
)

// Verdict is the outcome of verifying one asm function against its Oak body.
type Verdict struct {
	Kind    VerdictKind
	Message string
	// Callees are the program functions the verdict took at their Oak
	// bodies (call summaries, docs/spec/94-assembler.md §8): a proven
	// verdict is relative to theirs, so the verified profile accepts the
	// body only when every one of them is proven too (compiler.verifiedProfile).
	Callees []string
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
	// termFloat is a floating-point operation (op over the IEEE bit
	// patterns left, right, cond — up to three operands, the third in
	// cond) at the result width: evaluated as the IEEE operation on a
	// witness, decided as an uninterpreted function (asm/floats_ops.go,
	// Oak.Uninterpreted).
	termFloat
	// termQuant is a bounded quantifier over a fresh parameter (name, its
	// width in value): op "forall" or "exists", left the 1-bit body
	// (docs/spec/10-syntax.md section 3e). A witness enumerates the
	// domain; the blaster eliminates the parameter's variables from the
	// body's diagram bit by bit (asm/blast.go).
	termQuant
)

// quantTerm is the quantifier op over the bound parameter name of the
// given width, body a 1-bit term; right is the parameter's own term, so a
// serialization numbers it before the terms that read it (the Oak
// solver's evaluator restarts the body there for every value).
func quantTerm(op, name string, width int, body, param *term) *term {
	return &term{kind: termQuant, width: 1, op: op, name: name, value: uint64(width), left: truncate(body, 1), right: param}
}

// quantifierBound reports a name the theorem lowering minted for a
// quantifier's binder (`x@q1`): a leaf of the blast, never a parameter a
// counterexample names.
func quantifierBound(name string) bool { return strings.Contains(name, "@q") }

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
	if width > 8 {
		// A wider element is, in the bodies the witnesses run, an index
		// or a count into another span (a literal's start, a table
		// offset): kept below the witness lengths (loopWitnessInputs), so
		// the reads it drives fall inside them rather than trap on every
		// input. Bytes keep the whole mix — the high bit matters to them.
		return h % 23
	}
	return h & mask(width)
}

// elementParam decodes an element parameter name v[k].
func elementParam(name string) (span string, k uint64, ok bool) {
	open := strings.IndexByte(name, '[')
	if open <= 0 {
		return "", 0, false
	}
	close := strings.IndexByte(name[open:], ']')
	if close < 0 {
		return "", 0, false
	}
	close += open
	index, err := strconv.ParseUint(name[open+1:close], 10, 64)
	if err != nil {
		return "", 0, false
	}
	// A record span's leaf: `v[k].f` is element k of the memory `v.f`
	// (docs/spec/94-assembler.md §9); the suffix names the leaf.
	return name[:open] + name[close+1:], index, true
}

// recordSpanArg is a span parameter of records: the element size and the
// record's scalar leaves, offsets relative to the element, names starting
// with the dot (`.f`, `.a.b`, `.buf[2]`).
type recordSpanArg struct {
	size   int64
	leaves []compositeLeaf
}

// recordSpanOf recognizes `[*]T` / `[]T` with T a composite of the
// function: isRecordSpan says the shape matched, ok that the leaves model
// it.
func recordSpanOf(comps map[string]Composite, typ ast.Expression) (arg recordSpanArg, reason string, isRecordSpan, ok bool) {
	indexExpr, isIndex := typ.(*ast.IndexExpression)
	if !isIndex || indexExpr.Dot {
		return recordSpanArg{}, "", false, false
	}
	marker, isMarker := indexExpr.Index.(*ast.Identifier)
	if !isMarker || (marker.Value != "*" && marker.Value != "") {
		return recordSpanArg{}, "", false, false
	}
	name := typeText(indexExpr.Left)
	comp, isComposite := comps[name]
	if !isComposite || comp.Size <= 0 {
		return recordSpanArg{}, "", false, false
	}
	leaves, reason, ok := compositeLeaves(comps, name, "", 0, nil)
	if !ok {
		return recordSpanArg{}, reason, true, false
	}
	return recordSpanArg{size: comp.Size, leaves: leaves}, "", true, true
}

// leafAt is the leaf at an offset with a width in bytes (a Bool leaf is
// one bit in its 4-byte cell).
func (arg recordSpanArg) leafAt(offset, size int64) (compositeLeaf, bool) {
	for _, leaf := range arg.leaves {
		if leaf.offset != offset {
			continue
		}
		if int64(leaf.width) == size*8 || (leaf.width == 1 && size == 4) {
			return leaf, true
		}
	}
	return compositeLeaf{}, false
}

// arrayFieldAt is the array field starting at an offset — its leaf-name
// prefix (`.entries`), its length, and its element stride — read off the
// enumerated leaves `.entries[0]`, `.entries[1]`, ….
func (arg recordSpanArg) arrayFieldAt(offset int64) (prefix string, length, stride int64, ok bool) {
	for _, leaf := range arg.leaves {
		if leaf.offset != offset || !strings.HasSuffix(leaf.name, "[0]") {
			continue
		}
		prefix = strings.TrimSuffix(leaf.name, "[0]")
		stride = int64(leaf.width+7) / 8
		if leaf.width == 1 {
			stride = 4
		}
		for _, other := range arg.leaves {
			if strings.HasPrefix(other.name, prefix+"[") {
				length++
			}
		}
		return prefix, length, stride, true
	}
	return "", 0, 0, false
}

// memories lists the span's per-leaf memories: `v.f` for each scalar
// leaf outside an array field, `v.a` for each array field — the names the
// write logs and the loop memory markers use.
func (arg recordSpanArg) memories(span string) []string {
	seen := map[string]bool{}
	var out []string
	for _, leaf := range arg.leaves {
		name := leaf.name
		if open := strings.IndexByte(name, '['); open > 0 {
			name = name[:open]
		}
		if !seen[name] {
			seen[name] = true
			out = append(out, span+name)
		}
	}
	return out
}

// arrayElementLeaf reports a leaf that is element k of an array field
// (`.entries[7]`): the field's memory prefix, k, and the field's length —
// such a leaf lives in the array's memory at the linear index i·N + k, as
// an element read by a register does.
func (arg recordSpanArg) arrayElementLeaf(leaf compositeLeaf) (prefix string, k, length int64, ok bool) {
	open := strings.LastIndexByte(leaf.name, '[')
	if open <= 0 || !strings.HasSuffix(leaf.name, "]") {
		return "", 0, 0, false
	}
	index, err := strconv.ParseInt(leaf.name[open+1:len(leaf.name)-1], 10, 64)
	if err != nil {
		return "", 0, 0, false
	}
	prefix = leaf.name[:open]
	for _, other := range arg.leaves {
		if strings.HasPrefix(other.name, prefix+"[") {
			length++
		}
	}
	return prefix, index, length, true
}

// leafMemory is the memory and index a leaf of element `index` lives at:
// its own memory `v.f` at index, or — an element of an array field — the
// field's memory `v.a` at the linear index i·N + k.
func (arg recordSpanArg) leafMemory(span string, index *term, leaf compositeLeaf) (memory, leafName string, at *term) {
	if prefix, k, length, isElement := arg.arrayElementLeaf(leaf); isElement {
		linear := binaryTerm("add", binaryTerm("mul", truncate(index, 32), constTerm(uint64(length), 32)), constTerm(uint64(k), 32))
		return span + prefix, prefix, linear
	}
	return span + leaf.name, leaf.name, truncate(index, 32)
}

// memoryWidths maps each per-leaf memory of the span (memories) to its
// element width.
func (arg recordSpanArg) memoryWidths(span string) map[string]int {
	out := map[string]int{}
	for _, leaf := range arg.leaves {
		name := leaf.name
		if open := strings.IndexByte(name, '['); open > 0 {
			name = name[:open]
		}
		out[span+name] = leaf.width
	}
	return out
}

// recordFieldTerm is a record span's leaf at an element index: the
// parameter `v[k].f` for a constant index (its witness value the memory
// `v.f` at k), else a select over that memory.
func recordFieldTerm(span string, index *term, leafName string, width int, concrete bool) *term {
	memory := span + leafName
	if index.kind == termConst {
		k := index.value & mask(32)
		if concrete {
			return constTerm(elementValue(memory, k, width), width)
		}
		return paramTerm(spanElemName(span, int64(k))+leafName, width)
	}
	return &term{kind: termSelect, width: width, name: memory, left: truncate(index, 32)}
}

// recordElementOf recognizes a record span element's address: `&v` plus
// the index scaled by the element size — a shift for a power-of-two
// stride, the product of the umaddl otherwise — with any constant offsets
// gathered; also `&v + K` with a constant element. Reports the span, the
// element index, and the byte offset inside the element.
func (x *pathExecutor) recordElementOf(address *term, extra int64) (span string, index *term, offset int64, ok bool) {
	t := address
	offset = extra
	for t != nil && t.kind == termBinary && t.op == "add" && (t.left.kind == termConst || t.right.kind == termConst) {
		if t.right.kind == termConst {
			offset += int64(t.right.value)
			t = t.left
		} else {
			offset += int64(t.left.value)
			t = t.right
		}
	}
	if param, baseOffset, isBase := spanBaseOf(t); isBase {
		arg, isRecord := x.recordSpans[param]
		if !isRecord {
			return "", nil, 0, false
		}
		total := baseOffset + offset
		if total < 0 {
			return "", nil, 0, false
		}
		return param, constTerm(uint64(total/arg.size), 32), total % arg.size, true
	}
	if t == nil || t.kind != termBinary || t.op != "add" {
		return "", nil, 0, false
	}
	for _, sides := range [][2]*term{{t.left, t.right}, {t.right, t.left}} {
		param, baseOffset, isBase := spanBaseOf(sides[0])
		if !isBase {
			continue
		}
		arg, isRecord := x.recordSpans[param]
		if !isRecord {
			return "", nil, 0, false
		}
		scaled := sides[1]
		var idx *term
		switch {
		case scaled.kind == termBinary && scaled.op == "shl" && scaled.right.kind == termConst && int64(1)<<scaled.right.value == arg.size:
			idx = scaled.left
		case scaled.kind == termBinary && scaled.op == "mul" && scaled.right.kind == termConst && int64(scaled.right.value) == arg.size:
			idx = scaled.left
		case scaled.kind == termBinary && scaled.op == "mul" && scaled.left.kind == termConst && int64(scaled.left.value) == arg.size:
			idx = scaled.right
		case arg.size == 1:
			idx = scaled
		default:
			return "", nil, 0, false
		}
		total := baseOffset + offset
		if total < 0 || total >= arg.size {
			return "", nil, 0, false
		}
		return param, truncate(idx, 32), total, true
	}
	return "", nil, 0, false
}

// recordSpanStore executes a store through a record span element's
// address: the leaf at the offset (or the array field's element at the
// linear index) takes the value in its memory's write log, as a scalar
// span's element does (asm/effects.go). Reports whether the store was
// through a record span.
func (x *pathExecutor) recordSpanStore(instr Instruction, mem Memory, base *term, state *symbolicState) (handled bool, reason string, ok bool) {
	if len(x.recordSpans) == 0 || mem.Mode != MemOffset {
		return false, "", false
	}
	span, index, offset, isElement := x.recordElementOf(base, mem.Offset)
	if !isElement {
		return false, "", false
	}
	if len(instr.Operands) != 2 {
		return true, "a pair store to a record span", false
	}
	src, isReg := instr.Operands[0].(Register)
	if !isReg || src.Class == ClassV {
		return true, "a vector-register store to a record span", false
	}
	arg := x.recordSpans[span]
	size := memorySize(instr.Mnemonic, src.Class)
	value, okValue := state.read(src)
	if !okValue {
		return true, "unbound register read", false
	}
	if mem.Index != nil {
		prefix, length, stride, isArray := arg.arrayFieldAt(offset)
		if !isArray {
			return true, fmt.Sprintf("an indexed store through %s at offset %d, which starts no array field", span, offset), false
		}
		if int64(1)<<uint(mem.Shift) != stride || size != stride {
			return true, fmt.Sprintf("an indexed store through %s%s whose scale is not the element size", span, prefix), false
		}
		j, okJ := state.read(*mem.Index)
		if !okJ {
			return true, "unbound register read", false
		}
		leaf, _ := arg.leafAt(offset, stride)
		linear := binaryTerm("add", binaryTerm("mul", truncate(index, 32), constTerm(uint64(length), 32)), truncate(j, 32))
		state.writes = appendWrite(state.writes, span+prefix, linear, truncate(value, leaf.width), nil)
		return true, "", true
	}
	leaf, isLeaf := arg.leafAt(offset, size)
	if !isLeaf {
		return true, fmt.Sprintf("a %d-byte store at offset %d of a %s element, which is no field", size, offset, span), false
	}
	memory, _, at := arg.leafMemory(span, index, leaf)
	state.writes = appendWrite(state.writes, memory, at, truncate(value, leaf.width), nil)
	return true, "", true
}

// recordSpanLoad executes a load through a record span element's address:
// a scalar leaf at the offset, or — with a register index — an element of
// an array field, the select over `v.f` at the linear index i*N + j.
// Reports whether the load was through a record span.
func (x *pathExecutor) recordSpanLoad(instr Instruction, dest Register, mem Memory, base *term, state *symbolicState) (handled bool, reason string, ok bool) {
	if len(x.recordSpans) == 0 || mem.Mode != MemOffset {
		return false, "", false
	}
	span, index, offset, isElement := x.recordElementOf(base, mem.Offset)
	if !isElement {
		return false, "", false
	}
	arg := x.recordSpans[span]
	size := memorySize(instr.Mnemonic, dest.Class)
	var value *term
	var leafWidth int
	var signed bool
	if mem.Index != nil {
		prefix, length, stride, isArray := arg.arrayFieldAt(offset)
		if !isArray {
			return true, fmt.Sprintf("an indexed load through %s at offset %d, which starts no array field", span, offset), false
		}
		if int64(1)<<uint(mem.Shift) != stride || size != stride {
			return true, fmt.Sprintf("an indexed load through %s.%s whose scale is not the element size", span, prefix), false
		}
		j, okJ := state.read(*mem.Index)
		if !okJ {
			return true, "unbound register read", false
		}
		leaf, _ := arg.leafAt(offset, stride)
		leafWidth, signed = leaf.width, leaf.signed
		linear := binaryTerm("add", binaryTerm("mul", truncate(index, 32), constTerm(uint64(length), 32)), truncate(j, 32))
		value = memoryAt(state.writes[span+prefix], linear, recordFieldTerm(span, linear, prefix, leafWidth, x.concrete))
	} else {
		leaf, isLeaf := arg.leafAt(offset, size)
		if !isLeaf {
			return true, fmt.Sprintf("a %d-byte load at offset %d of a %s element, which is no field", size, offset, span), false
		}
		leafWidth, signed = leaf.width, leaf.signed
		memory, leafName, at := arg.leafMemory(span, index, leaf)
		value = memoryAt(state.writes[memory], at, recordFieldTerm(span, at, leafName, leafWidth, x.concrete))
	}
	_ = signed
	if isSignExtendingLoad(instr.Mnemonic) && leafWidth == int(size)*8 {
		state.write(dest, extendTerm(value, leafWidth, widthOf(dest.Class), true))
	} else {
		state.write(dest, zeroExtend(value, widthOf(dest.Class)))
	}
	return true, "", true
}

// term is a fixed-width bitvector expression. Width is 32 or 64.
type term struct {
	kind  termKind
	width int
	// declared is a parameter's declared width when the term reads it at
	// another (a zero-extension or truncation copies the parameter at the
	// use width): an element parameter's fixed-memory value is its
	// declared width's, whatever width it is read at. Zero: the width.
	declared int
	// id is the term's index in the termEvaluator that last numbered it,
	// one-based; zero before any numbering. Only the witness pass sets it,
	// before the variable orders' goroutines start reading the terms.
	id    int32
	name  string // termParam
	value uint64 // termConst (already masked to width)
	op    string // termBinary: add sub and or xor shl shr; termCmp: condition code
	left  *term
	right *term
	cond  *term // termIte
	// The known-bits memo (knownBits, asm/floats_ops.go): set once computed.
	kbDone  bool
	kbValue uint64
	kbKnown uint64
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
	if flags.float {
		if t, ok := floatCondition(code, flags.left, flags.right, flags.width); ok {
			return t
		}
		return paramTerm("fcmp#"+code, 1) // a code without an IEEE reading: an unknown
	}
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
	if right.kind == termConst && right.value == 0 && (code == "eq" || code == "ne") {
		if distributed, isReduction := zeroTestOfReduction(code, left, left.width); isReduction {
			return distributed
		}
	}
	return t
}

// isLowMask reports whether m is 2^k - 1 for some k.
func isLowMask(m uint64) bool { return m&(m+1) == 0 }

// significantBits bounds the position of a term's highest set bit: its
// width, or less for a masked, compared, or selected value. Terms are
// DAGs (a value read through a chain of summarized stores shares its
// subterms many times over), so the walk is memoized per call.
func significantBits(t *term) int {
	return significantBitsMemo(t, map[*term]int{})
}

func significantBitsMemo(t *term, memo map[*term]int) int {
	if n, seen := memo[t]; seen {
		return n
	}
	n := t.width
	switch t.kind {
	case termConst:
		n = bits.Len64(t.value)
	case termParam:
		n = min(t.width, t.declaredWidth()) // a parameter widened past its declared width is zero-extended
	case termCmp:
		n = 1
	case termIte:
		n = min(t.width, max(significantBitsMemo(t.left, memo), significantBitsMemo(t.right, memo)))
	case termBinary:
		switch t.op {
		case "and":
			n = t.width
			if t.right.kind == termConst {
				n = min(n, bits.Len64(t.right.value))
			}
			n = min(n, significantBitsMemo(t.left, memo))
		case "or", "xor":
			n = min(t.width, max(significantBitsMemo(t.left, memo), significantBitsMemo(t.right, memo)))
		}
	}
	memo[t] = n
	return n
}

// zeroTestOfReduction distributes a zero test over a max or min chain — the
// `umaxv`/`uminv` reductions (asm/verify_vector.go laneReduce), each step
// `ite(l hi r, l, r)` or `ite(l lo r, l, r)` — into per-lane tests, at the
// given width: max(l, r) ≠ 0 ⇔ l ≠ 0 ∨ r ≠ 0, max(l, r) = 0 ⇔ l = 0 ∧ r = 0,
// and dually for min (Oak.NeonSemantics.umaxv_ne_zero_iff,
// umaxv_cmeq_zero_iff). The chain's diagram over sixteen free lanes
// exceeds the node budget; the lane tests are linear. Zero-extensions of
// the chain are looked through; a truncation is not (it drops bits).
func zeroTestOfReduction(code string, t *term, width int) (*term, bool) {
	// Masks that keep every significant bit — a zero-extension, or the
	// lane's extraction from the register it was placed in — do not change
	// the value; they are looked through.
	for t.kind == termBinary && t.op == "and" && t.right.kind == termConst && isLowMask(t.right.value) && significantBits(t.left) <= min(bits.Len64(t.right.value), t.width) {
		t = t.left
	}
	if t.kind != termIte || t.cond.kind != termCmp || (t.cond.op != "hi" && t.cond.op != "lo") || t.cond.left != t.left || t.cond.right != t.right {
		return nil, false
	}
	isMax := t.cond.op == "hi"
	side := func(x *term) *term {
		if distributed, isReduction := zeroTestOfReduction(code, x, width); isReduction {
			return distributed
		}
		return zeroExtend(cmpTerm(code, x, constTerm(0, x.width)), width)
	}
	op := "and"
	if isMax == (code == "ne") {
		op = "or"
	}
	return binaryTerm(op, side(t.left), side(t.right)), true
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
	return &term{kind: termParam, width: width, name: name, declared: width}
}

// declaredWidth is a parameter term's declared width: the width it was
// created at, carried through re-widthed copies.
func (t *term) declaredWidth() int {
	if t.declared > 0 {
		return t.declared
	}
	return t.width
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
	// A mask of every bit at the width is the identity: `x & 0xFFFFFFFF`
	// at 32 bits is x. Without the fold two reads of one address, one of
	// them masked, are different terms, and a coupling offset that is zero
	// (`hr - hx`) looks like a memory difference the diagrams must decide.
	if op == "and" && right.kind == termConst && right.value&mask(left.width) == mask(left.width) && left.width == t.width {
		return left
	}
	if op == "and" && left.kind == termConst && left.value&mask(right.width) == mask(right.width) && right.width == t.width {
		return right
	}
	// x - x and x ^ x are zero; x & x and x | x are x. The two sides are
	// often distinct nodes for one value — two reads of one address, each
	// built afresh — so the comparison is structural, to a small depth.
	if (op == "sub" || op == "xor" || op == "and" || op == "or") && left.width == right.width && left.width == t.width {
		budget := sameTermBudget
		if sameTerm(left, right, &budget) {
			if op == "sub" || op == "xor" {
				return constTerm(0, t.width)
			}
			return left
		}
	}
	return t
}

// sameTermBudget bounds the nodes a structural comparison of two terms
// visits (sameTerm): enough for a read's index arithmetic, not a DAG.
const sameTermBudget = 48

// sameTerm reports two terms structurally equal, visiting at most *budget
// nodes; false when the budget runs out.
func sameTerm(a, b *term, budget *int) bool {
	if a == b {
		return true
	}
	if a == nil || b == nil || *budget <= 0 {
		return false
	}
	*budget--
	if a.kind != b.kind || a.width != b.width || a.op != b.op || a.name != b.name || a.value != b.value {
		return false
	}
	switch a.kind {
	case termConst, termParam:
		return true
	}
	return sameTerm(a.cond, b.cond, budget) && sameTerm(a.left, b.left, budget) && sameTerm(a.right, b.right, budget)
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
	return mapMemo{}.eval(t, env)
}

// A termMemo remembers the values of shared subterms during one evaluation:
// a map for a single evaluation, the id-indexed termEvaluator for a witness
// pass over many inputs.
type termMemo interface {
	eval(t *term, env map[string]uint64) uint64
}

type mapMemo map[*term]uint64

func (memo mapMemo) eval(t *term, env map[string]uint64) uint64 {
	if cached, seen := memo[t]; seen {
		return cached
	}
	value := t.evalUncached(env, memo)
	memo[t] = value
	return value
}

func (t *term) evalUncached(env map[string]uint64, memo termMemo) uint64 {
	m := mask(t.width)
	switch t.kind {
	case termParam:
		if value, bound := env[t.name]; bound {
			return value & m
		}
		// An element parameter outside the witness environment reads the
		// fixed memory, consistently with symbolic selects.
		if span, k, isElement := elementParam(t.name); isElement {
			return elementValue(span, k, t.declaredWidth()) & m
		}
		return 0
	case termConst:
		return t.value & m
	case termSelect:
		// The element the diagrams' counterexample chose, when it named
		// one (counterexampleOf); else the fixed memory.
		k := memo.eval(t.left, env) & mask(32)
		if value, chosen := env[spanElemName(t.name, int64(k))]; chosen {
			return value & m
		}
		return elementValue(t.name, k, t.width) & m
	case termQuant:
		// The body under every value of the bound parameter, in a memo of
		// its own per value (its subterms depend on the binding); the
		// enumeration stops at the deciding value, as the interpreter's.
		saved, wasBound := env[t.name]
		universal := t.op == "forall"
		holds := universal
		for v := uint64(0); v < uint64(1)<<uint(t.value); v++ {
			env[t.name] = v
			if (mapMemo{}.eval(t.left, env)&1 == 1) != universal {
				holds = !universal
				break
			}
		}
		if wasBound {
			env[t.name] = saved
		} else {
			delete(env, t.name)
		}
		if holds {
			return 1
		}
		return 0
	case termFloat:
		args := make([]uint64, 0, 3)
		widths := make([]int, 0, 3)
		for _, arg := range []*term{t.left, t.right, t.cond} {
			if arg != nil {
				args = append(args, memo.eval(arg, env)&mask(arg.width))
				widths = append(widths, arg.width)
			}
		}
		return floatEval(t.op, t.width, args, widths) & m
	case termCmp:
		// The comparison happens at the operands' width; t.width is only
		// the width the 1/0 result is used at.
		if conditionHolds(t.op, memo.eval(t.left, env), memo.eval(t.right, env), t.left.width) {
			return 1
		}
		return 0
	case termIte:
		if memo.eval(t.cond, env) != 0 {
			return memo.eval(t.left, env) & m
		}
		return memo.eval(t.right, env) & m
	}
	// Operands evaluate at their own widths (a mask node's inner term keeps
	// its width and modulus); the operation wraps to this term's width.
	l := memo.eval(t.left, env) & m
	r := memo.eval(t.right, env) & m
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
// equalTerms reports two terms structurally identical: the same kind,
// width, name, value, operator, and children — a cheap proof of equality
// before any diagram is built. Memoized over pairs of nodes, since the
// terms are DAGs.
func equalTerms(a, b *term) bool {
	return equalTermsMemo(a, b, map[[2]*term]bool{})
}

func equalTermsMemo(a, b *term, memo map[[2]*term]bool) bool {
	if a == b {
		return true
	}
	if a == nil || b == nil {
		return false
	}
	key := [2]*term{a, b}
	if known, seen := memo[key]; seen {
		return known
	}
	memo[key] = false // a cycle (there are none) would read as unequal
	equal := a.kind == b.kind && a.width == b.width && a.name == b.name && a.value == b.value && a.op == b.op &&
		equalTermsMemo(a.left, b.left, memo) && equalTermsMemo(a.right, b.right, memo) && equalTermsMemo(a.cond, b.cond, memo)
	memo[key] = equal
	return equal
}

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
	case termQuant:
		return fmt.Sprintf("(%s %s:%d. %s)", t.op, t.name, t.value, t.left.stringBounded(budget))
	case termFloat:
		parts := []string{}
		for _, arg := range []*term{t.left, t.right, t.cond} {
			if arg != nil {
				parts = append(parts, arg.stringBounded(budget))
			}
		}
		return fmt.Sprintf("%s%d(%s)", t.op, t.width, strings.Join(parts, ", "))
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
	case termCmp, termIte, termSelect, termFloat, termQuant:
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
	// vregs is the vector file: register number -> 128-bit value as lanes
	// (asm/verify_vector.go); nil until a vector instruction runs.
	vregs map[int]vecValue
	// unknownFrom, when set, is the lowest frame address a store at a
	// data-dependent index reached: slots from there up hold opaque values.
	unknownFrom *int64
	// bounds: register number -> exclusive bound K established on this
	// path by `cmp wI, #K; b.hs <trap>` (the checker's frame-array index
	// guard), cleared when the register is written. A frame store at the
	// register's index then names K possible slots (registerFrameAccess).
	bounds map[int]uint64
	// fregs is the RV64 lane's floating-point file (f0–f31, a class of its
	// own): register number -> the IEEE bit pattern at its width
	// (asm/rv64_verify_float.go); nil until a float instruction runs.
	fregs map[int]*term
	// rvcfg is the RV64 lane's fixed vector configuration (K lanes of S
	// bits, asm/rv64_verify_vector.go); nil until a vsetivli sets one.
	rvcfg *rvVectorConfigVerify
	// globals: the package-global cells this path has written, by Oak
	// name, at the cell's width (docs/spec/94-assembler.md §9); a cell not
	// here still holds its entry value, the parameter `global:NAME`.
	globals map[string]*term
	// writes: the stores this path made through span parameters, by
	// parameter, oldest first (asm/effects.go); a read consults them
	// before the entry memory, and the final logs are compared with the
	// Oak body's.
	writes map[string][]*spanWrite
	// notes is the execution's shared record (pathNotes); nil in a state
	// that reports nothing (a callee's summary, a witness run).
	notes *pathNotes
	// path is the chain of branches this path took at every undecided
	// fork, nil before the first (pathNode). A loop or a call with loops
	// reached again on another path merges its event's fields under the
	// path's condition (loopSite, mergeLoopEvents).
	path *pathNode
	// termBounds: the RV64 lane's index guards by the index's term —
	// `li rK, K; bgeu rI, rK, trap` bounds the value rI held below K —
	// which survives the scaling and the add that rewrite the register
	// (`slli rI, rI, s; add rI, rB, rI`, asm/rv64_frame_index.go).
	termBounds map[*term]uint64
}

type frameSlot struct {
	value *term
	width int // bytes
	// vec, on the low half of a whole q-register store, is the vector
	// value stored, and hi the term written to the high half: a whole
	// reload gives the value back lane for lane while both halves stand
	// (vectorFrameAccessAt), so a vector kept in a caller-saved home and
	// saved around a call keeps its lane structure for the proof.
	vec *vecValue
	hi  *term
}

// pathNotes is what every path of one execution reports back to the
// verdict, shared by the states of a fork (clone copies the pointer):
// shiftGuardMax is the largest trap bound under which a register-count
// shift ran — math.MaxUint64 for a count no guard bounded — so the Oak
// lowering admits a variable shift count only when the machine trapped
// at or below Oak's width on every such shift (docs/spec/94-assembler.md
// §8, variable shift counts; lowerVariableShift).
type pathNotes struct {
	shiftGuardMax uint64
}

// noteVariableShift records a shift whose count came from register num,
// guarded on this path by the trap bound bounds[num] if any.
func (s *symbolicState) noteVariableShift(num int) {
	if s.notes == nil {
		return
	}
	bound, guarded := s.bounds[num]
	if !guarded {
		bound = math.MaxUint64
	}
	if bound > s.notes.shiftGuardMax {
		s.notes.shiftGuardMax = bound
	}
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
	// float: fcmp left, right — the codes read as IEEE predicates
	// (asm/verify_float.go floatCondition).
	float bool
	// ccmp: the comparison's flags when cond holds, else the immediate NZCV.
	cond     *term
	elseNZCV int64
	// A `cmp wI, #K`: the register and the immediate, for the index bound a
	// `b.hs <trap>` on these flags establishes on the fall-through path
	// (symbolicState.bounds); indexReg is -1 otherwise.
	indexReg int
	bound    uint64
}

func (s *symbolicState) read(reg Register) (*term, bool) {
	if reg.ZeroRegister() {
		return constTerm(0, widthOf(reg.Class)), true
	}
	if reg.Class == ClassRV64F {
		value, bound := s.fregs[reg.Num]
		if !bound && rv64FloatCalleeSaved(reg.Num) {
			// A callee-saved float register (fs0–fs11) carries the caller's
			// pattern on entry: an opaque symbol the save/restore pair
			// round-trips (LP64D, docs/spec/94-assembler.md §9).
			value = paramTerm(fmt.Sprintf("entry.f%d", reg.Num), 64)
			if s.fregs == nil {
				s.fregs = map[int]*term{}
			}
			s.fregs[reg.Num] = value
			bound = true
		}
		return value, bound
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
		// A w view reads back the 32-bit term a w write zero-extended (not
		// a mask over the extension): the machine then spells an element
		// index exactly as the Oak side does, and the two sides' reads of
		// one element share a single abstraction in the decision.
		if value.kind == termBinary && value.op == "and" && value.right.kind == termConst && value.right.value == mask(32) && value.left.width == 32 {
			return value.left, true
		}
		return truncate(value, 32), true
	}
	return value, true
}

func (s *symbolicState) write(reg Register, value *term) {
	if reg.ZeroRegister() {
		return
	}
	if reg.Class == ClassRV64F {
		if s.fregs == nil {
			s.fregs = map[int]*term{}
		}
		s.fregs[reg.Num] = value
		return
	}
	if reg.Class == ClassW {
		value = zeroExtend(value, 64) // AArch64: a 32-bit write zeroes the upper half
	}
	s.regs[reg.Num] = value
	delete(s.bounds, reg.Num)
}

// The proof's names for a global (docs/spec/94-assembler.md §9): its
// value on entry (`global:NAME`, a parameter at the scalar's width), its
// address, and its page address (64-bit parameters the loads recognize).
const globalParamPrefix = "global:"

func globalParam(name string) string    { return globalParamPrefix + name }
func globalAddrName(name string) string { return "&" + globalParamPrefix + name }
func globalPageName(name string) string { return "&" + globalParamPrefix + name + "#page" }

// globalAddrOf recognizes a global's address term.
func globalAddrOf(t *term) (string, bool) {
	if t == nil || t.kind != termParam || !strings.HasPrefix(t.name, "&"+globalParamPrefix) || strings.HasSuffix(t.name, "#page") {
		return "", false
	}
	return t.name[len("&"+globalParamPrefix):], true
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
		return &term{kind: termParam, width: width, name: t.name, declared: t.declaredWidth()}
	case termCmp:
		return &term{kind: termCmp, width: width, op: t.op, left: t.left, right: t.right}
	case termBinary:
		// Truncating a zero-extension back to its width is the extended term.
		if t.op == "and" && t.right.kind == termConst && t.right.value == mask(width) && t.left.width == width {
			return t.left
		}
		// A mask that keeps every bit under the width is invisible under
		// it: `(x and 0xFFFFFFFF) at 32 bits` is x at 32 bits (the
		// machine's `mov w, w` of a result then read at its width). Not
		// over a parameter: a parameter at a width is the parameter, and
		// its extension back (the case above, the Oak lowering's
		// convention with its own masks) would forget the mask.
		if t.op == "and" && t.right.kind == termConst && t.right.value&mask(width) == mask(width) && t.left.width > width && t.left.kind != termParam {
			return truncate(t.left, width)
		}
		// Bits placed above the width vanish under it: a call's result with
		// its unspecified upper bits (`(r and mask) or (hi shl 32)`) read
		// at its width is the result — the same term the Oak side builds,
		// where the wrapper kept a select at a symbolic index from being
		// one term on both sides.
		if t.op == "or" {
			if shiftedAbove(t.right, width) {
				return truncate(t.left, width)
			}
			if shiftedAbove(t.left, width) {
				return truncate(t.right, width)
			}
		}
	}
	return &term{kind: termBinary, width: width, op: "and", left: t, right: constTerm(mask(width), width)}
}

// shiftedAbove reports a term whose every set bit lies at or above the
// width: a left shift, at a width the count stays below (a count at the
// term's width wraps to zero in this algebra, as the machine's does), by
// a constant of at least the width truncated to.
func shiftedAbove(t *term, width int) bool {
	return t.kind == termBinary && t.op == "shl" && t.right.kind == termConst && t.right.value < uint64(t.width) && t.right.value >= uint64(width)
}

func zeroExtend(t *term, width int) *term {
	if t.width == width {
		return t
	}
	switch t.kind {
	case termConst:
		return constTerm(t.value&mask(t.width), width)
	case termParam:
		return &term{kind: termParam, width: width, name: t.name, declared: t.declaredWidth()}
	case termCmp:
		return &term{kind: termCmp, width: width, op: t.op, left: t.left, right: t.right}
	case termBinary:
		// Extending a truncation of a wider term is the wider term masked.
		if t.op == "and" && t.right.kind == termConst && t.right.value == mask(t.width) && t.left.width == width {
			return &term{kind: termBinary, width: width, op: "and", left: t.left, right: constTerm(mask(t.width), width)}
		}
	}
	// The narrow computation's wrap is preserved by masking to its width.
	return &term{kind: termBinary, width: width, op: "and", left: t, right: constTerm(mask(t.width), width)}
}

var verifiableOps = map[string]string{"add": "add", "sub": "sub", "adds": "add", "subs": "sub", "and": "and", "orr": "or", "eor": "xor", "lsl": "shl", "lsr": "shr", "asr": "sar", "mul": "mul"}

// executeBody symbolically executes the body along every path; reports (result
// term, "", true) or ("", reason, false) when the body is outside the
// verified subset.
func executeBody(fn *Function, sig *ast.FunctionStatement, concrete map[string]uint64) (*term, *pathExecutor, string, bool) {
	return executeBodyChunk(fn, sig, concrete, 0, 0)
}

// executeBodyHalf is executeBody delivering, for a vector result, the
// given 64-bit half of v0 (asm/verify_vector.go verifyVectorResult).
func executeBodyHalf(fn *Function, sig *ast.FunctionStatement, concrete map[string]uint64, half int) (*term, *pathExecutor, string, bool) {
	return executeBodyChunk(fn, sig, concrete, half, 0)
}

// executeBodyChunk is executeBody delivering, for a record result of two
// register chunks (9 to 16 bytes: x0 and x1, a0 and a1), the given chunk.
func executeBodyChunk(fn *Function, sig *ast.FunctionStatement, concrete map[string]uint64, half, chunk int) (*term, *pathExecutor, string, bool) {
	// Every path to its end first: the result is then a select tree on the
	// branch conditions, which the decision splits well. Past the path
	// budget the body runs again merging its paths at their joins
	// (joinPoints), linear in the forks rather than exponential.
	result, exec, reason, ok := executeBodyChunkJoining(fn, sig, concrete, half, chunk, false)
	if !ok && strings.HasPrefix(reason, "more paths than the verifier's budget") {
		return executeBodyChunkJoining(fn, sig, concrete, half, chunk, true)
	}
	if ok && exec != nil && !exec.loopsInLayoutOrder() {
		if os.Getenv("OAK_VERIFY_TRACE") != "" {
			fmt.Fprintf(os.Stderr, "verify %s: loop events out of layout order; running again merging at the joins\n", fn.Name)
		}
		// A fork's first side ran past the meeting point and summarized
		// the loops there before the other side's (`groups == 1 ? {loop}
		// | {loop}` then a loop): the events are numbered out of the Oak
		// body's order. Merging at the joins numbers them as the Oak side
		// does; when that run fails, the first stands.
		if joined, joinedExec, joinedReason, joinedOK := executeBodyChunkJoining(fn, sig, concrete, half, chunk, true); joinedOK {
			return joined, joinedExec, joinedReason, joinedOK
		}
	}
	return result, exec, reason, ok
}

func executeBodyChunkJoining(fn *Function, sig *ast.FunctionStatement, concrete map[string]uint64, half, chunk int, joins bool) (*term, *pathExecutor, string, bool) {
	state := &symbolicState{arch: fn.Arch, regs: map[int]*term{}, notes: &pathNotes{}}
	params := map[string]RegClass{}
	var resultArea []compositeLeaf // a record result returned through memory: its leaves
	spans := map[string]int64{}    // span/view parameter -> element size in bytes
	declared := map[string]int{}
	composites := map[string]compositeArg{}
	recordSpans := map[string]recordSpanArg{}
	boolParams := map[string]bool{}
	vectors := map[string]typechecker.SimdShape{} // vector parameter -> shape
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
		if reason, ok := bindRV64Params(fn, sig, state, input, spans, declared, composites); !ok {
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
		if arg, reason, isRecordSpan, ok := recordSpanOf(fn.Composites, param.Type); isRecordSpan {
			// A span of records: its element size is the record's, and a
			// field read through an element address is a leaf's select term.
			if !ok {
				return nil, nil, reason, false
			}
			spans[param.Name.Value] = arg.size
			recordSpans[param.Name.Value] = arg
			declared[spanLenName(param.Name.Value)] = 32
			declared[spanBaseName(param.Name.Value)] = 64
			continue
		}
		class, ok := contractClass(param.Type)
		if shape, isVector := vectorShape(param.Type); isVector && ok && class == ClassV {
			// A fixed vector: its lanes are the leaves `p[k]`, the register
			// the whole (asm/verify_vector.go).
			vectors[param.Name.Value] = shape
			for k := 0; k < shape.Lanes; k++ {
				declared[spanElemName(param.Name.Value, int64(k))] = laneWidth(shape)
			}
			continue
		}
		if !ok {
			return nil, nil, "vector or non-integer parameters", false
		}
		if class == ClassV {
			// A float: its IEEE bit pattern in the low lane of its vector
			// register (asm/verify_float.go).
			bits, _, isFloat := contractBits(param.Type)
			if !isFloat {
				return nil, nil, "vector or non-integer parameters", false
			}
			params[param.Name.Value] = class
			declared[param.Name.Value] = bits
			continue
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
		if binding.OnStack {
			// A parameter in the caller's outgoing area: the frame slot at
			// Stack bytes above the entry sp holds it, at the size the
			// caller stored it (classifyArguments: a narrow scalar its own
			// bytes, a Bool the four of the C int, a 64-bit scalar eight),
			// a span's base at Stack and its 32-bit length at Stack+8, a
			// by-value record its chunks, a by-reference one its address
			// (docs/spec/94-assembler.md §8, thirty-second increment;
			// Oak.StackArguments). The body's loads then read the
			// parameters as they read any frame slot.
			if state.frame == nil {
				state.frame = map[int64]frameSlot{}
			}
			switch {
			case composites[binding.Param].leaves != nil:
				cp := composites[binding.Param]
				if cp.size > 16 {
					state.storeSlot(binding.Stack, paramTerm(spanBaseName(binding.Param), 64), 8)
					continue
				}
				state.storeSlot(binding.Stack, chunkTerm(cp.leaves, 0, input), 8)
				if cp.size > 8 {
					state.storeSlot(binding.Stack+8, chunkTerm(cp.leaves, 1, input), 8)
				}
			case spans[binding.Param] != 0:
				state.storeSlot(binding.Stack, paramTerm(spanBaseName(binding.Param), 64), 8)
				state.storeSlot(binding.Stack+8, input(spanLenName(binding.Param), 32), 4)
			case vectors[binding.Param].Lanes != 0:
				// A vector past v0–v7: its sixteen bytes in the outgoing
				// area, the lanes packed as the register would hold them,
				// two eight-byte slots the body's `ldr q` reads whole.
				halves := vectorParamValue(binding.Param, vectors[binding.Param], input).halves()
				state.storeSlot(binding.Stack, halves[0], 8)
				state.storeSlot(binding.Stack+8, halves[1], 8)
			case params[binding.Param] == ClassV:
				// A float past v0–v7: its bit pattern at its own size.
				bits := declared[binding.Param]
				state.storeSlot(binding.Stack, input(binding.Param, bits), int64(bits)/8)
			case params[binding.Param] == ClassX:
				state.storeSlot(binding.Stack, input(binding.Param, 64), 8)
			case boolParams[binding.Param]:
				state.storeSlot(binding.Stack, zeroExtend(input(binding.Param, 1), 32), 4)
			default:
				bits := declared[binding.Param]
				if bits < 32 {
					state.storeSlot(binding.Stack, input(binding.Param, bits), int64(bits+7)/8)
				} else {
					state.storeSlot(binding.Stack, input(binding.Param, 32), 4)
				}
			}
			continue
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
		if shape, isVector := vectors[binding.Param]; isVector {
			if binding.Register.Class != ClassV {
				return nil, nil, "a vector parameter bound outside the vector file", false
			}
			state.writeVec(binding.Register.Num, vectorParamValue(binding.Param, shape, input))
			continue
		}
		class := params[binding.Param]
		bits := declared[binding.Param]
		switch {
		case class == ClassV:
			if binding.Register.Class != ClassV {
				return nil, nil, "a float parameter bound outside the vector file", false
			}
			state.writeVec(binding.Register.Num, vecFromLow(zeroExtend(input(binding.Param, bits), 64)))
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
	// The program's constant tables read as spans named by their Oak
	// identifiers: `adrl`/`la` binds a register to the base `&T`, and a
	// load through it is the element term T[k] — the same term the Oak
	// side gives T[k] (docs/spec/94-assembler.md §9, constant tables).
	for symbol, table := range fn.Tables {
		if table.Elem > 0 {
			spans[TableName(symbol)] = table.Elem
		}
	}
	resultClass, hasResult := contractClass(sig.ReturnType)
	if comp, isComposite := fn.Composites[typeText(sig.ReturnType)]; isComposite && len(comp.Fields) > 0 {
		// A record result of one chunk comes back in x0, of two in x0 and
		// x1 (a0 and a1), each chunk verified in its own run (Verify);
		// larger ones come back through the area x8 addresses, outside the
		// subset.
		if chunk >= int((comp.Size+7)/8) {
			return nil, nil, "a result chunk past the record", false
		}
		resultClass, hasResult = ClassX, true
		if comp.Size > 16 {
			// Returned through memory: the caller passes the result area
			// in x8 (a0 on RV64 is outside the subset). The area is modeled
			// as frame memory at an address of its own, far above the
			// frame and the incoming arguments, so the body's stores through
			// x8 tile it as they tile the frame (registerFrameAccess) and
			// the ret delivers the chunk assembled from its slots, leaf by
			// leaf (docs/spec/94-assembler.md §9).
			if fn.Arch == ArchRV64 {
				return nil, nil, "a record result beyond two register chunks (returned through memory) on RV64", false
			}
			leaves, _, ok := compositeLeaves(fn.Composites, typeText(sig.ReturnType), "", 0, nil)
			if !ok {
				return nil, nil, "a record result whose layout has no leaves", false
			}
			state.regs[8] = frameAddressTerm(resultAreaBase)
			resultArea = leaves
		}
	}
	_, vectorResult := vectorShape(sig.ReturnType)
	floatResult := 0
	if hasResult && resultClass == ClassV && !vectorResult {
		bits, _, isFloat := contractBits(sig.ReturnType)
		if !isFloat {
			return nil, nil, "no integer result", false
		}
		floatResult = bits // an f32/f64 result: the low lane of v0 at its width
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
	exec := &pathExecutor{items: fn.Items, labels: labels, resultClass: resultClass, spans: spans, declared: declared, concrete: concrete != nil, env: concrete, records: composites, arch: fn.Arch, globals: fn.Globals, fn: fn, notes: state.notes, recordSpans: recordSpans}
	exec.resultReg = Register{Class: resultClass, Num: chunk}
	exec.resultHalf = half
	exec.floatResult = floatResult
	exec.resultChunk = chunk
	exec.resultArea = resultArea
	if fn.Arch == ArchRV64 {
		exec.resultReg = Register{Class: rv64ResultRegister.Class, Num: rv64ResultRegister.Num + chunk}
		if floatResult != 0 {
			exec.resultReg = rv64FloatResultRegister
		}
	}
	exec.hasResult = hasResult
	exec.loopExits = findLoopsIn(fn.Name, fn.Items, labels, fn.Callees)
	if joins {
		exec.joins = joinPoints(fn.Items, labels)
	}
	result, effects, reason, ok := exec.runAll(state)
	if effects != nil {
		exec.cells, exec.writes, exec.trap = effects.cells, effects.writes, effects.trap
	}
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
	// floatResult is the width of an f32/f64 result (the low lane of v0),
	// zero for the other result kinds.
	floatResult int
	resultHalf  int               // a vector result: the 64-bit half of v0 delivered (asm/verify_vector.go)
	resultChunk int               // a record result of two chunks: the chunk delivered (0: x0/a0, 1: x1/a1)
	resultArea  []compositeLeaf   // a record result returned through memory (x8): its leaves; nil otherwise
	spans       map[string]int64  // span parameter -> element size in bytes
	declared    map[string]int    // parameter -> declared width
	globals     map[string]Global // the globals the body addresses (fn.Globals)
	// recordSpans: span parameters whose elements are records, by name —
	// the element size and the record's scalar leaves (relative to the
	// element), so a field read through an element address is the leaf's
	// select term (docs/spec/94-assembler.md §9).
	recordSpans map[string]recordSpanArg
	// hasResult: the function delivers a scalar result; false for a unit
	// function that writes package state, whose paths return unitResult.
	// cells: the written cells after run, merged across every path.
	hasResult bool
	cells     map[string]*term
	writes    map[string][]*spanWrite // the span memories written after run (asm/effects.go)
	concrete  bool                    // a witness run: every input is a constant
	loopExits map[int]loopShape
	callAt    int          // the item index of the call being summarized (loopEvent.at)
	loops     []*loopEvent // data-dependent loops met, in creation order
	loopStack []int        // indices of the loops whose bodies are being executed
	// sites: the loop events by the site that created them — a loop head
	// (`loop@<pc>`) or a call whose callee has loops (`call@<line>`) — as
	// the range of indices the site's events occupy. A site reached again
	// on another path reuses them (asm/loops.go, loopSite).
	sites map[string]loopSite
	// joins: each forward conditional branch's immediate post-dominator
	// (joinPoints) — the item where its two paths meet again, at which
	// the executor merges their states into one continuation instead of
	// running each to the end (docs/spec/94-assembler.md §9, joins).
	joins map[int]int
	// stops is the stack of joins being collected: a path reaching the
	// innermost stop parks its state in joined and ends.
	stops  []int
	joined []*symbolicState
	// ends are the paths' outcomes — a result with its effects, or a trap
	// — each under the path's condition; runAll folds them.
	ends []pathEnd
	// loopsInsideMemo caches loopsInside per loop shape (by its body's start).
	loopsInsideMemo map[int]bool
	outgoingMemo    *int64      // outgoingArea, once computed
	bodyJoinsMemo   map[int]int // bodyJoins, once computed
	paths           int
	steps           int
	// records: record and union parameters by name (their leaves), env the
	// concrete inputs of a witness run (nil when symbolic).
	records map[string]compositeArg
	env     map[string]uint64
	// fn is the function under verification (its program tables:
	// Callees, Records, Constants); summarized names the callees taken at
	// their Oak bodies (summarizeCall), freshSyms the unknowns those
	// summaries introduced (the unspecified upper bits of a result), and
	// callSites counts them for naming.
	fn         *Function
	summarized []string
	freshSyms  map[string]int
	// trap is the condition under which the machine traps (pathEffects.trap
	// of the whole body): the equivalence is decided outside it.
	trap      *term
	callSites int
	// notes is the record every path shares (pathNotes): the shift
	// count guards, read by the verdict's lowering.
	notes *pathNotes
	// freshCount numbers the unspecified lane values of the RV64 vector
	// model (asm/rv64_verify_vector.go freshLane).
	freshCount int
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
				if field.Name == "" {
					// An owned array as a value (docs/spec/94-assembler.md
					// §9, forty-eighth increment): the composite is the
					// array itself, its leaves the elements `p[k]`, as the
					// Oak side names them (aggregateFrom).
					elemName = fmt.Sprintf("%s[%d]", prefix, k)
				}
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

// definedMask is the bit mask of the cells the leaves inside chunk k
// occupy — what a callee's result defines: a Bool's whole 4-byte cell (the
// C enum, written as a word holding 0 or 1), every other leaf its width.
// The rest of the chunk is padding the ABI leaves unspecified.
func definedMask(leaves []compositeLeaf, k int64) uint64 {
	var m uint64
	for _, leaf := range leaves {
		if leaf.offset < 8*k || leaf.offset >= 8*k+8 {
			continue
		}
		cell := leaf.width
		if cell == 1 {
			cell = 32
		}
		m |= mask(cell) << uint((leaf.offset-8*k)*8)
	}
	return m
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
	var vregs map[int]vecValue
	if s.vregs != nil {
		vregs = make(map[int]vecValue, len(s.vregs))
		for reg, value := range s.vregs {
			vregs[reg] = value
		}
	}
	var globals map[string]*term
	if len(s.globals) > 0 {
		globals = make(map[string]*term, len(s.globals))
		for name, value := range s.globals {
			globals[name] = value
		}
	}
	var fregs map[int]*term
	if s.fregs != nil {
		fregs = make(map[int]*term, len(s.fregs))
		for reg, value := range s.fregs {
			fregs[reg] = value
		}
	}
	var rvcfg *rvVectorConfigVerify
	if s.rvcfg != nil {
		cfg := *s.rvcfg
		rvcfg = &cfg
	}
	var bounds map[int]uint64
	if len(s.bounds) > 0 {
		bounds = make(map[int]uint64, len(s.bounds))
		for reg, bound := range s.bounds {
			bounds[reg] = bound
		}
	}
	var termBounds map[*term]uint64
	if len(s.termBounds) > 0 {
		termBounds = make(map[*term]uint64, len(s.termBounds))
		for t, bound := range s.termBounds {
			termBounds[t] = bound
		}
	}
	return &symbolicState{arch: s.arch, regs: regs, flags: s.flags, disp: s.disp, frame: frame, vregs: vregs, fregs: fregs, rvcfg: rvcfg, globals: globals, writes: cloneWrites(s.writes), unknownFrom: s.unknownFrom, bounds: bounds, notes: s.notes, termBounds: termBounds, path: s.path}
}

// pathNode is one fork on a path: the condition (1 bit) the path took
// there, which side of the fork it is, and the fork itself (one mark per
// fork, shared by its two sides), so two paths' relation is structural:
// they are exclusive when they left one fork on different sides.
type pathNode struct {
	parent *pathNode
	cond   *term
	fork   *forkMark // nil for a join node: the disjunction of the paths merged there
	side   bool
	term   *term // the conjunction down to here, built on demand
}

// forkMark identifies one fork: the branch's position and its condition
// (the taken side's, at the width the branch produced it). A field keeps
// every mark a distinct allocation (pointers to zero-size values may
// coincide).
type forkMark struct {
	pc   int
	cond *term
}

// assume narrows the path to one side of a fork: the inputs on which cond
// (its low bit) holds.
func (s *symbolicState) assume(cond *term, fork *forkMark, side bool) {
	s.path = &pathNode{parent: s.path, cond: truncate(cond, 1), fork: fork, side: side}
}

// pathCondition is the path's condition: the conjunction of the branches
// it took, nil before the first fork.
func (s *symbolicState) pathCondition() *term {
	return s.path.condition()
}

func (n *pathNode) condition() *term {
	if n == nil {
		return nil
	}
	if n.term == nil {
		if parent := n.parent.condition(); parent != nil {
			n.term = binaryTerm("and", parent, n.cond)
		} else {
			n.term = n.cond
		}
	}
	return n.term
}

// exclusive reports whether two paths cannot both be taken: they left
// one fork on different sides. Otherwise one is a prefix of the other —
// the same path, reaching a site again (an unrolled iteration's call).
func (n *pathNode) exclusive(other *pathNode) bool {
	sides := map[*forkMark]bool{}
	for at := other; at != nil; at = at.parent {
		if at.fork != nil {
			sides[at.fork] = at.side
		}
	}
	for at := n; at != nil; at = at.parent {
		if at.fork == nil {
			continue // a join: the paths it merged are told apart by their forks
		}
		if side, shared := sides[at.fork]; shared && side != at.side {
			return true
		}
	}
	return false
}

// conditionBelow is the conjunction of the branches taken below parent
// (nil when none): the path's condition relative to the fork that ends
// at a join.
func (n *pathNode) conditionBelow(parent *pathNode) *term {
	var cond *term
	for at := n; at != nil && at != parent; at = at.parent {
		if cond == nil {
			cond = at.cond
		} else {
			cond = binaryTerm("and", at.cond, cond)
		}
	}
	return cond
}

// noteTrapGuard records, on the path that falls through a `b.hs <trap>`
// reading `cmp wI, #K`, that wI < K: the index bound of a frame array.
func (s *symbolicState) noteTrapGuard(instr Instruction) {
	if instr.Mnemonic == "bgeu" && len(instr.Operands) == 3 {
		// The RV64 lane's guard: `li rK, K; bgeu rI, rK, trap` bounds rI
		// below K on the fall-through path (the shift count guard,
		// nativegen/rv64.go).
		index, okI := instr.Operands[0].(Register)
		limit, okK := instr.Operands[1].(Register)
		if !okI || !okK {
			return
		}
		bound, ok := s.read(limit)
		if !ok || bound.kind != termConst {
			return
		}
		if s.bounds == nil {
			s.bounds = map[int]uint64{}
		}
		s.bounds[index.Num] = bound.value
		if value, ok := s.read(index); ok {
			if s.termBounds == nil {
				s.termBounds = map[*term]uint64{}
			}
			s.termBounds[value] = bound.value
		}
		return
	}
	if instr.Mnemonic != "b." || (instr.Cond != "hs" && instr.Cond != "cs") || s.flags == nil || s.flags.unknown || s.flags.indexReg < 0 || s.flags.kind != "" {
		return
	}
	if s.bounds == nil {
		s.bounds = map[int]uint64{}
	}
	s.bounds[s.flags.indexReg] = s.flags.bound
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
	if regs[0].Class == ClassV {
		return x.vectorFrameAccessAt(instr, state, addr, regs)
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
		value, ok := x.loadFrame(state, addr+int64(i)*size, size)
		if !ok {
			value, ok = state.opaqueSlot(addr+int64(i)*size, size)
		}
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

// loadFrame reads size bytes at addr from the frame. A byte no store on
// the path reached is unspecified — the padding of a record chunk stored
// at a narrower width, the payload bytes of a union variant not
// constructed — and becomes a fresh unknown (`frame#<addr>`, zero in a
// witness run) that later loads of the same byte see again; the Oak side
// never reads such a byte, so the unknown can only fail a proof, never
// forge one. A byte that lies inside no frame slot at all (a read outside
// the declared frame) is still refused.
func (x *pathExecutor) loadFrame(state *symbolicState, addr, size int64) (*term, bool) {
	if value, ok := state.loadSlot(addr, size); ok {
		return value, true
	}
	if state.frame == nil {
		state.frame = map[int64]frameSlot{}
	}
	for b := addr; b < addr+size; b++ {
		covered := false
		for start, slot := range state.frame {
			if start <= b && b < start+int64(slot.width) {
				covered = true
				break
			}
		}
		if covered {
			continue
		}
		var fresh *term
		if x.concrete {
			fresh = constTerm(0, 8)
		} else {
			name := fmt.Sprintf("frame#%d", b)
			if x.freshSyms == nil {
				x.freshSyms = map[string]int{}
			}
			if _, known := x.freshSyms[name]; !known {
				x.freshSyms[name] = 8
				x.declared[name] = 8
			}
			fresh = paramTerm(name, 8)
		}
		state.storeSlot(b, fresh, 1)
	}
	return state.loadSlot(addr, size)
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
				// The piece is placed as packLanes places a lane — masked to
				// its width at the full width — so a word assembled from byte
				// slots is a recognizable pack of them (unpackLane).
				shifted := slot.value
				if cursor > start {
					shifted = binaryTerm("shr", slot.value, constTerm(uint64((cursor-start)*8), slot.value.width))
				}
				piece := truncate(shifted, int(take)*8)
				placed := widenLane(piece, int(take)*8, int(size)*8)
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

// resultAreaBase is the entry-relative address the executor gives the
// result area a caller passes in x8: far above any frame or incoming
// argument, so the area's slots never meet the function's own.
const resultAreaBase = int64(1) << 40

// resultAreaChunk assembles chunk resultChunk of a record result returned
// through memory from the slots the body stored in the x8 area: every
// leaf in the chunk read at its offset and width, placed at its bit
// position; a leaf the body never stored leaves the chunk undefined.
func (x *pathExecutor) resultAreaChunk(state *symbolicState) (*term, string, bool) {
	var missing string
	chunk := chunkTerm(x.resultArea, int64(x.resultChunk), func(name string, width int) *term {
		for _, leaf := range x.resultArea {
			if leaf.name != name {
				continue
			}
			size := (int64(leaf.width) + 7) / 8
			value, ok := state.loadSlot(resultAreaBase+leaf.offset, size)
			if !ok {
				missing = name
				return constTerm(0, width)
			}
			return truncate(value, width)
		}
		missing = name
		return constTerm(0, width)
	})
	if missing != "" {
		return nil, fmt.Sprintf("the result field %s was never stored to the result area", missing), false
	}
	return chunk, "", true
}

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
			// A store at a data-dependent index into a frame array (a loop
			// filling a tail buffer). Under the checker's index guard
			// (`cmp wI, #K; b.hs <trap>`, state.bounds) the store names K
			// possible slots and each takes the value under the condition
			// that the index selects it — the frame array as a memory, so
			// the slots stay loop-carried state. Without the bound, or over
			// slots the frame does not hold whole, every slot from the
			// array's base up is forgotten and reads there become opaque
			// symbols (an evidence verdict at most). A load at such an index
			// stays outside the subset.
			if !isStoreMnemonic(instr.Mnemonic) {
				// A load at a guarded index reads the elements merged
				// under the index (docs/spec/94-assembler.md §8, frame
				// loads at a data-dependent index; Oak.FrameIndex), as
				// the Oak side reads an array element under a symbolic
				// index (elementUnderIndex).
				if bound, isBounded := state.bounds[mem.Index.Num]; isBounded {
					return x.boundedFrameLoad(instr, state, addr, truncate(index, 32), bound, mem.Shift)
				}
				return "a frame load at a data-dependent index (the index is not guarded)", false
			}
			if bound, isBounded := state.bounds[mem.Index.Num]; isBounded && x.boundedFrameStore(instr, state, addr, truncate(index, 32), bound, mem.Shift) {
				return "", true
			}
			state.forgetFrameFrom(addr)
			return "", true
		}
		addr += int64(index.value&mask(32)) << uint(mem.Shift)
	}
	return x.frameAccessAt(instr, state, addr)
}

// boundedFrameStore performs a store at a symbolic element index below
// bound into the frame array at base: element e's bytes, inside one slot
// the frame holds, take ite(index = e, value, old) in place, the slot
// keeping its width. It reports false — nothing written — when an element
// lies in no single slot.
func (x *pathExecutor) boundedFrameStore(instr Instruction, state *symbolicState, base int64, index *term, bound uint64, shift int) bool {
	regs := registerOperands(instr.Operands[:len(instr.Operands)-1])
	if len(regs) != 1 || regs[0].Class == ClassV || isPairAccess(instr.Mnemonic) {
		return false
	}
	size := memorySize(instr.Mnemonic, regs[0].Class)
	if int64(1)<<uint(shift) != size || bound > 64 {
		return false
	}
	value, ok := state.read(regs[0])
	if !ok {
		return false
	}
	return state.boundedFrameStoreAt(base, index, bound, size, truncate(value, int(size)*8))
}

// boundedFrameStoreAt is boundedFrameStore's store proper: value, size
// bytes wide, into element index (below bound) of the frame array at
// base, each element taking ite(index = e, value, old) in its slot.
func (state *symbolicState) boundedFrameStoreAt(base int64, index *term, bound uint64, size int64, value *term) bool {
	type target struct {
		start int64
		slot  frameSlot
		at    int64
	}
	targets := make([]target, 0, bound)
	for e := uint64(0); e < bound; e++ {
		at := base + int64(e)*size
		found := false
		for start, slot := range state.frame {
			if start <= at && at+size <= start+int64(slot.width) {
				targets = append(targets, target{start: start, slot: slot, at: at})
				found = true
				break
			}
		}
		if !found {
			return false
		}
	}
	for e, t := range targets {
		cond := truncate(cmpTerm("eq", index, constTerm(uint64(e), 32)), 1)
		slot := state.frame[t.start] // the slot as updated by earlier elements
		width := slot.width * 8
		if int64(slot.width) == size {
			state.frame[t.start] = frameSlot{value: iteTerm(cond, value, slot.value), width: slot.width}
			continue
		}
		offset := uint64((t.at - t.start) * 8)
		old := truncate(binaryTerm("shr", slot.value, constTerm(offset, width)), int(size)*8)
		chosen := zeroExtend(iteTerm(cond, value, old), width)
		kept := binaryTerm("and", slot.value, constTerm(^(mask(int(size)*8)<<offset)&mask(width), width))
		state.frame[t.start] = frameSlot{value: binaryTerm("or", kept, binaryTerm("shl", chosen, constTerm(offset, width))), width: slot.width}
	}
	return true
}

// boundedFrameLoad performs a load at a symbolic element index below
// bound from the frame array at base: the elements the frame holds,
// merged under `index == e` from the last element down — the same fold
// as the Oak side's elementUnderIndex, so on an index at or past the
// bound (the path the guard's trap removes) both sides read the last
// element and no mismatch is invented there (Oak.FrameIndex.chain_select,
// chain_beyond). The value is then extended as the load extends it.
func (x *pathExecutor) boundedFrameLoad(instr Instruction, state *symbolicState, base int64, index *term, bound uint64, shift int) (string, bool) {
	regs := registerOperands(instr.Operands[:len(instr.Operands)-1])
	if len(regs) != 1 || regs[0].Class == ClassV || isPairAccess(instr.Mnemonic) {
		return "a frame load at a data-dependent index (" + instr.Mnemonic + ")", false
	}
	size := memorySize(instr.Mnemonic, regs[0].Class)
	if int64(1)<<uint(shift) != size || bound == 0 || bound > 64 {
		return "a frame load at a data-dependent index (the guard's bound or the scale is outside the subset)", false
	}
	if state.unknownFrom != nil && base+int64(bound)*size > *state.unknownFrom {
		return "a frame load at a data-dependent index into the frame's unknown region", false
	}
	merged, reason, ok := x.mergedFrameElements(state, base, index, bound, size)
	if !ok {
		return reason, false
	}
	if isSignExtendingLoad(instr.Mnemonic) {
		state.write(regs[0], extendTerm(merged, int(size)*8, widthOf(regs[0].Class), true))
	} else {
		state.write(regs[0], zeroExtend(merged, widthOf(regs[0].Class)))
	}
	return "", true
}

// mergedFrameElements reads the bound elements of size bytes at base,
// merged under `index == e` from the last element down, the last the
// default (Oak.FrameIndex) — the value of a frame load at a guarded
// data-dependent index on either lane.
func (x *pathExecutor) mergedFrameElements(state *symbolicState, base int64, index *term, bound uint64, size int64) (*term, string, bool) {
	if bound == 0 || bound > 64 {
		return nil, "a frame load at a data-dependent index (the guard's bound is outside the subset)", false
	}
	if state.unknownFrom != nil && base+int64(bound)*size > *state.unknownFrom {
		return nil, "a frame load at a data-dependent index into the frame's unknown region", false
	}
	var merged *term
	for e := int64(bound) - 1; e >= 0; e-- {
		value, ok := x.loadFrame(state, base+e*size, size)
		if !ok {
			return nil, "a frame load at a data-dependent index over a slot never stored on this path", false
		}
		value = truncate(value, int(size)*8)
		if merged == nil {
			merged = value // the last element: the default beyond the bound
			continue
		}
		merged = iteTerm(cmpTerm("eq", index, constTerm(uint64(e), 32)), value, merged)
	}
	return merged, "", true
}

// opaqueSlot is the value of a slot in the forgotten region: a fresh
// symbol per address and width, the same on every read.
func (s *symbolicState) opaqueSlot(addr, size int64) (*term, bool) {
	if s.unknownFrom == nil || addr < *s.unknownFrom {
		return nil, false
	}
	return paramTerm(fmt.Sprintf("frame#%d", addr), int(size)*8), true
}

// forgetFrameFrom drops every frame slot at or above addr and marks the
// region unknown: a later load there reads an opaque symbol `frame#addr`.
func (s *symbolicState) forgetFrameFrom(addr int64) {
	for start := range s.frame {
		if start >= addr {
			delete(s.frame, start)
		}
	}
	if s.unknownFrom == nil || *s.unknownFrom > addr {
		at := addr
		s.unknownFrom = &at
	}
}

// trapPath marks a path that ends in a trap (brk): it yields no result and
// is dropped from the fork that reached it. A body that traps on every
// path has no result to verify.
var trapPath = &term{kind: termConst, width: 64}

// cellWidth is the width a global's cell is modeled at: its storage width,
// except a Bool, whose C cell holds 0 or 1 in a word — one bit, zero-extended
// on a load and truncated on a store (Oak's typing keeps a Bool 0 or 1).
func cellWidth(global Global) int {
	if global.Type == "Bool" {
		return 1
	}
	return global.Bits
}

// cellEntry is a global's value on entry: the parameter `global:NAME`.
func cellEntry(name string, global Global) *term {
	return paramTerm(globalParam(name), cellWidth(global))
}

// mergeCells joins the written cells of a fork's two paths: a cell written
// on one side only meets its entry value on the other.
func (x *pathExecutor) mergeCells(cond *term, taken, fallThrough map[string]*term) map[string]*term {
	if len(taken) == 0 && len(fallThrough) == 0 {
		return nil
	}
	merged := map[string]*term{}
	for name := range taken {
		merged[name] = nil
	}
	for name := range fallThrough {
		merged[name] = nil
	}
	for name := range merged {
		t, f := taken[name], fallThrough[name]
		if t == nil {
			t = cellEntry(name, x.globals[name])
		}
		if f == nil {
			f = cellEntry(name, x.globals[name])
		}
		merged[name] = iteTerm(cond, t, f)
	}
	return merged
}

// globalStore executes a store through a global's address: the cell takes
// the stored register's value at the cell's width. Reports whether the
// instruction was such a store.
func (x *pathExecutor) globalStore(instr Instruction, state *symbolicState) (handled bool, reason string, ok bool) {
	if !isStoreMnemonic(instr.Mnemonic) || len(instr.Operands) != 2 {
		return false, "", false
	}
	mem, isMem := instr.Operands[1].(Memory)
	if !isMem || mem.Base.Class != ClassX {
		return false, "", false
	}
	base, bound := state.regs[mem.Base.Num]
	if !bound {
		return false, "", false
	}
	name, isGlobal := globalAddrOf(base)
	if !isGlobal {
		return false, "", false
	}
	global, known := x.globals[name]
	if !known {
		return true, "a store through the address of an undeclared global", false
	}
	if global.Aggregate {
		return true, "a store into a top-level record or array (not modeled)", false
	}
	src, isReg := instr.Operands[0].(Register)
	if !isReg || src.Class == ClassV {
		return true, "a vector-register store to a global", false
	}
	if mem.Index != nil || mem.Mode != MemOffset || mem.Offset != 0 {
		return true, "a store through a global's address away from its cell", false
	}
	if size := memorySize(instr.Mnemonic, src.Class); int(size)*8 != global.Bits {
		return true, fmt.Sprintf("a %d-byte store to the %d-bit global %s", size, global.Bits, name), false
	}
	value, okValue := state.read(src)
	if !okValue {
		return true, "unbound register read", false
	}
	if state.globals == nil {
		state.globals = map[string]*term{}
	}
	state.globals[name] = truncate(value, cellWidth(global))
	return true, "", true
}

// unitResult is the result of a path through a function with no result:
// only the package state it writes is compared.
var unitResult = &term{kind: termConst, width: 64}

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
// run executes from item index pc to a ret on every path: the result term
// and the effects (the package-global cells and the span memories
// written), merged across the paths.
func (x *pathExecutor) run(pc int, state *symbolicState) (*term, *pathEffects, string, bool) {
	x.paths++
	if x.paths > pathBudget {
		return nil, nil, "more paths than the verifier's budget (a loop whose trip count depends on the inputs, or too many forks)", false
	}
	for ; pc < len(x.items); pc++ {
		if n := len(x.stops); n > 0 && pc == x.stops[n-1] {
			// The join the enclosing fork collects: this path parks here.
			x.joined = append(x.joined, state)
			return nil, nil, "", true
		}
		instr, isInstr := x.items[pc].(Instruction)
		if !isInstr {
			continue // a label is a position
		}
		x.steps++
		if x.steps > stepBudget || (x.concrete && x.steps > witnessStepBudget) {
			return nil, nil, "more instructions than the verifier's unrolling budget (a loop whose trip count depends on the inputs)", false
		}
		switch instr.Mnemonic {
		case "ret":
			if !x.hasResult {
				return x.end(unitResult, state)
			}
			if x.resultClass == ClassV && (x.arch != ArchRV64 || x.floatResult == 0) {
				// A vector result: v0 on AArch64, v8 on RV64 (the RVV psABI);
				// an AArch64 float result is the low lane of v0.
				vreg := 0
				if x.arch == ArchRV64 {
					vreg = rv64VectorResultRegister
				}
				value, ok := state.readVec(vreg)
				if !ok {
					return nil, nil, "result register never written", false
				}
				if x.floatResult != 0 {
					return x.end(value.lanesAt(x.floatResult)[0], state)
				}
				return x.end(value.halves()[x.resultHalf], state)
			}
			if x.resultArea != nil {
				// The chunk of the result area the caller reads: each leaf in
				// it from the slot the body stored, at its offset and width.
				chunk, reason, okArea := x.resultAreaChunk(state)
				if !okArea {
					return nil, nil, atInstruction(reason, instr), false
				}
				return x.end(chunk, state)
			}
			result, ok := state.read(x.resultReg)
			if !ok {
				return nil, nil, "result register never written", false
			}
			if x.arch == ArchRV64 {
				// a0 holds the widened result; the contract width reads it.
				// An f32/f64 result is fa0 at its width (LP64D).
				if x.floatResult != 0 {
					result = truncate(result, x.floatResult)
				} else {
					result = truncate(result, widthOf(x.resultClass))
				}
			}
			return x.end(result, state)
		case "brk", "ebreak":
			// A trap: this path delivers no result. The Oak body traps on
			// the same inputs (a failed bounds check, division by zero, an
			// overflowing shift, a failed assert), so the path is outside
			// the equivalence: it drops from the fork it came from, and
			// the condition that reached it leaves the input domain
			// (pathEffects.trap).
			x.ends = append(x.ends, pathEnd{result: trapPath, cond: state.pathCondition(), path: state.path})
			return nil, nil, "", true
		case "bl":
			x.callAt = pc
			if reason, ok := x.summarizeCall(instr, state); !ok {
				return nil, nil, atInstruction(reason, instr), false
			}
			continue
		case "adrl":
			// A constant table's address: the base of the span its Oak
			// name denotes (executeBodyChunk).
			dest := instr.Operands[0].(Register)
			sym, isSym := instr.Operands[1].(Symbol)
			if !isSym {
				return nil, nil, "adrl without a symbol", false
			}
			if x.fn == nil {
				return nil, nil, "adrl of a symbol that is not a constant table", false
			}
			if _, known := x.fn.Tables[sym.Name]; !known {
				return nil, nil, "adrl of a symbol that is not a constant table", false
			}
			state.write(dest, paramTerm(spanBaseName(TableName(sym.Name)), 64))
			continue
		case "b", "j":
			target, ok := x.labels[instr.Operands[0].(Symbol).Name]
			if !ok {
				return nil, nil, "a branch to an unknown label", false
			}
			pc = target - 1 // backward: a loop, bounded by the budgets
			continue
		case "b.", "cbz", "cbnz", "tbz", "tbnz", "beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz", "bnez", "bgez", "bltz", "blez", "bgtz":
			cond, reason, ok := branchCondition(instr, state)
			if !ok {
				return nil, nil, atInstruction(reason, instr), false
			}
			target, ok := x.labels[instr.Operands[len(instr.Operands)-1].(Symbol).Name]
			if !ok {
				return nil, nil, "a branch to an unknown label", false
			}
			if cond.kind == termConst {
				// Decided: one continuation. A counted loop's backward
				// branch always lands here — on every path, since the
				// counter it compares is constant whatever the inputs did
				// inside the loop; the path and step budgets bound the
				// unfolding of forks inside it. A counted loop whose body
				// holds a loop (its own, or a callee's) is the exception:
				// unrolled, each copy of the body would summarize the inner
				// loop again — sixteen copies of a verifier's inner search
				// against a budget of eight events — so it is summarized
				// as a loop like a data-dependent one, and the Oak side
				// summarizes the same loop (lowerWhile).
				if shape, isLoopExit := x.loopExits[pc]; isLoopExit && cond.value == 0 && !x.concrete && x.summarizeCounted(shape, instr, state) {
					return x.loopEvent(shape, instr, state)
				}
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
			if isTrapBlock(x.items, target) {
				// A guard: the taken side traps, an end under the guard's
				// condition (the Oak body traps on the same inputs, which
				// leave the domain); this path continues past it under the
				// bound the guard establishes, no fork recorded.
				x.ends = append(x.ends, pathEnd{result: trapPath, cond: conjoin(state.pathCondition(), truncate(cond, 1)), path: state.path})
				state.noteTrapGuard(instr)
				// The trapping side counts as the path it was: a counted
				// loop guarding every iteration meets the path budget as
				// it did, rather than unrolling to the step budget with a
				// write log the decision cannot afford.
				x.paths++
				if x.paths > pathBudget {
					return nil, nil, "more paths than the verifier's budget (a loop whose trip count depends on the inputs, or too many forks)", false
				}
				continue
			}
			// Any other undecided branch forks. A forward fork whose paths
			// meet again (its immediate post-dominator, joinPoints) runs
			// each side to the join, merges the states parked there into
			// one — each register, slot, cell, and memory a select on the
			// path condition — and continues once; without a join, or a
			// backward branch (an unrecognized loop unfolding until the
			// budgets stop it), each side runs to its end.
			fork := &forkMark{pc: pc, cond: cond}
			parent := state.path
			takenState := state.clone()
			takenState.assume(cond, fork, true)
			state.assume(notTerm(cond), fork, false)
			// Each side learns what the branch decided about its register.
			bindZeroTest(instr, takenState, true)
			bindZeroTest(instr, state, false)
			// The fall-through side runs first at a forward fork: the
			// layout's order, which is the Oak body's (`c ? then | else`
			// lays the then block after the branch and jumps to the else
			// block), so the loops the two sides summarize take their
			// indices in the order the Oak side's do — the coupling pairs
			// the k-th event of each side — and a merged state selects
			// `taken ? … : fall-through` under the branch condition's
			// negation, the Oak body's own condition. A loop body's
			// worklist (runBody) runs the fall-through side first too.
			join, hasJoin := x.joins[pc]
			if !hasJoin || target <= pc || join <= pc {
				if target > pc {
					if _, _, reason, ok := x.run(pc+1, state); !ok {
						return nil, nil, atInstruction(reason, instr), false
					}
					return x.run(target, takenState)
				}
				if _, _, reason, ok := x.run(target, takenState); !ok {
					return nil, nil, atInstruction(reason, instr), false
				}
				return x.run(pc+1, state)
			}
			mark := len(x.joined)
			x.stops = append(x.stops, join)
			_, _, reason, ok = x.run(pc+1, state)
			if ok {
				_, _, reason, ok = x.run(target, takenState)
			}
			x.stops = x.stops[:len(x.stops)-1]
			if !ok {
				return nil, nil, atInstruction(reason, instr), false
			}
			parked := append([]*symbolicState(nil), x.joined[mark:]...)
			x.joined = x.joined[:mark]
			if len(parked) == 0 {
				return nil, nil, "", true // both sides ended before the join
			}
			merged, mergeable := x.mergeStates(parent, parked)
			if !mergeable {
				for _, parkedState := range parked {
					if _, _, reason, ok := x.run(join, parkedState); !ok {
						return nil, nil, atInstruction(reason, instr), false
					}
				}
				return nil, nil, "", true
			}
			return x.run(join, merged)
		}
		if x.arch == ArchRV64 {
			if reason, ok := x.stepRV64(instr, state); !ok {
				return nil, nil, atInstruction(reason, instr), false
			}
			continue
		}
		if isFrameMemory(instr) {
			if reason, ok := x.frameAccess(instr, state); !ok {
				return nil, nil, atInstruction(reason, instr), false
			}
			continue
		}
		if mem, base, isFrame := registerFrameMemory(instr, state); isFrame {
			if reason, ok := x.registerFrameAccess(instr, state, mem, base); !ok {
				return nil, nil, atInstruction(reason, instr), false
			}
			continue
		}
		if handled, reason, ok := x.atomicInstruction(instr, state); handled {
			// An exclusive store, an LSE atomic, or clrex through a span
			// element (asm/atomics.go).
			if !ok {
				return nil, nil, atInstruction(reason, instr), false
			}
			continue
		}
		if instr.Mnemonic == "ldp" {
			if reason, ok := x.loadPair(instr, state); !ok {
				return nil, nil, atInstruction(reason, instr), false
			}
			continue
		}
		if isLoad(instr.Mnemonic) {
			if dest, isReg := instr.Operands[0].(Register); isReg && dest.Class == ClassV {
				if reason, ok := x.loadVector(instr, state); !ok {
					return nil, nil, atInstruction(reason, instr), false
				}
				continue
			}
			if reason, ok := x.load(instr, state); !ok {
				return nil, nil, atInstruction(reason, instr), false
			}
			continue
		}
		if handled, reason, ok := x.globalStore(instr, state); handled {
			if !ok {
				return nil, nil, atInstruction(reason, instr), false
			}
			continue
		}
		if handled, reason, ok := x.spanStore(instr, state); handled {
			if !ok {
				return nil, nil, atInstruction(reason, instr), false
			}
			continue
		}
		if hasVectorOperand(instr) {
			if reason, ok := x.stepVector(instr, state); !ok {
				return nil, nil, atInstruction(reason, instr), false
			}
			continue
		}
		if reason, ok := step(instr, state); !ok {
			return nil, nil, atInstruction(reason, instr), false
		}
	}
	return nil, nil, "no ret reached", false
}

// atInstruction names the instruction behind a refusal that says nothing
// of where it arose (an unbound register read: which register, which
// line), so the verdict points at the code.
func atInstruction(reason string, instr Instruction) string {
	if reason == "unbound register read" {
		return fmt.Sprintf("unbound register read at line %d (%s)", instr.Line, instr.String())
	}
	return reason
}

// pathEnd is one path's outcome: its result and effects, or trapPath, with
// the path that reached it and, for a trap, the exact condition (the path's
// with the guard's).
type pathEnd struct {
	result  *term
	effects *pathEffects
	cond    *term
	path    *pathNode
}

// end records a path that returned result from state.
func (x *pathExecutor) end(result *term, state *symbolicState) (*term, *pathEffects, string, bool) {
	x.ends = append(x.ends, pathEnd{result: result, effects: state.effects(), path: state.path})
	return nil, nil, "", true
}

// conjoin is the conjunction of two 1-bit conditions, either nil for true.
func conjoin(a, b *term) *term {
	switch {
	case a == nil:
		return b
	case b == nil:
		return a
	}
	return binaryTerm("and", a, b)
}

// runAll executes the body from its first item and folds the paths' ends
// along the tree of forks they took (foldTree): the result and effects at
// a fork select on its condition between the two sides' — as they did
// when every path ran to its end — and the ends past a join stand in for
// both sides wherever a side parked rather than ended. The trap condition
// is the disjunction of the trapping ends' exact conditions. Every path
// trapping is trapPath.
func (x *pathExecutor) runAll(state *symbolicState) (*term, *pathEffects, string, bool) {
	if _, _, reason, ok := x.run(0, state); !ok {
		return nil, nil, reason, false
	}
	chains := make([][]*pathNode, len(x.ends))
	all := make([]int, len(x.ends))
	var trap *term
	for k, e := range x.ends {
		all[k] = k
		var chain []*pathNode
		for at := e.path; at != nil; at = at.parent {
			chain = append(chain, at)
		}
		for a, b := 0, len(chain)-1; a < b; a, b = a+1, b-1 {
			chain[a], chain[b] = chain[b], chain[a]
		}
		chains[k] = chain
		if e.result == trapPath {
			cond := e.cond
			if cond == nil {
				cond = constTerm(1, 1)
			}
			if trap == nil {
				trap = cond
			} else {
				trap = binaryTerm("or", cond, trap)
			}
		}
	}
	result, effects := x.foldTree(all, chains, 0, nil, nil)
	if result == nil {
		return trapPath, &pathEffects{trap: trap}, "", true
	}
	out := pathEffects{trap: trap}
	if effects != nil {
		out.cells, out.writes = effects.cells, effects.writes
	}
	return result, &out, "", true
}

// foldTree combines the ends whose paths share the first level nodes. At
// this level the paths either end (one returning end at most; trapping
// ends count only in the trap condition), fork — one fork, its sides
// folded in turn — or pass a join node, whose ends are the continuation
// both sides of the fork share: the fallback for a side that parked there
// instead of ending. A side with no value (it trapped, or every path in
// it did) yields the other side's, as the fork did when its paths ran to
// their ends.
func (x *pathExecutor) foldTree(ends []int, chains [][]*pathNode, level int, fallback *term, fallbackEffects *pathEffects) (*term, *pathEffects) {
	var here *pathEnd
	var fork *forkMark
	var trueEnds, falseEnds, joinEnds []int
	for _, k := range ends {
		chain := chains[k]
		if len(chain) <= level {
			if x.ends[k].result != trapPath {
				e := x.ends[k]
				here = &e
			}
			continue
		}
		node := chain[level]
		switch {
		case node.fork == nil:
			joinEnds = append(joinEnds, k)
		case node.side:
			fork = node.fork
			trueEnds = append(trueEnds, k)
		default:
			fork = node.fork
			falseEnds = append(falseEnds, k)
		}
	}
	if here != nil {
		return here.result, here.effects
	}
	if len(joinEnds) > 0 {
		fallback, fallbackEffects = x.foldTree(joinEnds, chains, level+1, fallback, fallbackEffects)
	}
	if fork == nil {
		return fallback, fallbackEffects
	}
	taken, takenEffects := x.foldTree(trueEnds, chains, level+1, fallback, fallbackEffects)
	fallThrough, fallEffects := x.foldTree(falseEnds, chains, level+1, fallback, fallbackEffects)
	switch {
	case taken == nil:
		return fallThrough, fallEffects
	case fallThrough == nil:
		return taken, takenEffects
	}
	return iteTerm(fork.cond, taken, fallThrough), x.mergeEffects(fork.cond, takenEffects, fallEffects)
}

// mergeStates merges the states parked at a join into one continuation:
// the last parked stands, and each earlier one selects over it on its
// own (exact) path condition; the merged path is a join node under the
// fork's parent holding the disjunction of the merged paths' conditions
// relative to it. Reports false when two states cannot merge (the
// frames' depths differ).
func (x *pathExecutor) mergeStates(parent *pathNode, parked []*symbolicState) (*symbolicState, bool) {
	if len(parked) == 1 {
		return parked[0], true
	}
	acc := parked[len(parked)-1]
	rel := acc.path.conditionBelow(parent)
	for i := len(parked) - 2; i >= 0; i-- {
		s := parked[i]
		cond := s.pathCondition()
		if cond == nil {
			cond = constTerm(1, 1)
		}
		merged, ok := x.mergeTwo(cond, s, acc)
		if !ok {
			return nil, false
		}
		acc = merged
		if below := s.path.conditionBelow(parent); below != nil && rel != nil {
			rel = binaryTerm("or", below, rel)
		} else {
			rel = nil
		}
	}
	if rel == nil {
		rel = constTerm(1, 1)
	}
	acc.path = &pathNode{parent: parent, cond: rel}
	return acc, true
}

// mergeTwo merges two states: a under cond, b otherwise. What only one
// side holds — a register, a slot, a vector — is unbound after the merge
// (a read of it on the other path would have been unbound too); what both
// hold selects on cond; the flags are forgotten; the cells and memories
// merge as a fork's effects do; a bound survives when both sides hold it.
func (x *pathExecutor) mergeTwo(cond *term, a, b *symbolicState) (*symbolicState, bool) {
	if a.disp != b.disp || a.arch != b.arch {
		return nil, false
	}
	cond = truncate(cond, 1)
	sel := func(l, r *term) *term {
		if l == r || equalTerms(l, r) {
			return l
		}
		return iteTerm(cond, l, r)
	}
	out := &symbolicState{arch: a.arch, disp: a.disp, notes: a.notes, regs: map[int]*term{}, frame: map[int64]frameSlot{}}
	for reg, l := range a.regs {
		if r, has := b.regs[reg]; has {
			out.regs[reg] = sel(l, r)
		}
	}
	for addr, l := range a.frame {
		if r, has := b.frame[addr]; has && r.width == l.width {
			out.frame[addr] = frameSlot{value: sel(l.value, r.value), width: l.width}
		}
	}
	if a.vregs != nil && b.vregs != nil {
		out.vregs = map[int]vecValue{}
		for reg, l := range a.vregs {
			r, has := b.vregs[reg]
			if !has || r.bits != l.bits || len(r.lanes) != len(l.lanes) {
				continue
			}
			lanes := make([]*term, len(l.lanes))
			for k := range lanes {
				lanes[k] = sel(l.lanes[k], r.lanes[k])
			}
			out.vregs[reg] = vecValue{bits: l.bits, lanes: lanes}
		}
	}
	if a.fregs != nil && b.fregs != nil {
		out.fregs = map[int]*term{}
		for reg, l := range a.fregs {
			if r, has := b.fregs[reg]; has {
				out.fregs[reg] = sel(l, r)
			}
		}
	}
	if a.rvcfg != nil && b.rvcfg != nil && *a.rvcfg == *b.rvcfg {
		cfg := *a.rvcfg
		out.rvcfg = &cfg
	}
	out.globals = x.mergeCells(cond, a.globals, b.globals)
	out.writes = mergeWrites(cond, a.writes, b.writes)
	switch {
	case a.unknownFrom != nil && b.unknownFrom != nil:
		from := *a.unknownFrom
		if *b.unknownFrom < from {
			from = *b.unknownFrom
		}
		out.unknownFrom = &from
	case a.unknownFrom != nil:
		from := *a.unknownFrom
		out.unknownFrom = &from
	case b.unknownFrom != nil:
		from := *b.unknownFrom
		out.unknownFrom = &from
	}
	if len(a.bounds) > 0 && len(b.bounds) > 0 {
		out.bounds = map[int]uint64{}
		for reg, l := range a.bounds {
			if r, has := b.bounds[reg]; has && r == l {
				out.bounds[reg] = l
			}
		}
	}
	if len(a.termBounds) > 0 && len(b.termBounds) > 0 {
		out.termBounds = map[*term]uint64{}
		for t, l := range a.termBounds {
			if r, has := b.termBounds[t]; has && r == l {
				out.termBounds[t] = l
			}
		}
	}
	return out, true
}

// joinPoints maps each conditional branch to its immediate post-dominator
// among the items — the point every path from the branch passes on its
// way to a return or trap — when it has one other than the exit itself.
// Post-dominators by the iterative set equations over the items' control
// flow (a label falls through, a jump goes to its label, a conditional
// branch both ways, ret and brk leave).
func joinPoints(items []Item, labels map[string]int) map[int]int {
	n := len(items)
	if n == 0 {
		return nil
	}
	exit := n
	succ := make([][]int, n)
	for i, item := range items {
		instr, isInstr := item.(Instruction)
		next := i + 1
		if next >= n {
			next = exit
		}
		switch {
		case !isInstr:
			succ[i] = []int{next}
		case instr.Mnemonic == "ret" || instr.Mnemonic == "brk" || instr.Mnemonic == "ebreak":
			succ[i] = []int{exit}
		case isUnconditionalJump(instr.Mnemonic):
			if sym, isSym := instr.Operands[0].(Symbol); isSym {
				if target, known := labels[sym.Name]; known {
					succ[i] = []int{target}
					continue
				}
			}
			succ[i] = []int{exit}
		case isConditionalBranch(instr.Mnemonic) && len(instr.Operands) > 0:
			if isGuardBranch(items, labels, instr) {
				// A guard's trap path yields nothing: the meeting points
				// are those of the paths that yield.
				succ[i] = []int{next}
				continue
			}
			if sym, isSym := instr.Operands[len(instr.Operands)-1].(Symbol); isSym {
				if target, known := labels[sym.Name]; known {
					succ[i] = []int{target, next}
					continue
				}
			}
			succ[i] = []int{next}
		default:
			succ[i] = []int{next}
		}
	}
	words := (n + 1 + 63) / 64
	full := make([]uint64, words)
	for i := 0; i <= n; i++ {
		full[i/64] |= 1 << uint(i%64)
	}
	pdom := make([][]uint64, n+1)
	for i := 0; i < n; i++ {
		pdom[i] = append([]uint64(nil), full...)
	}
	pdom[exit] = make([]uint64, words)
	pdom[exit][exit/64] |= 1 << uint(exit%64)
	for changed := true; changed; {
		changed = false
		for i := n - 1; i >= 0; i-- {
			set := append([]uint64(nil), full...)
			for _, s := range succ[i] {
				for w := range set {
					set[w] &= pdom[s][w]
				}
			}
			set[i/64] |= 1 << uint(i%64)
			for w := range set {
				if set[w] != pdom[i][w] {
					pdom[i] = set
					changed = true
					break
				}
			}
		}
	}
	size := func(set []uint64) int {
		count := 0
		for _, w := range set {
			count += bits.OnesCount64(w)
		}
		return count
	}
	has := func(set []uint64, i int) bool { return set[i/64]&(1<<uint(i%64)) != 0 }
	joins := map[int]int{}
	for i := 0; i < n; i++ {
		instr, isInstr := items[i].(Instruction)
		if !isInstr || !isConditionalBranch(instr.Mnemonic) {
			continue
		}
		best, bestSize := -1, -1
		for d := 0; d < n; d++ {
			if d == i || !has(pdom[i], d) {
				continue
			}
			if sz := size(pdom[d]); sz > bestSize {
				best, bestSize = d, sz
			}
		}
		if best >= 0 {
			joins[i] = best
		}
	}
	return joins
}

// load executes `ldr rD, [xB, #off]` through a span base: the seam checker
// has already placed the access under a dominating length guard, so the
// verifier's only question is which element it reads. The offset must be a
// whole element and the register width the element's width; loads from the
// frame, stores, and moving bases are outside the subset.
// loadPair reads `ldp xA, xB, [xE, #off]` off a span element address
// (nativegen/pair_loads.go) as two loads of the register width, the
// second one width on; the frame's pairs are read before this.
func (x *pathExecutor) loadPair(instr Instruction, state *symbolicState) (string, bool) {
	if len(instr.Operands) != 3 {
		return "a pair load in a form the verifier does not read", false
	}
	first, okA := instr.Operands[0].(Register)
	second, okB := instr.Operands[1].(Register)
	mem, okM := instr.Operands[2].(Memory)
	if !okA || !okB || !okM || first.Class == ClassV || mem.Mode != MemOffset {
		return "a pair load the verifier does not read (a vector pair, or a pre/post-indexed form outside the frame)", false
	}
	if reason, ok := x.load(Instruction{Mnemonic: "ldr", Operands: []Operand{first, mem}, Line: instr.Line}, state); !ok {
		return reason, false
	}
	next := mem
	next.Offset += int64(widthOf(first.Class) / 8)
	return x.load(Instruction{Mnemonic: "ldr", Operands: []Operand{second, next}, Line: instr.Line}, state)
}

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
	if name, isGlobal := globalAddrOf(base); isGlobal {
		// The global's cell: its value on entry, a parameter of the proof
		// (a store to it leaves the body trusted, so the value never
		// changes along a verified path).
		global, known := x.globals[name]
		if !known {
			return "a load through the address of an undeclared global", false
		}
		if global.Aggregate {
			return "a load from a top-level record or array (not modeled)", false
		}
		if mem.Index != nil || mem.Mode != MemOffset || mem.Offset != 0 {
			return "a load through a global's address away from its cell", false
		}
		size := memorySize(instr.Mnemonic, dest.Class)
		if int(size)*8 != global.Bits {
			return fmt.Sprintf("a %d-byte load of the %d-bit global %s", size, global.Bits, name), false
		}
		// The cell's current value on this path: what a store on the path
		// put there, else the entry parameter.
		value, written := state.globals[name]
		if !written {
			value = cellEntry(name, global)
		}
		if isSignExtendingLoad(instr.Mnemonic) && cellWidth(global) == global.Bits {
			state.write(dest, extendTerm(value, global.Bits, widthOf(dest.Class), true))
		} else {
			state.write(dest, zeroExtend(value, widthOf(dest.Class)))
		}
		return "", true
	}
	if handled, reason, ok := x.recordSpanLoad(instr, dest, mem, base, state); handled {
		return reason, ok
	}
	param, baseOffset, isSpan := spanBaseOf(base)
	if !isSpan {
		// A span element's address in the base (an atomic cell reached by
		// storage path): the element is the index term's.
		name, offset, index, shift, isElement := elementBaseOf(base)
		if !isElement || mem.Mode != MemOffset {
			return "a load through a register that is not a span base", false
		}
		elem, known := x.spans[name]
		if derived, at, isDerived := spanAddressOf(base, elem); isDerived && known && elem > 0 {
			// A derived span's base (`subslice`), possibly re-sliced, with
			// or without a scaled index in the addressing mode: the root's
			// element at the indices' sum (asm/derived_spans.go).
			name, index, offset, shift = derived, at, 0, log2(elem)
			if mem.Index != nil {
				if int64(1)<<uint(mem.Shift) != elem {
					return "an indexed load whose scale is not the element size", false
				}
				further, ok := state.read(*mem.Index)
				if !ok {
					return "unbound register read", false
				}
				index = addIndex(index, truncate(further, 32))
			}
			if index == nil {
				index = constTerm(0, 32)
			}
		} else if mem.Index != nil {
			return "a load through a register that is not a span base", false
		}
		if !known || elem == 0 || int64(1)<<uint(shift) != elem || offset%elem != 0 || mem.Offset%elem != 0 {
			return "a load through an element address not aligned to an element", false
		}
		size := memorySize(instr.Mnemonic, dest.Class)
		if size != elem {
			return fmt.Sprintf("a %d-byte load over %d-byte elements", size, elem), false
		}
		at := truncate(index, 32)
		if extra := offset/elem + mem.Offset/elem; extra != 0 {
			at = binaryTerm("add", at, constTerm(uint64(extra), 32))
		}
		value := x.elementIn(state, name, at, int(elem)*8)
		if isSignExtendingLoad(instr.Mnemonic) {
			state.write(dest, extendTerm(value, int(elem)*8, widthOf(dest.Class), true))
		} else {
			state.write(dest, zeroExtend(value, widthOf(dest.Class)))
		}
		return "", true
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
	if size < elem || size%elem != 0 || isSignExtendingLoad(instr.Mnemonic) && size != elem {
		return fmt.Sprintf("a %d-byte load over %d-byte elements", size, elem), false
	}
	extend := func(element *term) *term {
		if isSignExtendingLoad(instr.Mnemonic) {
			return extendTerm(element, int(elem)*8, widthOf(dest.Class), true)
		}
		return zeroExtend(element, widthOf(dest.Class))
	}
	// A load wider than the element (`ldr x` over bytes, the little-endian
	// word assembly the native backend fuses, docs/spec/94-assembler.md §9)
	// reads size/elem consecutive elements: the value is the or of each
	// element shifted to its byte position — the term Oak's `u64(v[i]) |
	// u64(v[i+1]) << 8 | …` spells (Oak.Assembler.wide_load_assembles).
	wide := func(first *term) *term {
		if size == elem {
			return extend(x.elementIn(state, param, first, int(elem)*8))
		}
		var value *term
		for k := int64(0); k < size/elem; k++ {
			at := first
			if k != 0 {
				at = binaryTerm("add", truncate(first, 32), constTerm(uint64(k), 32))
			}
			element := zeroExtend(x.elementIn(state, param, at, int(elem)*8), widthOf(dest.Class))
			if k != 0 {
				element = binaryTerm("shl", element, constTerm(uint64(k*elem*8), widthOf(dest.Class)))
			}
			if value == nil {
				value = element
			} else {
				value = binaryTerm("or", value, element)
			}
		}
		return value
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
		state.write(dest, wide(truncate(index, 32)))
		return "", true
	}
	if mem.Offset < 0 || mem.Offset%elem != 0 {
		return "a load not aligned to an element", false
	}
	state.write(dest, wide(constTerm(uint64(mem.Offset/elem+baseIndex), 32)))
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
		// A leaf narrower than a byte (a Bool) still occupies its byte:
		// rounding its width down to zero bytes would drop a Bool at the
		// start of the window and read the field as zero.
		end := leaf.offset + (int64(leaf.width)+7)/8
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

// isLoad reports the load mnemonics the executor resolves through a span:
// the plain loads, and the acquire and exclusive loads of the atomics,
// whose value is the element's (their ordering is the checker's concern,
// not the term's; docs/spec/65-machine-memory.md section 7).
func isLoad(mnemonic string) bool {
	switch mnemonic {
	case "ldar", "ldarb", "ldarh", "ldxr", "ldxrb", "ldxrh", "ldaxr", "ldaxrb", "ldaxrh", "ldapr", "ldaprb", "ldaprh":
		// ldapr: the RCpc acquire load (Armv8.3, what clang emits for an
		// acquire load on the Apple cores and other LRCPC targets).
		return true
	}
	return isPlainLoad(mnemonic)
}

// elementBaseOf reads a register holding a span element's address —
// `add xE, xB, wI, uxtw #s` steps to add(base, shl(zext(wI), s)) — as the
// span, the constant part of the base offset, the element index term, and
// the shift; the native backend addresses an atomic cell this way.
func elementBaseOf(t *term) (param string, baseOffset int64, index *term, shift int, ok bool) {
	if t.kind != termBinary || t.op != "add" {
		return "", 0, nil, 0, false
	}
	for _, sides := range [][2]*term{{t.left, t.right}, {t.right, t.left}} {
		name, base, isSpan := spanBaseOf(sides[0])
		if !isSpan {
			continue
		}
		scaled := sides[1]
		if scaled.kind == termBinary && scaled.op == "shl" && scaled.right.kind == termConst {
			return name, base, scaled.left, int(scaled.right.value), true
		}
		return name, base, scaled, 0, true
	}
	return "", 0, nil, 0, false
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
	if instr.Mnemonic == "add" && len(instr.Operands) == 3 {
		if sym, isSym := instr.Operands[2].(Symbol); isSym && sym.Lo12 {
			// `add xA, xN, :lo12:G` over G's page: xA is G's address.
			dest := instr.Operands[0].(Register)
			base, ok := operandTerm(state, instr.Operands[1], 64)
			if !ok || base.kind != termParam || base.name != globalPageName(sym.Name) {
				return "add :lo12: over a register that does not hold the symbol's page", false
			}
			state.write(dest, paramTerm(globalAddrName(sym.Name), 64))
			return "", true
		}
	}
	for _, reg := range registerOperands(instr.Operands) {
		if reg.Class == ClassV {
			return "a floating-point or vector instruction (" + instr.Mnemonic + ")", false
		}
	}
	{
		switch instr.Mnemonic {
		case "mov", "movz":
			dest := instr.Operands[0].(Register)
			value, ok := operandTerm(state, instr.Operands[1], widthOf(dest.Class))
			if !ok {
				return "unbound register read", false
			}
			state.write(dest, value)
		case "movk":
			// Insert a halfword: the destination's other bits are kept.
			dest := instr.Operands[0].(Register)
			width := widthOf(dest.Class)
			imm, isImm := instr.Operands[1].(Immediate)
			if !isImm {
				return "movk without an immediate", false
			}
			old, ok := state.read(dest)
			if !ok {
				return "unbound register read", false
			}
			keep := ^(uint64(0xffff) << uint(imm.Shift)) & mask(width)
			kept := binaryTerm("and", old, constTerm(keep, width))
			state.write(dest, binaryTerm("or", kept, constTerm(uint64(imm.Value)<<uint(imm.Shift), width)))
		case "cmp":
			left := instr.Operands[0].(Register)
			width := widthOf(left.Class)
			l, okL := operandTerm(state, left, width)
			r, okR := operandTerm(state, instr.Operands[1], width)
			if !okL || !okR {
				return "unbound register read", false
			}
			state.flags = &flagsFact{left: l, right: r, width: width, indexReg: -1}
			// `cmp wI, #K` bounds an index; `cmp xN, #K` bounds a 64-bit
			// shift count (the backend's guard before `lsl xD, xS, xN`,
			// docs/spec/94-assembler.md §8, variable shift counts). The
			// bound is kept by register number: below K in xN, the low
			// half wN is below K too.
			if imm, isImm := instr.Operands[1].(Immediate); isImm && (left.Class == ClassW || left.Class == ClassX) && imm.Shift == 0 {
				state.flags.indexReg, state.flags.bound = left.Num, uint64(imm.Value)
			}
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
			state.flags = &flagsFact{left: l, right: r, width: width, kind: "and", indexReg: -1}
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
		case "udiv", "sdiv":
			// The quotient as the uninterpreted operation (asm/floats_ops.go);
			// the lowering's msub then forms the remainder a - q*b.
			dest := instr.Operands[0].(Register)
			width := widthOf(dest.Class)
			n, okN := operandTerm(state, instr.Operands[1], width)
			m, okM := operandTerm(state, instr.Operands[2], width)
			if !okN || !okM {
				return "unbound register read", false
			}
			state.write(dest, floatTerm(instr.Mnemonic, width, n, m))
		case "umaddl", "smaddl":
			// xD = xA + ext32(wN) * ext32(wM): the element idiom's stride
			// multiply (docs/spec/94-assembler.md §9).
			dest := instr.Operands[0].(Register)
			n, okN := operandTerm(state, instr.Operands[1], 32)
			m, okM := operandTerm(state, instr.Operands[2], 32)
			a, okA := operandTerm(state, instr.Operands[3], 64)
			if !okN || !okM || !okA {
				return "unbound register read", false
			}
			signed := instr.Mnemonic == "smaddl"
			product := binaryTerm("mul", extendTerm(n, 32, 64, signed), extendTerm(m, 32, 64, signed))
			state.write(dest, binaryTerm("add", a, product))
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
		case "csinc":
			// Wd = cond ? Wn : Wm + 1 — the if-converted arm assigning 1
			// (`found = true`) selects from wzr (nativegen/select.go).
			if state.flags == nil || state.flags.unknown {
				return "csinc reading flags not produced by cmp/subs", false
			}
			code := instr.Operands[3].(Condition).Code
			if !verifiableConditions[code] {
				return fmt.Sprintf("condition code %s", code), false
			}
			dest := instr.Operands[0].(Register)
			width := widthOf(dest.Class)
			whenTrue, okT := operandTerm(state, instr.Operands[1], width)
			other, okF := operandTerm(state, instr.Operands[2], width)
			if !okT || !okF {
				return "unbound register read", false
			}
			state.write(dest, iteTerm(flagsCondition(code, state.flags), whenTrue, binaryTerm("add", other, constTerm(1, width))))
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
			state.flags = &flagsFact{left: l, right: r, width: width, cond: prior, elseNZCV: instr.Operands[2].(Immediate).Value, indexReg: -1}
		case "adrp":
			// A global's page address: a distinguished parameter the
			// completing `add :lo12:` recognizes.
			dest := instr.Operands[0].(Register)
			sym, isSym := instr.Operands[1].(Symbol)
			if !isSym {
				return "adrp without a symbol", false
			}
			state.write(dest, paramTerm(globalPageName(sym.Name), 64))
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
				state.flags = &flagsFact{left: left, right: right, width: widthOf(dest.Class), indexReg: -1}
			case "adds":
				state.flags = &flagsFact{left: left, right: right, width: widthOf(dest.Class), kind: "add", indexReg: -1}
			case "lsl", "lsr", "asr":
				if count, isReg := instr.Operands[2].(Register); isReg {
					state.noteVariableShift(count.Num)
				}
			}
			state.write(dest, binaryTerm(op, left, right))
		}
	}
	return "", true
}

// bindZeroTest records, on one side of a fork over a register's zero test
// (`cbz`, `cbnz`, `beqz`, `bnez`), what that side knows of the register:
// zero where the test says so, one where a one-bit value (a `cset`) is
// nonzero. An `assert(a && b)` lowers to a `cset` tested twice — once to
// skip the second test, once for the trap — and without this the path
// that skipped the second test forked on it again, a contradictory path
// that summarized every loop after the assert a second time.
func bindZeroTest(instr Instruction, state *symbolicState, taken bool) {
	var zeroWhenTaken bool
	switch instr.Mnemonic {
	case "cbz", "beqz":
		zeroWhenTaken = true
	case "cbnz", "bnez":
		zeroWhenTaken = false
	default:
		return
	}
	reg, isReg := instr.Operands[0].(Register)
	if !isReg {
		return
	}
	value, ok := state.read(reg)
	if !ok {
		return
	}
	width := widthOf(reg.Class)
	if taken == zeroWhenTaken {
		state.write(reg, constTerm(0, width))
	} else if significantBits(value) == 1 {
		state.write(reg, constTerm(1, width))
	}
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

// lowerVariableShift lowers `x << n` / `x >> n` of an unsigned operand
// whose count may reach the width for the assembler verifier
// (docs/spec/94-assembler.md §8, variable shift counts). Oak traps at the
// width (docs/spec/10-syntax.md §3b) and so does the native code — the
// backends guard the count and the executor drops the trapping path — so
// the equivalence is over the counts below the width, where Oak's shift is
// the machine's. The machine shifts at its register width modulo that
// width: the term is the shift at the register width, truncated back, so
// that on the dropped counts it is the machine's value rather than a
// claim about Oak (Oak.Shifts.shift_below_width; a claim over every
// input, with the trapping path's condition forgotten at the fork). A
// signed operand keeps the refusal: the backends leave those bodies to C.
func (lo *oakLowering) lowerVariableShift(e *ast.InfixExpression, op string, left, right *term, width int) (*term, string, bool) {
	_, signed, isScalar := lo.operandContract(e)
	if !isScalar || signed {
		return nil, "a non-constant shift count of a signed operand", false
	}
	if lo.concrete != nil {
		// A witness run: a count at the width is Oak trapping on this
		// input (on this path), and the run stops there.
		lo.addTrap(cmpTerm("hs", right, constTerm(uint64(width), right.width)))
		if lo.witnessTrapped {
			return nil, "a shift count reaching the width on this input", false
		}
	}
	if lo.shiftGuardMax > uint64(width) {
		// The machine's shift ran under no trap guard at Oak's width, so
		// Oak traps where the machine wraps: no claim.
		return nil, "a non-constant shift count (the machine's shift is not guarded at the width)", false
	}
	reg := 64
	if width <= 32 && (lo.arch != ArchRV64 || width == 32) {
		// AArch64 shifts a narrow operand in a w register; RV64 shifts
		// a 32-bit operand with sllw/srlw and a narrower one at XLEN.
		reg = 32
	}
	if reg == width {
		return binaryTerm(op, left, right), "", true
	}
	return truncate(binaryTerm(op, zeroExtend(left, reg), zeroExtend(right, reg)), width), "", true
}

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
	// writableSpans names the function's `[*]T` parameters: the spans a
	// loop body may store through, which take a loop's memory marker on
	// both sides (loopEvent, summarizeLoop).
	writableSpans map[string]bool
	// tagDomains: every union tag parameter with its variants' tag values
	// (recordTagDomains); the decision is over inputs inside them.
	tagDomains map[string][]int64
	// tableLens: the program's constant tables by Oak name with their
	// element counts; a table reads as a span (spans holds its contract)
	// whose length is the constant (declareTables).
	tableLens map[string]int64
	locals    map[string]*oakLocal // statement-body locals, in declaration scope
	concrete  map[string]uint64    // a witness run: parameters are these constants
	loops     []*loopEvent         // data-dependent loops met, in creation order
	loopStack []int                // indices of the loops whose bodies are being lowered
	fresh     map[string]int       // loop-carried fresh symbols -> width
	// arch is the lane an asm unit's Oak body is lowered against ("" for
	// the theorem decider): the RV64 lane's quotients are its own
	// operations (asm/floats_ops.go rv.udiv, rv.sdiv).
	arch        string
	quantifiers int // quantifier binders minted (lowerQuantifier)
	// resultChunk: for a record result of two register chunks, the chunk
	// this lowering's resultTerm packs (Verify runs one chunk at a time).
	resultChunk int
	// globals are the mutable top-level scalars the body addresses
	// (Function.Globals): a read of one is the parameter `global:NAME` of
	// the proof, the value the cell holds on entry; a write leaves the body
	// trusted (docs/spec/94-assembler.md §9).
	globals map[string]Global
	// recordSpans are the span parameters of records (recordSpanArg): a
	// field of an element lowers to the same select term the executor
	// forms from the element address.
	recordSpans map[string]recordSpanArg
	// cells: the globals as statement-body locals — declared by
	// prepareLowering at their entry values, so assignments, reads, and the
	// conditional merging of locals model the cells; their final values
	// are the Oak side's written state.
	cells map[string]*oakLocal
	// writes: the stores the body makes through span parameters, by
	// parameter, in program order, each under its path condition
	// (asm/effects.go); reads consult them before the entry memory.
	writes map[string][]*spanWrite
	// spanAlias maps an inlined callee's span parameter to the caller's
	// span it was passed (asm/effects.go): the callee's reads and writes
	// are spelled in the caller's names, so they share its memory.
	spanAlias map[string]string
	// spanOffset and spanLen: for a span parameter standing for a derived
	// span (`subslice(v, start, n)` of the caller's span), the 32-bit index
	// offset into the root and the length term (asm/derived_spans.go).
	spanOffset map[string]*term
	spanLen    map[string]*term
	// views: the span or view locals over aggregate locals (asm/agg_views.go).
	views map[string]aggView
	// bounds memoizes maxValue over the lowering's terms (asm/range.go).
	bounds map[*term]uint64
	// loopBase offsets the indices of the loop events this lowering
	// creates: a callee lowered inside a call summary numbers its loops
	// after the caller's, so the fresh symbols `loop<k>.<var>` of the two
	// sides — which inline the same callee body — coincide (asm/loops.go).
	loopBase int
	// rootContracts holds the element contracts of the caller-rooted
	// writable spans a loop marks (loopEvent), for a callee lowering whose
	// own span names are aliases of them.
	rootContracts map[string]spanContract
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
	// witnessTrapped: in a witness run (concrete), a trap condition held
	// on the input — Oak traps there (addTrap). The witness comparisons
	// skip such an input, and the machine trapping on an input without it
	// is a mismatch (machineTrapsWhereOakYields, verifyLoops).
	witnessTrapped bool
	// witnessMemo shares the values of subterms across the witness run's
	// trap evaluations (the path conditions and indices repeat).
	witnessMemo mapMemo
	// machineTrap is the asm side's trap condition (pathExecutor.trap):
	// the inputs on which the machine trapped — where Oak traps too, on
	// the same guard — leave the input domain (domainCondition).
	machineTrap *term
	// shiftGuardMax: the executor's largest trap bound over the register
	// count shifts it ran (pathNotes); a variable shift count lowers only
	// under a guard at or below its width.
	shiftGuardMax uint64
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
	// constants are the program's folded constant globals
	// (asm.Function.Constants): an identifier naming one is that value.
	constants map[string]Constant
	types     map[string]*oakType
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
	float    bool // a scalar that is an IEEE bit pattern (the syntax table only)
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
	if shape, isVector := vectorShape(expr); isVector {
		// A fixed vector: its lane array (asm/verify_simd.go), one shared
		// type per shape so a callee's declared result is the caller's.
		return lo.vectorType(shape), true
	}
	if width, signed, ok := contractBits(expr); ok {
		text := typeText(expr)
		return &oakType{kind: oakScalar, width: width, signed: signed, float: text == "f32" || text == "f64"}, true
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
		place, reason, ok := lo.readPlace(expr)
		if !ok {
			return nil, reason, false
		}
		if !sameType(place.typ, typ) {
			return nil, fmt.Sprintf("%s is not a %s", expr.String(), typ.name), false
		}
		return place.copy(), "", true
	case *ast.InvocationExpression:
		// A vector operation is the aggregate of its lanes (asm/verify_simd.go).
		if member, isSimd := simdMember(e.Function); isSimd {
			return lo.simdVectorValue(member, e.Arguments, typ)
		}
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
			if lo.concrete != nil && cond.kind == termConst {
				if cond.value&1 == 1 {
					return lo.aggregateValue(whenTrue, typ)
				}
				return lo.aggregateValue(whenFalse, typ)
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
		if handled, reason, ok := lo.lowerUnitCall(s.Expression); handled {
			return reason, ok
		}
		return "an expression statement before the end of a block", false
	}
	return fmt.Sprintf("%T", stmt), false
}

// unitFunction reports a function with no result: no return type, or the
// unit type `()` spelled out.
func unitFunction(fn *ast.FunctionStatement) bool {
	return fn.ReturnType == nil || typeText(fn.ReturnType) == "()"
}

// lowerUnitCall inlines a call in statement position to a function with no
// result: its statements run in the caller's scope of cells (enterCall),
// so the package state it writes is the caller's. Reports whether the
// expression was such a call.
func (lo *oakLowering) lowerUnitCall(expr ast.Expression) (handled bool, reason string, ok bool) {
	call, isCall := expr.(*ast.InvocationExpression)
	if !isCall {
		return false, "", false
	}
	if handled, reason, ok := lo.simdStore(call); handled {
		// simd.store_<shape>: lanes into a span's write log (asm/verify_simd.go).
		return true, reason, ok
	}
	ident, isIdent := call.Function.(*ast.Identifier)
	if !isIdent || call.ResolvedMethod != "" {
		return false, "", false
	}
	if spec, isAtomic := semir.LookupAtomicBuiltin(ident.Value); isAtomic {
		// An atomic in statement position: its write (a fence has none;
		// a returned value is dropped), asm/atomics.go.
		_, reason, ok := lo.lowerAtomic(spec, call, 64)
		return true, reason, ok
	}
	callee := lo.functions[ident.Value]
	if callee == nil || !unitFunction(callee) || callee.Body == nil {
		return false, "", false
	}
	restore, reason, ok := lo.enterCall(callee, call)
	if !ok {
		return true, reason, false
	}
	defer restore()
	if reason, ok := lo.lowerUnitBody(callee.Body); !ok {
		return true, fmt.Sprintf("a call to %s whose body contains %s", ident.Value, reason), false
	}
	return true, "", true
}

// addTrap records a trap condition under the current path condition.
func (lo *oakLowering) addTrap(t *term) {
	t = truncate(t, 1)
	if lo.path != nil {
		t = binaryTerm("and", lo.path, t)
	}
	if lo.concrete != nil {
		// A witness run: the condition is decided on the input (its
		// parameters, lengths, and elements), and so is the path it lies
		// on (a dead arm's trap is no trap).
		if lo.witnessMemo == nil {
			lo.witnessMemo = mapMemo{}
		}
		if lo.witnessMemo.eval(t, lo.concrete)&1 == 1 {
			lo.witnessTrapped = true
		}
		return
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

func notTerm(t *term) *term {
	if t.kind == termCmp {
		if neg := negatedCmp(truncate(t, 1)); neg != nil {
			return neg
		}
	}
	return binaryTerm("xor", truncate(t, 1), constTerm(1, 1))
}

// narrowComparison narrows an unsigned comparison (or an equality) whose
// operands, at one width, both fit a smaller natural width — parameters
// widened past their declared width, masked or one-bit values — to that
// width: the comparison's value is the same, and it is the width the Oak
// body compares at. Nil when nothing narrows.
func narrowComparison(t, left, right *term) *term {
	switch t.op {
	case "eq", "ne", "hs", "lo", "hi", "ls":
	default:
		return nil
	}
	if left.width != right.width || left.width <= 8 {
		return nil
	}
	fit := max(significantBits(left), significantBits(right))
	if fit <= 1 {
		return nil // 1/0 values: the boolean rules read the comparison
	}
	w := 8
	for w < fit {
		w *= 2
	}
	if w >= left.width {
		return nil
	}
	return &term{kind: termCmp, width: t.width, op: t.op, left: adaptWidth(left, w), right: adaptWidth(right, w)}
}

// booleanValued reports a term whose value is 0 or 1 at its width: a
// comparison, a one-bit term or a constant 0 or 1, a bitwise
// combination or conditional of such terms, a one-bit term extended.
func booleanValued(t *term, memo map[*term]bool) bool {
	if t.width == 1 {
		return true
	}
	if known, seen := memo[t]; seen {
		return known
	}
	memo[t] = false
	var is bool
	switch t.kind {
	case termConst:
		is = t.value <= 1
	case termCmp:
		is = true
	case termBinary:
		switch t.op {
		case "and":
			is = (t.right.kind == termConst && t.right.value == 1) || (t.left.kind == termConst && t.left.value == 1) || (booleanValued(t.left, memo) && booleanValued(t.right, memo))
		case "or", "xor":
			is = booleanValued(t.left, memo) && booleanValued(t.right, memo)
		}
	case termIte:
		is = booleanValued(t.left, memo) && booleanValued(t.right, memo)
	}
	memo[t] = is
	return is
}

// complementary reports whether two one-bit conditions are each other's
// negation: one the other's xor with 1, or comparisons of the same
// operands under opposite codes.
func complementary(a, b *term) bool {
	isNot := func(x, y *term) bool {
		if x.kind != termBinary || x.op != "xor" || x.right.kind != termConst || x.right.value != 1 {
			return false
		}
		budget := sameTermBudget
		return sameTerm(x.left, y, &budget)
	}
	if isNot(a, b) || isNot(b, a) {
		return true
	}
	if a.kind != termCmp || b.kind != termCmp || negatedCondition[a.op] != b.op {
		return false
	}
	budget := sameTermBudget
	return sameTerm(a.left, b.left, &budget) && sameTerm(a.right, b.right, &budget)
}

// negatedCmp is the one-bit comparison's negation as the opposite
// comparison (`lo` for `hs`, `ne` for `eq`), nil for a condition without
// one.
func negatedCmp(c *term) *term {
	neg, known := negatedCondition[c.op]
	if !known || c.kind != termCmp {
		return nil
	}
	return &term{kind: termCmp, width: 1, op: neg, left: c.left, right: c.right}
}

// lowerAssert records `assert(cond)` as a trap obligation under the
// theorem decider (docs/spec/85-discipline.md section 5: an assert is
// never elided; here the decider proves it cannot fire); under the
// assembler verifier it is a no-op, the trapping inputs being outside
// the equivalence on both sides.
func (lo *oakLowering) lowerAssert(expr ast.Expression) (reason string, isAssert bool, ok bool) {
	call, isCall := expr.(*ast.InvocationExpression)
	if !isCall || len(call.Arguments) != 1 {
		return "", false, false
	}
	if fn, isIdent := call.Function.(*ast.Identifier); !isIdent || fn.Value != "assert" {
		return "", false, false
	}
	if !lo.trapsTracked {
		// The assembler verifier's side: a failed assert traps, and the
		// executor drops a trapping path from its fork (a `brk` delivers
		// no result), so the equivalence is over the inputs on which the
		// assert holds and the statement itself is a no-op here — except
		// on a witness input, where a failed assert is Oak trapping on
		// that input (machineTrapsWhereOakYields).
		if lo.concrete != nil {
			cond, reason, ok := lo.lowerCondition(call.Arguments[0])
			if !ok {
				return reason, true, false
			}
			lo.addTrap(notTerm(cond)) // evaluated on the input under the path
			if lo.witnessTrapped {
				return "a failed assert on this input", true, false
			}
		} else if bodyHasLoop(call.Arguments[0], lo.functions) {
			// The loops a call in the condition runs: the machine side
			// executes the call and summarizes them, so the condition is
			// lowered for its loop events and its stores, its truth dropped.
			if _, reason, ok := lo.lowerCondition(call.Arguments[0]); !ok {
				return reason, true, false
			}
		}
		return "", true, true
	}
	cond, reason, ok := lo.lowerCondition(call.Arguments[0])
	if !ok {
		return reason, true, false
	}
	if lo.trapsTracked {
		lo.addTrap(binaryTerm("xor", truncate(cond, 1), constTerm(1, 1)))
	}
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
	return lo.placeIn(expr, false)
}

// readPlace is placeOf for a read: the base may also be a call or a
// literal yielding an aggregate (the value is materialized), and an array
// element may be at a data-dependent index (a mux over the elements under
// the index, with the out-of-range trap Oak takes as an obligation). The
// value returned is not a place to write through.
func (lo *oakLowering) readPlace(expr ast.Expression) (*oakValue, string, bool) {
	return lo.placeIn(expr, true)
}

func (lo *oakLowering) placeIn(expr ast.Expression, read bool) (*oakValue, string, bool) {
	switch e := expr.(type) {
	case *ast.Identifier:
		local, isLocal := lo.locals[e.Value]
		if !isLocal || local.agg == nil {
			return nil, fmt.Sprintf("%s is not an aggregate local", e.Value), false
		}
		return local.agg, "", true
	case *ast.InvocationExpression, *ast.RecordLiteral, *ast.VariantExpression:
		typ, isRoot := lo.aggregateRoot(e)
		if !read || !isRoot {
			return nil, fmt.Sprintf("%s as a place", e.String()), false
		}
		return lo.aggregateValue(e, typ)
	case *ast.IndexExpression:
		if view, isView := lo.viewOf(e.Left); isView && !e.Dot {
			// A view's element: the owner's under offset + i (asm/agg_views.go).
			if !read {
				return nil, "a view element as a write place", false
			}
			owner, reason, ok := lo.viewOwner(view)
			if !ok {
				return nil, reason, false
			}
			index, reason, ok := lo.lower(e.Index, 32)
			if !ok {
				return nil, reason, false
			}
			return lo.elementUnderIndexTerm(owner, viewIndex(view, index), view.length)
		}
		base, reason, ok := lo.placeIn(e.Left, read)
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
			if !read {
				return nil, "an array element at a data-dependent index", false
			}
			return lo.elementUnderIndex(base, e.Index)
		}
		if k < 0 || k >= base.typ.length {
			return nil, fmt.Sprintf("the index %d past [%d]", k, base.typ.length), false
		}
		return base.elems[k], "", true
	}
	return nil, fmt.Sprintf("%T as a place", expr), false
}

// elementUnderIndex reads an array element at a symbolic index: the
// elements merged leaf by leaf under `index == k`, and the index at or past
// the length recorded as a trap obligation (the bounds check Oak keeps).
func (lo *oakLowering) elementUnderIndex(base *oakValue, indexExpr ast.Expression) (*oakValue, string, bool) {
	index, reason, ok := lo.lower(indexExpr, 32)
	if !ok {
		return nil, reason, false
	}
	return lo.elementUnderIndexTerm(base, index, nil)
}

// elementUnderIndexTerm is elementUnderIndex at an index term; bound, when
// given, is a view's length, the index checked against it as the view's
// own bounds check (the owner's is the view's construction guard).
func (lo *oakLowering) elementUnderIndexTerm(base *oakValue, index *term, bound *term) (*oakValue, string, bool) {
	if len(base.elems) == 0 {
		return nil, "an element of an empty array", false
	}
	if bound == nil {
		bound = constTerm(uint64(base.typ.length), 32)
	}
	lo.addTrap(cmpTerm("hs", index, bound))
	if lo.witnessTrapped {
		return nil, "an index past the array's length on this input", false
	}
	out := base.elems[len(base.elems)-1].copy()
	for k := len(base.elems) - 2; k >= 0; k-- {
		out = mergeValues(cmpTerm("eq", index, constTerm(uint64(k), 32)), base.elems[k], out)
	}
	return out, "", true
}

// assignUnderIndex executes `arr[i] = e` at a symbolic index: the value is
// lowered once, and every element takes it under `i == k`.
func (lo *oakLowering) assignUnderIndex(base *oakValue, indexExpr ast.Expression, value ast.Expression) (string, bool) {
	index, reason, ok := lo.lower(indexExpr, 32)
	if !ok {
		return reason, false
	}
	return lo.assignUnderIndexTerm(base, index, nil, value)
}

// assignUnderIndexTerm is assignUnderIndex at an index term; bound as in
// elementUnderIndexTerm.
func (lo *oakLowering) assignUnderIndexTerm(base *oakValue, index *term, bound *term, value ast.Expression) (string, bool) {
	if len(base.elems) == 0 {
		return "an element of an empty array", false
	}
	if bound == nil {
		bound = constTerm(uint64(base.typ.length), 32)
	}
	lo.addTrap(cmpTerm("hs", index, bound))
	if lo.witnessTrapped {
		return "an index past the array's length on this input", false
	}
	fresh := base.elems[0].copy()
	if reason, ok := lo.assignPlace(fresh, value); !ok {
		return reason, false
	}
	for k, element := range base.elems {
		cond := cmpTerm("eq", index, constTerm(uint64(k), 32))
		leaves(fresh, element, func(f, e *oakValue) {
			e.scalar = iteTerm(truncate(cond, 1), f.scalar, e.scalar)
		})
	}
	return "", true
}

// paramAggregate builds a record or union parameter's aggregate: every
// scalar leaf the parameter term named by its access path (the executor's
// compositeLeaves spelling), a concrete value in a witness run.
func (lo *oakLowering) paramAggregate(typ *oakType, prefix string) (*oakValue, bool) {
	lo.recordTagDomains(typ, prefix)
	return aggregateFrom(typ, prefix, func(name string, leaf *oakType) *term {
		lo.params[name] = leaf.width
		lo.signed[name] = leaf.signed
		if value, isConcrete := lo.concrete[name]; isConcrete {
			return constTerm(value&mask(leaf.width), leaf.width)
		}
		return paramTerm(name, leaf.width)
	})
}

// recordTagDomains notes, for every union inside a parameter's type, the
// tag values its variants take (tagDomains): the equivalence is decided
// over well-typed inputs, where a tag is one of them. On a tag outside
// the variants the asm traps where the Oak match defaults through its
// last arm, and a union's payload leaves — assembled under the tag on the
// asm side (compositeLeaf.guarded), free on the Oak side — need not agree.
func (lo *oakLowering) recordTagDomains(typ *oakType, prefix string) {
	switch typ.kind {
	case oakRecord:
		for _, f := range typ.fields {
			lo.recordTagDomains(f.typ, prefix+"."+f.name)
		}
	case oakADT:
		tags := make([]int64, 0, len(typ.variants))
		for _, v := range typ.variants {
			tags = append(tags, v.tag)
			if v.payload != nil {
				lo.recordTagDomains(v.payload, prefix+"."+v.name)
			}
		}
		if lo.tagDomains == nil {
			lo.tagDomains = map[string][]int64{}
		}
		lo.tagDomains[prefix+".tag"] = tags
	case oakArray:
		for k := int64(0); k < typ.length; k++ {
			lo.recordTagDomains(typ.elem, fmt.Sprintf("%s[%d]", prefix, k))
		}
	}
}

// domainCondition is the 1-bit term "every union tag parameter holds one
// of its variants' values", or nil when the parameters have no unions.
func (lo *oakLowering) domainCondition() *term {
	var cond *term
	if lo.machineTrap != nil {
		cond = binaryTerm("xor", truncate(lo.machineTrap, 1), constTerm(1, 1))
	}
	names := make([]string, 0, len(lo.tagDomains))
	for name := range lo.tagDomains {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		var member *term
		for _, tag := range lo.tagDomains[name] {
			is := truncate(cmpTerm("eq", paramTerm(name, 32), constTerm(uint64(tag), 32)), 1)
			if member == nil {
				member = is
			} else {
				member = binaryTerm("or", member, is)
			}
		}
		if member == nil {
			continue
		}
		if cond == nil {
			cond = member
		} else {
			cond = binaryTerm("and", cond, member)
		}
	}
	return cond
}

// inDomain reports whether a witness assignment gives every union tag one
// of its variants' values.
func (lo *oakLowering) inDomain(env map[string]uint64) bool {
	for name, tags := range lo.tagDomains {
		value, bound := env[name]
		if !bound {
			continue
		}
		member := false
		for _, tag := range tags {
			if value == uint64(tag) {
				member = true
				break
			}
		}
		if !member {
			return false
		}
	}
	return true
}

// aggregateFrom builds an aggregate value of the type from a term per
// scalar leaf, the leaves named by access path under prefix (`.f`,
// `.tag`, `.Variant.x`, `[k]`) — the names compositeLeaves and leafTerms
// use, so a value built here packs (packAggregateChunk) to the chunks it
// was read from.
func aggregateFrom(typ *oakType, prefix string, leaf func(name string, typ *oakType) *term) (*oakValue, bool) {
	switch typ.kind {
	case oakScalar:
		t := leaf(prefix, typ)
		if t == nil {
			return nil, false
		}
		return &oakValue{typ: typ, scalar: t}, true
	case oakRecord:
		out := &oakValue{typ: typ, fields: map[string]*oakValue{}}
		for _, f := range typ.fields {
			value, ok := aggregateFrom(f.typ, prefix+"."+f.name, leaf)
			if !ok {
				return nil, false
			}
			out.fields[f.name] = value
		}
		return out, true
	case oakADT:
		out := &oakValue{typ: typ, fields: map[string]*oakValue{}}
		tag, ok := aggregateFrom(&oakType{kind: oakScalar, width: 32}, prefix+".tag", leaf)
		if !ok {
			return nil, false
		}
		out.fields["tag"] = tag
		for _, v := range typ.variants {
			if v.payload != nil {
				value, ok := aggregateFrom(v.payload, prefix+"."+v.name, leaf)
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
			value, ok := aggregateFrom(typ.elem, fmt.Sprintf("%s[%d]", prefix, k), leaf)
			if !ok {
				return nil, false
			}
			out.elems = append(out.elems, value)
		}
		return out, true
	}
}

// bindAggregateArgument binds a summarized callee's record or union
// parameter of up to two chunks from the argument registers at next
// (unpackAggregate); it reports the registers consumed.
func (x *pathExecutor) bindAggregateArgument(lo *oakLowering, param *ast.FunctionParameter, comp Composite, next, argBase int, state *symbolicState, name string) (int, string, bool) {
	paramText := typeText(param.Type)
	typ, isType := lo.oakTypeOf(param.Type)
	if len(comp.Fields) == 0 || !isType || typ.kind == oakScalar {
		return 0, fmt.Sprintf("a call to %s: parameter %s has a type without a model", name, param.Name.Value), false
	}
	leaves, _, ok := compositeLeaves(x.fn.Composites, paramText, "", 0, nil)
	if !ok {
		return 0, fmt.Sprintf("a call to %s: parameter %s (no layout)", name, param.Name.Value), false
	}
	chunks := make([]*term, (comp.Size+7)/8)
	if next+len(chunks) > argBase+8 {
		return 0, fmt.Sprintf("a call to %s with arguments beyond the registers", name), false
	}
	for k := range chunks {
		value, has := state.regs[next+k]
		if !has {
			return 0, "unbound register read", false
		}
		chunks[k] = value
	}
	value, ok := unpackAggregate(typ, leaves, chunks)
	if !ok {
		return 0, fmt.Sprintf("a call to %s: parameter %s has a leaf the layout lacks", name, param.Name.Value), false
	}
	lo.locals[param.Name.Value] = &oakLocal{agg: value}
	return len(chunks), "", true
}

// frameRecordArgument binds a summarized callee's by-reference record
// parameter to the caller's copy in its frame at addr: the record's
// 8-byte chunks read from the slots (a chunk's unstored bytes are the
// frame's unknowns) and unpacked leaf by leaf, as a by-value record's
// register chunks are (docs/spec/94-assembler.md §8, record arguments).
func (x *pathExecutor) frameRecordArgument(lo *oakLowering, param *ast.FunctionParameter, comp Composite, addr int64, state *symbolicState, name string) (string, bool) {
	paramText := typeText(param.Type)
	typ, isType := lo.oakTypeOf(param.Type)
	if len(comp.Fields) == 0 || !isType || typ.kind == oakScalar {
		return fmt.Sprintf("a call to %s: parameter %s has a type without a model", name, param.Name.Value), false
	}
	leaves, _, ok := compositeLeaves(x.fn.Composites, paramText, "", 0, nil)
	if !ok {
		return fmt.Sprintf("a call to %s: parameter %s (no layout)", name, param.Name.Value), false
	}
	if state.unknownFrom != nil && addr+comp.Size > *state.unknownFrom {
		return fmt.Sprintf("a call to %s: the record argument %s lies in the frame's unknown region", name, param.Name.Value), false
	}
	chunks := make([]*term, (comp.Size+7)/8)
	for k := range chunks {
		value, has := x.loadFrame(state, addr+int64(8*k), 8)
		if !has {
			return fmt.Sprintf("a call to %s: the record argument %s is not held in the frame", name, param.Name.Value), false
		}
		chunks[k] = value
	}
	value, ok := unpackAggregate(typ, leaves, chunks)
	if !ok {
		return fmt.Sprintf("a call to %s: parameter %s has a leaf the layout lacks", name, param.Name.Value), false
	}
	lo.locals[param.Name.Value] = &oakLocal{agg: value}
	return "", true
}

// unpackAggregate reads an aggregate value of the type from its register
// chunks (the inverse of packAggregateChunk): each leaf is the slice of
// the chunk at its offset and width.
func unpackAggregate(typ *oakType, leaves []compositeLeaf, chunks []*term) (*oakValue, bool) {
	byName := map[string]compositeLeaf{}
	for _, leaf := range leaves {
		byName[leaf.name] = leaf
	}
	return aggregateFrom(typ, "", func(name string, leafType *oakType) *term {
		leaf, has := byName[name]
		if !has {
			return nil
		}
		k := leaf.offset / 8
		if k < 0 || int(k) >= len(chunks) {
			return nil
		}
		shifted := chunks[k]
		if shift := (leaf.offset - 8*k) * 8; shift > 0 {
			shifted = binaryTerm("shr", shifted, constTerm(uint64(shift), 64))
		}
		return adaptWidth(truncate(shifted, leaf.width), leafType.width)
	})
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
	return packAggregateChunk(v, leaves, 0)
}

// packAggregateChunk packs the leaves inside register chunk k (bytes 8k
// to 8k+7) of an aggregate value, each at its offset from the chunk.
func packAggregateChunk(v *oakValue, leaves []compositeLeaf, k int64) (*term, bool) {
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
		if leaf.offset < 8*k || leaf.offset >= 8*k+8 {
			continue
		}
		t, has := terms[leaf.name]
		if !has {
			return nil, false
		}
		placed := zeroExtend(leaf.guarded(adaptWidth(t, leaf.width), tagTerm), 64)
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
	place, _, isAggregate := lo.readPlace(match.Scrutinee)
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

// sameType is structural identity: declared records and unions by name,
// arrays by element and length, scalars by width and signedness (an array
// type is built afresh at each mention, so pointer identity would part
// `[4]u8` from `[4]u8`).
func sameType(a, b *oakType) bool {
	if a == b {
		return true
	}
	if a == nil || b == nil || a.kind != b.kind {
		return false
	}
	switch a.kind {
	case oakScalar:
		return a.width == b.width && a.signed == b.signed
	case oakArray:
		return a.length == b.length && sameType(a.elem, b.elem)
	}
	return a.name == b.name
}

// aggregateRoot reports an expression that yields an aggregate without
// being a local: a call to a program function returning a record, union,
// or array, or a typed record literal or variant. A field or element read
// off such a value is lowered from the value (readPlace).
func (lo *oakLowering) aggregateRoot(expr ast.Expression) (*oakType, bool) {
	switch e := expr.(type) {
	case *ast.InvocationExpression:
		ident, isIdent := e.Function.(*ast.Identifier)
		if !isIdent {
			return nil, false
		}
		callee, known := lo.functions[ident.Value]
		if !known || callee.ReturnType == nil {
			return nil, false
		}
		typ, ok := lo.oakTypeOf(callee.ReturnType)
		if !ok || typ.kind == oakScalar {
			return nil, false
		}
		return typ, true
	case *ast.RecordLiteral:
		if e.TypeName == nil {
			return nil, false
		}
		return lo.namedType(e.TypeName.Value)
	case *ast.VariantExpression:
		if e.TypeName == nil {
			return nil, false
		}
		return lo.namedType(e.TypeName.Value)
	}
	return nil, false
}

// aggregateChain reports an access chain rooted at an aggregate local.
func (lo *oakLowering) aggregateChain(expr ast.Expression) bool {
	switch e := expr.(type) {
	case *ast.Identifier:
		if _, isView := lo.views[e.Value]; isView {
			return true
		}
		return lo.aggregateLocal(e.Value)
	case *ast.IndexExpression:
		if lo.aggregateChain(e.Left) {
			return true
		}
		_, isRoot := lo.aggregateRoot(e.Left)
		return isRoot
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
	if isBorrowType(s.Type) && s.Value != nil {
		return lo.declareSpanLocal(s)
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
		// Value-less storage is zero (docs/spec/90-backend.md §6): an
		// array's elements, a record's fields, a sum's tag and payloads,
		// as both backends fill them.
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

// declareSpanLocal declares a span or view local over one of the
// function's spans (docs/spec/94-assembler.md §8, derived spans): `w: []T
// = v` is an alias of v (with v's own offset and length when v is
// derived), `w: []T = subslice(v, start, n)` an alias of v's root at the
// offset start (plus v's) of length n, the C helper's check a trap
// obligation. The local's reads, writes, and `len` translate to the root
// (asm/derived_spans.go); a view over an owned array stays outside.
func (lo *oakLowering) declareSpanLocal(s *ast.VariableDeclaration) (string, bool) {
	name := s.Name.Value
	elem, _, ok := spanShape(s.Type)
	if !ok {
		return fmt.Sprintf("a local of type %s", typeText(s.Type)), false
	}
	if handled, reason, ok := lo.declareView(s, elem); handled {
		return reason, ok // a view over an aggregate local (asm/agg_views.go)
	}
	bind := func(src string, offset, length *term) (string, bool) {
		delete(lo.views, name)
		contract, isSpan := lo.spans[src]
		if _, isLocal := lo.locals[src]; isLocal || !isSpan {
			return fmt.Sprintf("the span local %s over %s, which is not a span", name, src), false
		}
		if int(elem)*8 != contract.elemWidth {
			return fmt.Sprintf("the span local %s over %s with %d-bit elements", name, src, contract.elemWidth), false
		}
		delete(lo.locals, name)
		lo.spans[name] = contract
		if lo.spanAlias == nil {
			lo.spanAlias = map[string]string{}
		}
		if lo.spanOffset == nil {
			lo.spanOffset, lo.spanLen = map[string]*term{}, map[string]*term{}
		}
		lo.spanAlias[name] = lo.spanRoot(src)
		delete(lo.spanOffset, name)
		delete(lo.spanLen, name)
		if offset != nil {
			lo.spanOffset[name] = offset
		}
		if length != nil {
			lo.spanLen[name] = length
		} else if srcLen, derived := lo.spanLen[src]; derived {
			lo.spanLen[name] = srcLen
		}
		return "", true
	}
	if src, isIdent := s.Value.(*ast.Identifier); isIdent {
		return bind(src.Value, lo.spanOffset[src.Value], nil)
	}
	sub, isSub := subsliceOf(s.Value)
	if !isSub {
		return fmt.Sprintf("the span local %s from %s", name, s.Value.String()), false
	}
	if _, isSpan := lo.spans[sub.span]; !isSpan {
		return fmt.Sprintf("the span local %s over %s, which is not a span", name, sub.span), false
	}
	start, reason, ok := lo.lower(sub.start, 32)
	if !ok {
		return reason, false
	}
	count, reason, ok := lo.lower(sub.count, 32)
	if !ok {
		return reason, false
	}
	length := lo.spanLenTerm(sub.span, 32)
	lo.addTrap(cmpTerm("hi", start, length))
	lo.addTrap(cmpTerm("hi", count, binaryTerm("sub", length, start)))
	if lo.witnessTrapped {
		return fmt.Sprintf("a subslice of %s past its length on this input", sub.span), false
	}
	return bind(sub.span, lo.spanIndex(sub.span, start), count)
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

// witnessLoopBudget and witnessStepBudget bound a witness run — one
// concrete input through the body — far below the symbolic budgets: a
// witness is evidence, and a body chasing the fixed memory's small
// elements around a cycle (a unique table's chain) would otherwise run
// the whole unrolling budget on each of its hundreds of inputs.
const (
	witnessLoopBudget = 256
	witnessStepBudget = 1 << 13
)

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
				if handled, reason, ok := lo.lowerUnitCall(s.Expression); handled {
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
	if name, contract, isSpan := lo.spanAssignment(s); isSpan {
		return lo.assignSpanElement(name, contract, s)
	}
	if handled, reason, ok := lo.assignRecordSpanField(s); handled {
		return reason, ok
	}
	if index := s.Target; index != nil && !index.Dot {
		if view, isView := lo.viewOf(index.Left); isView {
			// A view's element takes the value in its owner (asm/agg_views.go).
			owner, reason, ok := lo.viewOwner(view)
			if !ok {
				return reason, false
			}
			idx, reason, ok := lo.lower(index.Index, 32)
			if !ok {
				return reason, false
			}
			return lo.assignUnderIndexTerm(owner, viewIndex(view, idx), view.length, s.Value)
		}
	}
	if index := s.Target; index != nil && !index.Dot {
		if _, isConst := lo.constantIndexValue(index.Index); !isConst {
			base, reason, ok := lo.placeOf(index.Left)
			if !ok {
				return reason, false
			}
			if base.typ.kind != oakArray {
				return fmt.Sprintf("an index into %s (not an array)", index.Left.String()), false
			}
			return lo.assignUnderIndex(base, index.Index, s.Value)
		}
	}
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
		if iteration > loopBudget || (lo.concrete != nil && iteration > witnessLoopBudget) {
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
		if iteration == 0 && lo.concrete == nil && lo.summarizeCounted(loop) {
			// A counted loop over a loop, past the unrolling limit:
			// summarized rather than unrolled, as the machine side
			// summarizes it (the counted loop's exception in the
			// executor's branch handling).
			return lo.loopEvent(loop)
		}
		if reason, ok := lo.lowerLoopBody(loop.Body); !ok {
			return reason, false
		}
	}
}

// countedUnrollLimit is the trip count from which a counted loop over a
// loop is summarized rather than unrolled: below it the unrolled copies
// are few and each summarizes the inner loop on its own path (a
// two-sided body whose sides read different lengths keeps two inner
// events on the machine side where the Oak side merges them into one
// before the loop); above it the copies exceed the event budget.
const countedUnrollLimit = 4

// countedTripLimit is the trip count from which any counted loop is
// summarized rather than unrolled, loop inside or not: a loop clearing
// or copying a table of two thousand words unrolls into a write log the
// decision cannot afford (and, guarded at every iteration, meets the
// path budget first), where its induction is a few steps. Sixty-four:
// above it the unrolled copies cost more than the induction (the
// interpreter's `step_binding` took five minutes unrolled, under a
// second inducted), and only a few loops of 128 and 512 trips prove
// unrolled where their coupling does not yet.
const countedTripLimit = 64

// summarizeCounted decides, at a counted loop's entry, whether the loop
// is summarized: its body holds a loop (bodyHasLoop) and its trip count —
// the bound of `i < c` or `i <= c` less the counter's value, both
// constant here — is past countedUnrollLimit. A condition of another
// shape unrolls as before.
func (lo *oakLowering) summarizeCounted(loop *ast.WhileStatement) bool {
	infix, isInfix := loop.Condition.(*ast.InfixExpression)
	if !isInfix || (infix.Operator != "<" && infix.Operator != "<=") {
		return false
	}
	left, _, okL := lo.lower(infix.Left, 32)
	right, _, okR := lo.lower(infix.Right, 32)
	if !okL || !okR || left.kind != termConst || right.kind != termConst || right.value < left.value {
		return false
	}
	trips := right.value - left.value
	if infix.Operator == "<=" {
		trips++
	}
	if lo.trapsTracked {
		// The theorem decider has no machine side to couple with: a
		// summarized loop is a law left open (the lattice laws' loops over
		// loops, `dnf_product_denotes`), so it unrolls every counted loop.
		return false
	}
	return trips > countedTripLimit || (trips > countedUnrollLimit && bodyHasLoop(loop.Body, lo.functions))
}

// summarizeCounted is the machine side's reading of the same decision at
// the decided exit branch of a recognized loop: the body holds a loop
// (loopsInside) and the flags compare the counter with its bound, both
// constant, the exit taken at or above the bound.
func (x *pathExecutor) summarizeCounted(shape loopShape, exit Instruction, state *symbolicState) bool {
	var left, right *term
	var atOrAbove bool
	switch exit.Mnemonic {
	case "b.":
		if state.flags == nil || state.flags.kind != "" || state.flags.cond != nil || state.flags.float {
			return false
		}
		left, right = state.flags.left, state.flags.right
		switch exit.Cond {
		case "hs", "cs", "ge":
			atOrAbove = true
		case "hi", "gt":
		default:
			return false
		}
	case "bgeu", "bge", "bltu", "blt":
		// RV64: `bgeu counter, bound, exit`; `bltu bound, counter, exit`.
		if len(exit.Operands) < 2 {
			return false
		}
		a, okA := exit.Operands[0].(Register)
		b, okB := exit.Operands[1].(Register)
		if !okA || !okB {
			return false
		}
		va, boundA := state.read(a)
		vb, boundB := state.read(b)
		if !boundA || !boundB {
			return false
		}
		if exit.Mnemonic == "bgeu" || exit.Mnemonic == "bge" {
			left, right, atOrAbove = va, vb, true
		} else {
			left, right = vb, va
		}
	default:
		return false
	}
	if left == nil || right == nil || left.kind != termConst || right.kind != termConst || right.value < left.value {
		return false
	}
	trips := right.value - left.value
	if !atOrAbove {
		trips++
	}
	return trips > countedTripLimit || (trips > countedUnrollLimit && x.loopsInside(shape))
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
				if reason, isAssert, ok := lo.lowerAssert(s.Expression); isAssert {
					// A failed assert traps; the machine side's trap arm
					// leaves its body path (runBody), so the iteration is
					// compared on the inputs where the assert holds.
					if !ok {
						return reason, false
					}
					continue
				}
				if handled, reason, ok := lo.lowerUnitCall(s.Expression); handled {
					if !ok {
						return reason, false
					}
					continue
				}
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
		// `cond ? { ... }` with no false arm: the false path is empty.
		if single, _, ok := statementConditional(match); ok {
			whenTrue, whenFalse, isBool = single, nil, true
		}
	}
	if !isBool {
		return lo.lowerMatchStatement(match)
	}
	cond, reason, ok := lo.lowerCondition(match.Scrutinee)
	if !ok {
		return reason, false
	}
	if lo.concrete != nil && cond.kind == termConst {
		// Decided on a witness input: only the arm taken runs — the
		// other's traps and reads are not on this path, and lowering it
		// would only cost (an unrolled callee). A symbolic run keeps both
		// arms even under a folded condition: pruning there lets bodies
		// past their refusals into decisions no budget affords yet.
		if cond.value&1 == 1 {
			return lo.lowerArm(whenTrue)
		}
		return lo.lowerArm(whenFalse)
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

// statementConditional recognizes a Bool conditional with a true arm and an
// optional false arm (`cond ? a` leaves it nil), the statement forms the
// parser's sugar produces; boolConditional needs both arms.
func statementConditional(match *ast.MatchExpression) (whenTrue, whenFalse ast.Expression, ok bool) {
	if match.Scrutinee == nil || len(match.Arms) == 0 || len(match.Arms) > 2 {
		return nil, nil, false
	}
	for i, arm := range match.Arms {
		switch pattern := arm.Pattern.(type) {
		case *ast.LiteralPattern:
			lit, isBool := pattern.Value.(*ast.Boolean)
			if !isBool {
				return nil, nil, false
			}
			if lit.Value {
				whenTrue = arm.Body
			} else {
				whenFalse = arm.Body
			}
		case *ast.WildcardPattern:
			if i != 1 {
				return nil, nil, false
			}
			whenFalse = arm.Body
		default:
			return nil, nil, false
		}
	}
	return whenTrue, whenFalse, whenTrue != nil
}

// lowerArm executes a conditional arm as statements: a block of
// assignments (possibly empty), nothing, or a chained conditional
// (`c1 ? { … } | c2 ? { … } | { … }`).
func (lo *oakLowering) lowerArm(arm ast.Expression) (string, bool) {
	if arm == nil {
		return "", true
	}
	if chained, isMatch := arm.(*ast.MatchExpression); isMatch {
		return lo.lowerConditionalStatement(chained)
	}
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
	float     bool // f32/f64 elements: an element read is a float of elemWidth
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
	return spanElemName(lo.spanRoot(ident.Value), k), contract, true
}

// spanRoot is the caller's span an inlined callee's span parameter
// stands for, or the name itself.
func (lo *oakLowering) spanRoot(name string) string {
	if root, aliased := lo.spanAlias[name]; aliased {
		return root
	}
	return name
}

// spanElementTerm lowers v[e] over a span parameter with any index
// expression: a constant index is the element parameter, a symbolic one a
// select (the loop-carried counter of a data-dependent loop).
func (lo *oakLowering) spanElementTerm(index *ast.IndexExpression) (*term, spanContract, string, bool) {
	if name, contract, isConst := lo.spanElement(index); isConst && lo.spanOffset[index.Left.(*ast.Identifier).Value] == nil {
		span := lo.spanRoot(index.Left.(*ast.Identifier).Value)
		_, k, _ := elementParam(name)
		entry := paramTerm(name, contract.elemWidth)
		if lo.concrete != nil {
			entry = constTerm(elementValue(span, k, contract.elemWidth), contract.elemWidth)
			// Past the length, Oak traps on this input (a witness run
			// notes it; the value stands in for nothing).
			lo.addTrap(cmpTerm("hs", constTerm(k, 32), lo.witnessBound(index.Left.(*ast.Identifier).Value)))
			if lo.witnessTrapped {
				return nil, contract, fmt.Sprintf("an index past len(%s) on this input", span), false
			}
		}
		return memoryAt(lo.writes[span], constTerm(k, 32), entry), contract, "", true
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
	if lo.concrete != nil {
		// Past the span's own length (a derived span's, when derived):
		// Oak traps on this input, which the witness run notes (addTrap)
		// under the path; the value then stands in for nothing.
		lo.addTrap(cmpTerm("hs", idx, lo.witnessBound(ident.Value)))
		if lo.witnessTrapped {
			return nil, spanContract{}, fmt.Sprintf("an index past len(%s) on this input", ident.Value), false
		}
	}
	idx = lo.spanIndex(ident.Value, idx) // a derived span: start + i in the root
	span := lo.spanRoot(ident.Value)
	if lo.concrete != nil && idx.kind == termConst {
		return memoryAt(lo.writes[span], idx, constTerm(elementValue(span, idx.value, contract.elemWidth), contract.elemWidth)), contract, "", true
	}
	entry := selectTerm(span, idx, contract.elemWidth)
	if !lo.trapsTracked {
		// The asm verifier's side: reads split over a conditional in the
		// index, as the machine's branches read (selectSplit). The theorem
		// decider keeps the read whole, as its Oak twin builds it.
		entry = selectSplit(span, idx, contract.elemWidth, 0)
	}
	return memoryAt(lo.writes[span], idx, entry), contract, "", true
}

// selectSplit builds a span read at an index holding a conditional by
// splitting the read over the conditional: v[x + (c ? a : b)] is
// c ? v[x + a] : v[x + b]. The native backend lowers a value-position
// conditional as branches, so the machine reads at each branch's own
// index; the split gives the Oak side the same reads — the same canonical
// index bits share one abstraction in the blaster — where one read at a
// conditional index would stand apart from both and leave the equality to
// the consistency constraint. Bounded in depth against a chain of
// conditionals.
func selectSplit(span string, index *term, width int, depth int) *term {
	if depth < 3 {
		if c, a, b, ok := hoistIte(index); ok {
			return iteTerm(c, selectSplit(span, a, width, depth+1), selectSplit(span, b, width, depth+1))
		}
	}
	return selectTerm(span, index, width)
}

// hoistIte rewrites a term whose top is a conditional, or a binary
// operation over a conditional operand, into the conditional over the
// operation applied to each branch.
func hoistIte(t *term) (cond, left, right *term, ok bool) {
	switch t.kind {
	case termIte:
		return t.cond, t.left, t.right, true
	case termBinary:
		if c, a, b, ok := hoistIte(t.right); ok {
			return c, binaryTerm(t.op, t.left, a), binaryTerm(t.op, t.left, b), true
		}
		if c, a, b, ok := hoistIte(t.left); ok {
			return c, binaryTerm(t.op, a, t.right), binaryTerm(t.op, b, t.right), true
		}
	}
	return nil, nil, nil, false
}

// constantIndexValue reads a constant index: a literal, a primitive
// constructor over one, or a local whose value has folded to a constant
// (the counter of an unrolled loop).
func (lo *oakLowering) constantIndexValue(expr ast.Expression) (int64, bool) {
	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		return e.Value, true
	case *ast.InfixExpression:
		// A sum, product, or difference of two literals converted to one
		// unsigned type (`u32(0) + u32(3)`, an inlined helper's constant
		// offsets; `u32(32) - u32(7)`, an inlined rotate's count) folds
		// when the result fits the type, as the extents checker folds it;
		// a wrapping `u8(200) + u8(100)` or `u32(1) - u32(2)` is lowered
		// as the operation.
		if e.Operator != "+" && e.Operator != "*" && e.Operator != "-" {
			return 0, false
		}
		typeName := ""
		for _, side := range []ast.Expression{e.Left, e.Right} {
			call, isCall := side.(*ast.InvocationExpression)
			if !isCall || len(call.Arguments) != 1 {
				return 0, false
			}
			conv, isIdent := call.Function.(*ast.Identifier)
			if !isIdent || (typeName != "" && conv.Value != typeName) {
				return 0, false
			}
			typeName = conv.Value
		}
		width := map[string]int{"u8": 8, "u16": 16, "u32": 32, "u64": 64}[typeName]
		if width == 0 {
			return 0, false
		}
		left, leftConst := lo.constantIndexValue(e.Left)
		right, rightConst := lo.constantIndexValue(e.Right)
		if !leftConst || !rightConst || left < 0 || right < 0 {
			return 0, false
		}
		var value uint64
		switch e.Operator {
		case "+":
			value = uint64(left) + uint64(right)
		case "-":
			if left < right {
				return 0, false
			}
			value = uint64(left - right)
		default:
			if right != 0 && uint64(left) > ^uint64(0)/uint64(right) {
				return 0, false
			}
			value = uint64(left) * uint64(right)
		}
		if width < 64 && value >= uint64(1)<<uint(width) || value >= 1<<32 {
			return 0, false
		}
		return int64(value), true
	case *ast.Identifier:
		if local, isLocal := lo.locals[e.Value]; isLocal && local.value.kind == termConst {
			return int64(local.value.value), true
		}
		if _, isLocal := lo.locals[e.Value]; !isLocal {
			if _, isParam := lo.params[e.Value]; !isParam {
				if value, w, ok := lo.constantValue(e.Value, 64); ok && w <= 64 {
					return int64(value), true
				}
			}
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
	calleeSpans := map[string]spanContract{}
	calleeRecordSpans := map[string]recordSpanArg{}
	calleeAlias := map[string]string{}
	calleeOffset := map[string]*term{}
	calleeLen := map[string]*term{}
	// The program's constant tables are in scope for the callee as they
	// are for the caller (`sum_view(view(&TABLE))` inside a callee).
	for table := range lo.tableLens {
		if contract, isSpan := lo.spans[table]; isSpan {
			calleeSpans[table] = contract
		}
	}
	calleeViews := map[string]aggView{}
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
			if recordArg, isRecordSpan := lo.recordSpans[owner]; !isLocal && isRecordSpan {
				// A span of records passed on: the callee's parameter is an
				// alias of the caller's, sharing its leaf memories.
				calleeRecordSpans[param.Name.Value] = recordArg
				calleeAlias[param.Name.Value] = lo.spanRoot(owner)
				continue
			}
			if contract, isSpanParam := lo.spans[owner]; !isLocal && isSpanParam {
				// A span parameter passed on: the callee's parameter is an
				// alias of the caller's span, sharing its memory
				// (asm/effects.go) — with the caller's own offset and
				// length when the caller's parameter is a derived span.
				elem, _, _ := spanShape(param.Type)
				if int(elem)*8 != contract.elemWidth {
					return nil, fmt.Sprintf("a call to %s: the span argument %s has %d-bit elements where %d-bit ones are expected", name, owner, contract.elemWidth, elem*8), false
				}
				calleeSpans[param.Name.Value] = contract
				calleeAlias[param.Name.Value] = lo.spanRoot(owner)
				if offset, derived := lo.spanOffset[owner]; derived {
					calleeOffset[param.Name.Value] = offset
				}
				if length, derived := lo.spanLen[owner]; derived {
					calleeLen[param.Name.Value] = length
				}
				continue
			}
			if sub, isSub := subsliceOf(arg); isSub && !lo.aggregateChain(&ast.Identifier{Value: sub.span}) {
				// `subslice(w, start, n)` of a span parameter: an alias of
				// the root at the offset start (plus w's own), of length n
				// (asm/derived_spans.go); the C helper's check is a trap
				// obligation. (Over an aggregate or a view: below.)
				contract, isSpanParam := lo.spans[sub.span]
				if _, isLocal := lo.locals[sub.span]; isLocal || !isSpanParam {
					return nil, fmt.Sprintf("a call to %s: subslice of %s, which is not a span parameter", name, sub.span), false
				}
				elem, _, _ := spanShape(param.Type)
				if int(elem)*8 != contract.elemWidth {
					return nil, fmt.Sprintf("a call to %s: the span argument %s has %d-bit elements where %d-bit ones are expected", name, sub.span, contract.elemWidth, elem*8), false
				}
				start, reason, ok := lo.lower(sub.start, 32)
				if !ok {
					return nil, reason, false
				}
				count, reason, ok := lo.lower(sub.count, 32)
				if !ok {
					return nil, reason, false
				}
				length := lo.spanLenTerm(sub.span, 32)
				lo.addTrap(cmpTerm("hi", start, length))
				lo.addTrap(cmpTerm("hi", count, binaryTerm("sub", length, start)))
				calleeSpans[param.Name.Value] = contract
				calleeAlias[param.Name.Value] = lo.spanRoot(sub.span)
				calleeOffset[param.Name.Value] = lo.spanIndex(sub.span, start)
				calleeLen[param.Name.Value] = count
				continue
			}
			if view, isView := lo.viewOf(arg); isView {
				// A view passed on: the callee's parameter is the same view
				// over a copy of the owner, written back on return
				// (asm/agg_views.go).
				ownerAgg, reason, ok := lo.viewOwner(view)
				if !ok {
					return nil, reason, false
				}
				hidden := "view#" + view.owner
				bound[hidden] = &oakLocal{agg: ownerAgg.copy()}
				calleeViews[param.Name.Value] = aggView{owner: hidden, offset: view.offset, length: view.length}
				if isWritableSpan(param.Type) {
					borrows = append(borrows, borrow{param: hidden, owner: ownerAgg})
				}
				continue
			}
			if sub, isSub := subsliceOf(arg); isSub {
				if view, ownerAgg, reason, ok := lo.subsliceView(sub); ok {
					hidden := "view#" + view.owner
					bound[hidden] = &oakLocal{agg: ownerAgg.copy()}
					calleeViews[param.Name.Value] = aggView{owner: hidden, offset: view.offset, length: view.length}
					if isWritableSpan(param.Type) {
						borrows = append(borrows, borrow{param: hidden, owner: ownerAgg})
					}
					continue
				} else if reason != "" {
					return nil, fmt.Sprintf("a call to %s: %s", name, reason), false
				}
			}
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
	// The caller's package-global cells are the callee's too — the same
	// locals, so the callee's assignments are the caller's final values —
	// unless a parameter of the callee shadows the name.
	for cellName, cell := range lo.cells {
		if _, shadowed := bound[cellName]; !shadowed {
			bound[cellName] = cell
		}
	}
	saved := lo.locals
	savedFloats := lo.floats
	savedSpans, savedAlias := lo.spans, lo.spanAlias
	savedOffset, savedLen := lo.spanOffset, lo.spanLen
	savedViews := lo.views
	savedRecordSpans := lo.recordSpans
	lo.locals = bound
	lo.floats = calleeFloats
	// The callee sees only its own span parameters, each spelled in the
	// caller's names through the alias.
	lo.spans, lo.spanAlias = calleeSpans, calleeAlias
	lo.spanOffset, lo.spanLen = calleeOffset, calleeLen
	lo.views = calleeViews
	lo.recordSpans = calleeRecordSpans
	if lo.inlining == nil {
		lo.inlining = map[string]bool{}
	}
	lo.inlining[name] = true
	return func() {
		lo.floats = savedFloats
		lo.spans, lo.spanAlias = savedSpans, savedAlias
		lo.spanOffset, lo.spanLen = savedOffset, savedLen
		lo.views = savedViews
		lo.recordSpans = savedRecordSpans
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

// declareTables makes the program's constant tables readable as spans:
// T[k] is the element term the asm side's load through `adrl`/`la` gives,
// len(T) the constant element count.
func (lo *oakLowering) declareTables(tables map[string]Table) {
	for symbol, table := range tables {
		if table.Elem <= 0 {
			continue
		}
		name := TableName(symbol)
		if _, isSpan := lo.spans[name]; isSpan {
			continue // a parameter shadows the table
		}
		lo.spans[name] = spanContract{elemWidth: int(table.Elem) * 8, signed: table.Signed}
		if lo.tableLens == nil {
			lo.tableLens = map[string]int64{}
		}
		lo.tableLens[name] = table.Size / table.Elem
	}
}

// tableLength recognizes len(T) over a constant table, or over a callee's
// span parameter aliased to one (`sum_view(view(&TABLE))`): the element
// count.
func (lo *oakLowering) tableLength(expr ast.Expression) (int64, bool) {
	call, isCall := expr.(*ast.InvocationExpression)
	if !isCall || len(call.Arguments) != 1 {
		return 0, false
	}
	fn, isIdent := call.Function.(*ast.Identifier)
	arg, argIsIdent := call.Arguments[0].(*ast.Identifier)
	if !isIdent || !argIsIdent || fn.Value != "len" {
		return 0, false
	}
	length, isTable := lo.tableLens[lo.spanRoot(arg.Value)]
	return length, isTable
}

// isTableLength reports a constant term that is a table's element count:
// the length a caller passes beside the table's address (`adrl xB, T; movz
// wL, #N`), so `view(&T)` handed to a callee is the table passed whole.
func (x *pathExecutor) isTableLength(length *term, owner string) bool {
	if length.kind != termConst || x.fn == nil {
		return false
	}
	for symbol, table := range x.fn.Tables {
		if TableName(symbol) == owner && table.Elem > 0 {
			return int64(length.value&mask(32)) == table.Size/table.Elem
		}
	}
	return false
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
		if _, isRecord := lo.recordSpans[arg.Value]; !isRecord {
			return "", false
		}
	}
	return spanLenName(lo.spanRoot(arg.Value)), true
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
		if value, _, ok := lo.constantValue(e.Value, width); ok {
			return constTerm(value, width), "", true
		}
		if global, isGlobal := lo.globals[e.Value]; isGlobal {
			return adaptWidth(cellEntry(e.Value, global), width), "", true
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
		if t, _, handled, reason, ok := lo.recordSpanField(e); handled {
			if !ok {
				return nil, reason, false
			}
			return adaptWidth(t, width), "", true
		}
		if lo.aggregateChain(e) {
			// A scalar leaf of an aggregate: a field, an element, or a field
			// of a call's or a literal's value.
			leaf, reason, ok := lo.readPlace(e)
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
		if member, isSimd := simdMember(e.Function); isSimd {
			// The scalar-valued vector operations (asm/verify_simd.go).
			return lo.simdScalar(member, e, width)
		}
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
		if ident, isIdent := e.Function.(*ast.Identifier); isIdent && ident.Value == "len" && len(e.Arguments) == 1 {
			if view, isView := lo.viewOf(e.Arguments[0]); isView {
				return adaptWidth(view.length, width), "", true // a view's length (asm/agg_views.go)
			}
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
		if length, isTable := lo.tableLength(e); isTable {
			return constTerm(uint64(length), width), "", true
		}
		if name, isLen := lo.spanLength(e); isLen {
			if arg := e.Arguments[0].(*ast.Identifier).Value; lo.spanLen[arg] != nil {
				return lo.spanLenTerm(arg, width), "", true // a derived span's count
			}
			if value, isConcrete := lo.concrete[name]; isConcrete {
				return constTerm(value, width), "", true
			}
			return zeroExtend(truncate(paramTerm(name, 32), width), width), "", true
		}
		// An atomic is a read of the cell its storage path names and a
		// write into its span's log (docs/spec/65-machine-memory.md
		// section 7a, asm/atomics.go): the order is the checker's concern,
		// the values the terms'.
		if ident, isIdent := e.Function.(*ast.Identifier); isIdent {
			if spec, isAtomic := semir.LookupAtomicBuiltin(ident.Value); isAtomic {
				if !spec.ReturnsValue() {
					return nil, "the atomic " + ident.Value + " in value position", false
				}
				return lo.lowerAtomic(spec, e, width)
			}
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
			// The integer constructor over a float is the conversion toward
			// zero (asm/floats_lowering.go); the `_bits_` forms below stay
			// bit moves.
			if len(e.Arguments) == 1 {
				if _, srcFloat := lo.floatWidthOf(e.Arguments[0]); srcFloat {
					return lo.floatConversion(target, e.Arguments[0], width)
				}
			}
		case "f32", "f64":
			if len(e.Arguments) == 1 {
				return lo.floatConversion(ident.Value, e.Arguments[0], width)
			}
		default:
			if t, op, src, isConv := typechecker.ConversionParts(ident.Value); isConv {
				floatSource := src == "f32" || src == "f64"
				floatTarget := t == "f32" || t == "f64"
				switch {
				case floatSource && op == "bits":
					target = t // a bit move, below
				case (floatSource || floatTarget) && (op == "trunc" || op == "round" || op == "saturating") && len(e.Arguments) == 1:
					// A float converted toward zero (trunc: the backend traps
					// out of range, so the value on the non-trapping paths is
					// the conversion's; saturating: it saturates, as fcvtz*
					// does), or a float rounded to another width (round).
					return lo.floatConversion(t, e.Arguments[0], width)
				case op == "trunc" || op == "bits":
					target = t
				}
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
		if w, isFloat := lo.floatWidthOf(e.Left); isFloat || func() bool { w, isFloat = lo.floatWidthOf(e.Right); return isFloat }() {
			// Floating-point arithmetic: the IEEE operation at the operands'
			// width as an uninterpreted term (asm/floats_ops.go); the
			// backends never contract, so `a * b + c` is two operations.
			if w == 0 {
				if other, ok := lo.floatWidthOf(e.Right); ok && other != 0 {
					w = other
				} else {
					w = width
				}
			}
			op, known := map[string]string{"+": "fadd", "-": "fsub", "*": "fmul", "/": "fdiv"}[e.Operator]
			if !known {
				return nil, fmt.Sprintf("floating-point %s", e.Operator), false
			}
			left, reason, okL := lo.lower(e.Left, w)
			if !okL {
				return nil, reason, false
			}
			right, reason, okR := lo.lower(e.Right, w)
			if !okR {
				return nil, reason, false
			}
			return adaptWidth(floatTerm(op, w, left, right), width), "", true
		}
		if e.Operator == "/" || e.Operator == "%" {
			// Unsigned division and remainder by a constant power of two
			// are a shift and a mask. Any other divisor: the quotient is
			// the uninterpreted operation udiv/sdiv of the operands at
			// their width (asm/floats_ops.go) and the remainder is
			// a - (a / b) * b, the machines' definition (Oak.IntegerDivision;
			// the AArch64 lowering's msub, RISC-V's rem); a zero divisor
			// traps, which the theorem decider states as an obligation and
			// the asm verifier meets in the lowering's guard.
			w, signed, isScalar := lo.operandContract(e)
			if !isScalar {
				return nil, fmt.Sprintf("operator %s over operands without a contract", e.Operator), false
			}
			if w == 0 {
				w = width
			}
			right, reason, okR := lo.lower(e.Right, w)
			if !okR {
				return nil, reason, false
			}
			left, reason, okL := lo.lower(e.Left, w)
			if !okL {
				return nil, reason, false
			}
			if !signed && right.kind == termConst && right.value != 0 && right.value&(right.value-1) == 0 {
				if e.Operator == "%" {
					return adaptWidth(binaryTerm("and", left, constTerm(right.value-1, w)), width), "", true
				}
				return adaptWidth(binaryTerm("shr", left, constTerm(uint64(bits.TrailingZeros64(right.value)), w)), width), "", true
			}
			if lo.trapsTracked {
				lo.addTrap(cmpTerm("eq", right, constTerm(0, w)))
			}
			if lo.concrete != nil {
				// A witness run: a zero divisor is Oak trapping on this
				// input (on this path), and the run stops there.
				lo.addTrap(cmpTerm("eq", right, constTerm(0, w)))
				if lo.witnessTrapped {
					return nil, "a zero divisor on this input", false
				}
			}
			op := "udiv"
			if signed {
				op = "sdiv"
			}
			if lo.arch == ArchRV64 {
				op = "rv." + op
			}
			quotient := floatTerm(op, w, left, right)
			if e.Operator == "%" {
				return extendTerm(binaryTerm("sub", left, binaryTerm("mul", quotient, right)), w, width, signed), "", true
			}
			return extendTerm(quotient, w, width, signed), "", true
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
			if lo.trapsTracked {
				lo.addTrap(cmpTerm("hs", right, constTerm(uint64(width), width)))
				return binaryTerm(op, left, right), "", true
			}
			if lo.maxValue(right) < uint64(width) {
				// A count whose range stays below the width never traps,
				// so Oak's shift is the machine's (asm/range.go).
				return binaryTerm(op, left, right), "", true
			}
			return lo.lowerVariableShift(e, op, left, right, width)
		}
		if (op == "shl" || op == "shr") && right.kind == termConst && right.value >= uint64(width) && lo.concrete != nil {
			// Oak traps at the width: on a witness input the constant
			// count says so if the path is live; a dead arm's count (the
			// other arm's arithmetic, `(k - 8) * 8` under `k < 8`) traps
			// nothing, and its value is discarded by the merge. A
			// symbolic run keeps the machine's wrapped shift: the
			// machine's guard traps there too, which the witness inputs
			// check (machineTrapsWhereOakYields).
			lo.addTrap(constTerm(1, 1))
			if lo.witnessTrapped {
				return nil, "a shift count reaching the width on this input", false
			}
		}
		return binaryTerm(op, left, right), "", true
	case *ast.BlockExpression:
		return lo.lowerBlock(e.Block, width)
	case *ast.QuantifierExpression:
		t, reason, ok := lo.lowerQuantifier(e)
		if !ok {
			return nil, reason, false
		}
		return zeroExtend(t, width), "", true
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
		if lo.concrete != nil && cond.kind == termConst {
			// Decided on a witness input: the arm taken alone.
			if cond.value&1 == 1 {
				return lo.lower(whenTrue, width)
			}
			return lo.lower(whenFalse, width)
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

// lowerQuantifier lowers `forall (x: T) { body }` / `exists (x: T) { body }`
// (docs/spec/10-syntax.md section 3e): each binder is a fresh parameter
// of its scalar width (`x@qN`; Bool 1, u8/i8 8, u16/i16 16), the body is
// lowered to its bit with the binders as locals, and the result is the
// quantifier term over the innermost binder outward. A binder over a sum
// type is left to the enumeration rung (the tag would need its domain
// hypothesis inside the elimination). A trap the body may take under some
// value of a binder is the quantifier's trap: the obligation is decided
// over the binder as a free leaf.
func (lo *oakLowering) lowerQuantifier(expr *ast.QuantifierExpression) (*term, string, bool) {
	if expr.Body == nil || expr.Body.Block == nil {
		return nil, "a quantifier without a body", false
	}
	if lo.locals == nil {
		lo.locals = map[string]*oakLocal{}
	}
	type bound struct {
		name  string
		fresh string
		width int
		param *term
		prev  *oakLocal
		had   bool
	}
	binders := make([]bound, 0, len(expr.Binders))
	restore := func() {
		for i := len(binders) - 1; i >= 0; i-- {
			b := binders[i]
			if b.had {
				lo.locals[b.name] = b.prev
			} else {
				delete(lo.locals, b.name)
			}
		}
	}
	for _, binder := range expr.Binders {
		width, signed, isScalar := contractBits(binder.Type)
		if typeText(binder.Type) == "Bool" {
			width, signed, isScalar = 1, false, true
		}
		if !isScalar || width > 16 {
			restore()
			return nil, fmt.Sprintf("a quantifier over %s (the bit level takes Bool and the 8- and 16-bit integers)", typeText(binder.Type)), false
		}
		lo.quantifiers++
		fresh := fmt.Sprintf("%s@q%d", binder.Name.Value, lo.quantifiers)
		lo.params[fresh] = width
		lo.signed[fresh] = signed
		prev, had := lo.locals[binder.Name.Value]
		param := paramTerm(fresh, width)
		lo.locals[binder.Name.Value] = &oakLocal{value: param, width: width, signed: signed}
		binders = append(binders, bound{name: binder.Name.Value, fresh: fresh, width: width, param: param, prev: prev, had: had})
	}
	body, reason, ok := lo.lowerBlock(expr.Body.Block, 1)
	restore()
	if !ok {
		return nil, reason, false
	}
	op := "exists"
	if expr.Universal {
		op = "forall"
	}
	t := truncate(body, 1)
	for i := len(binders) - 1; i >= 0; i-- {
		t = quantTerm(op, binders[i].fresh, binders[i].width, t, binders[i].param)
	}
	return t, "", true
}

// lowerCondition lowers a Bool condition — a comparison, or comparisons
// joined by && and || — to a 0/1 term. Oak's && and || short-circuit, but
// over pure comparisons of parameters evaluation order is unobservable, so
// the strict and/or is the same function.
func (lo *oakLowering) lowerCondition(expr ast.Expression) (*term, string, bool) {
	infix, isInfix := expr.(*ast.InfixExpression)
	if !isInfix {
		// A literal condition (`true ? { … }`, a scope idiom): its bit.
		if lit, isLit := expr.(*ast.Boolean); isLit {
			if lit.Value {
				return constTerm(1, 1), "", true
			}
			return constTerm(0, 1), "", true
		}
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

// constantValue reads a constant global's value at width: the bit pattern
// at its declared width, sign-extended when the type is signed and width is
// wider, masked when narrower — the value the native backend materialized
// (nativegen's constant). Reports the declared width beside the value.
func (lo *oakLowering) constantValue(name string, width int) (uint64, int, bool) {
	c, isConst := lo.constants[name]
	if !isConst {
		return 0, 0, false
	}
	cw, signed, ok := contractBits(&ast.Identifier{Value: c.Type})
	if !ok {
		return 0, 0, false
	}
	value := c.Value & mask(cw)
	if signed && width > cw && (value>>uint(cw-1))&1 == 1 {
		value |= ^mask(cw)
	}
	return value & mask(width), cw, true
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
		if c, isConst := lo.constants[e.Value]; isConst {
			if w, signed, ok := contractBits(&ast.Identifier{Value: c.Type}); ok {
				return w, signed, true
			}
		}
	case *ast.IndexExpression:
		if lo.aggregateChain(e) {
			if leaf, _, ok := lo.readPlace(e); ok && leaf.typ.kind == oakScalar {
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
	case *ast.PrefixExpression:
		// `!x` is Bool; `-x` and `^x` have their operand's contract, so
		// `f64_round_i64(-n)` converts a signed 64-bit source.
		if e.Operator == "!" {
			return 1, false, true
		}
		return lo.operandContract(e.Right)
	case *ast.InvocationExpression:
		if _, isLen := lo.spanLength(e); isLen {
			return 32, false, true
		}
		if member, isSimd := simdMember(e.Function); isSimd {
			// Bool for any/all, u32 for movemask, the mask helpers' width; a
			// vector-valued operation has no scalar contract.
			if w, isScalar := simdScalarWidth(member); isScalar {
				return w, false, true
			}
			return 0, false, false
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
		if w == 32 || w == 64 {
			// A parameter of a float's width may be one: ordinary values,
			// signed zeros, an infinity, and a NaN beside the patterns.
			values = append(values, floatWitnessValues(w)...)
		}
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

// Verify checks one asm function against its Oak fallback body. A record
// result of two register chunks (9 to 16 bytes) is verified chunk by
// chunk — x0 then x1 (a0 then a1) — each run of the paths delivering one
// chunk against the same chunk packed from the Oak body's value; the
// verdict is proof only when both are proven, otherwise the first that
// is not.
func Verify(fn *Function, sig *ast.FunctionStatement, oakBody ast.Expression) Verdict {
	if only := os.Getenv("OAK_VERIFY_ONLY"); only != "" && only != fn.Name {
		// A diagnostic switch: one function verified, every other unit
		// trusted without a look (its verdict is never cached).
		return Verdict{Kind: VerdictTrusted, Message: "skipped under OAK_VERIFY_ONLY"}
	}
	if os.Getenv("OAK_VERIFY_TRACE") != "" {
		started := time.Now()
		defer func() {
			fmt.Fprintf(os.Stderr, "verify %s: %s\n", fn.Name, time.Since(started).Round(time.Millisecond))
		}()
	}
	if shape, isVector := vectorShape(sig.ReturnType); isVector {
		return verifyVectorResult(fn, sig, oakBody, shape)
	}
	if _, chunks, isComposite := resultComposite(fn, sig); isComposite && chunks >= 2 {
		// Each chunk of the record — two registers, or the words of the
		// result area beyond them — verified in its own run.
		first := verifyChunk(fn, sig, oakBody, 0)
		if first.Kind == VerdictMismatch || first.Kind == VerdictTrusted {
			return first
		}
		var second Verdict
		for k := 1; k < chunks; k++ {
			second = verifyChunk(fn, sig, oakBody, k)
			if second.Kind != VerdictProven {
				return second
			}
		}
		if first.Kind != VerdictProven {
			return first
		}
		if chunks == 2 {
			return Verdict{Kind: VerdictProven, Message: first.Message + " (both result chunks)"}
		}
		return Verdict{Kind: VerdictProven, Message: fmt.Sprintf("%s (all %d result chunks)", first.Message, chunks)}
	}
	return verifyChunk(fn, sig, oakBody, 0)
}

// machineTrapsWhereOakYields runs the machine on witness inputs and, on
// one where it traps, runs the Oak body's witness lowering: a run that
// yields a value without noting a trap of its own (a failed bounds check,
// a zero divisor, a shift count at the width, a failed assert — addTrap
// on a witness run) is the mismatch. Inputs on which the Oak run fails
// for any other reason (a construct outside the subset) say nothing.
// The machine runs concretely (a witness run of the executor, its loops
// unrolled on the input) rather than by evaluating the symbolic trap
// condition, whose loop symbols have no value on an input. Bounded: the
// machine's runs are cheap, the Oak run is not.
func machineTrapsWhereOakYields(fn *Function, sig *ast.FunctionStatement, oakBody ast.Expression, chunk int, hasResult bool) (map[string]uint64, bool) {
	evaluated, runs := 0, 0
	for _, env := range loopWitnessInputs(fn, sig) {
		if evaluated >= trapWitnessBudget || runs >= trapWitnessRuns {
			break
		}
		evaluated++
		asmValue, _, _, okA := executeBodyChunk(fn, sig, env, 0, chunk)
		if !okA || asmValue != trapPath {
			continue
		}
		concrete := prepareLowering(fn, sig, env)
		concrete.resultChunk = chunk
		if !concrete.inDomain(env) {
			continue
		}
		runs++
		if os.Getenv("OAK_VERIFY_TRACE") != "" {
			fmt.Fprintf(os.Stderr, "trap witness %s %s: the machine traps; running the Oak body\n", fn.Name, describeEnvSorted(env))
		}
		var okO bool
		var reasonO string
		if hasResult {
			_, _, reasonO, okO = concrete.resultTerm(fn, sig, oakBody)
		} else {
			reasonO, okO = concrete.lowerUnitBody(oakBody)
		}
		if os.Getenv("OAK_VERIFY_TRACE") != "" {
			fmt.Fprintf(os.Stderr, "trap witness %s %s: oak ok=%v %q trapped=%v\n", fn.Name, describeEnvSorted(env), okO, reasonO, concrete.witnessTrapped)
		}
		if okO && !concrete.witnessTrapped {
			return env, true
		}
	}
	return nil, false
}

// witnessBound is the length a witness run checks a span index against:
// a constant table's length, else the span's own length term (a derived
// span's over its start and count; a parameter's `len(v)`, which the
// witness environment binds).
func (lo *oakLowering) witnessBound(name string) *term {
	if length, isTable := lo.tableLens[name]; isTable {
		return constTerm(uint64(length), 32)
	}
	return lo.spanLenTerm(name, 32)
}

// trapWitnessBudget bounds the witness inputs the machine runs on,
// trapWitnessRuns the Oak witness runs among them, for a body without
// data-dependent loops (a body with them runs every witness input in
// verifyLoops, where the same check applies).
const (
	trapWitnessBudget = 48
	trapWitnessRuns   = 6
)

// describeEnvSorted is describeEnv over every name of env, sorted.
func describeEnvSorted(env map[string]uint64) string {
	names := make([]string, 0, len(env))
	for name := range env {
		names = append(names, name)
	}
	sort.Strings(names)
	return describeEnv(names, env)
}

// verifyChunk is Verify for one result chunk (0 for a scalar or a
// one-chunk record).
func verifyChunk(fn *Function, sig *ast.FunctionStatement, oakBody ast.Expression, chunk int) Verdict {
	asmTerm, exec, reason, ok := executeBodyChunk(fn, sig, nil, 0, chunk)
	if !ok {
		return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (%s) — trusted per docs/spec/94-assembler.md §5", fn.Name, reason)}
	}
	if asmTerm == trapPath {
		return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (every path traps) — trusted per docs/spec/94-assembler.md §5", fn.Name)}
	}
	lowering := prepareLowering(fn, sig, nil)
	lowering.resultChunk = chunk
	lowering.machineTrap = exec.trap
	if exec.notes != nil {
		lowering.shiftGuardMax = exec.notes.shiftGuardMax
	}
	for name, width := range exec.freshSyms {
		lowering.fresh[name] = width // a summarized call's unspecified result bits
	}
	// A tail-recursive body is the loop it compiles to (docs/spec/85-discipline.md).
	if loop, isTail := tailRecursionAsLoop(sig, oakBody); isTail {
		oakBody = loop
	}
	// The machine trapped on some inputs; those leave the domain on the
	// claim that Oak traps there too. Witness inputs check the claim: an
	// input on which the machine traps and the Oak body yields a value is
	// a mismatch (a speculated arm whose guard trapped, say), not an
	// exclusion. A body with data-dependent loops runs every witness
	// input in verifyLoops, where the same check applies.
	trapClaim := func() (Verdict, bool) {
		if exec.trap == nil || len(exec.loops) > 0 || len(lowering.loops) > 0 {
			return Verdict{}, false
		}
		if env, found := machineTrapsWhereOakYields(fn, sig, oakBody, chunk, exec.hasResult); found {
			return Verdict{Kind: VerdictMismatch, Message: fmt.Sprintf("asm unit %s disagrees with its Oak body at %s (fixed element contents): the machine traps where Oak yields a value", fn.Name, describeEnvSorted(env))}, true
		}
		return Verdict{}, false
	}
	if !exec.hasResult {
		// A unit function that writes package state: the cells are the
		// whole comparison.
		if reason, ok := lowering.lowerUnitBody(oakBody); !ok {
			return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (the Oak body contains %s) — trusted per docs/spec/94-assembler.md §5", fn.Name, reason)}
		}
		if len(exec.loops) > 0 || len(lowering.loops) > 0 {
			if len(exec.cells) > 0 || len(lowering.writtenCells()) > 0 {
				return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (package state written around a data-dependent loop) — trusted per docs/spec/94-assembler.md §5", fn.Name)}
			}
			// The span memories are the comparison, under the loop coupling.
			return verifyLoops(fn, sig, oakBody, exec, lowering, nil, nil, 0)
		}
		if verdict, refuted := trapClaim(); refuted {
			return verdict
		}
		return decideEffects(fn, lowering, exec, nil)
	}
	oakTerm, width, reason, ok := lowering.resultTerm(fn, sig, oakBody)
	if !ok {
		return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (the Oak body contains %s) — trusted per docs/spec/94-assembler.md §5", fn.Name, reason)}
	}
	asmTerm = maskResult(fn, sig, asmTerm, chunk)
	if name := typeText(sig.ReturnType); name == "f32" || name == "f64" {
		// A float result is decided up to its NaN payload (floatCanonicalNaN).
		asmTerm = floatCanonicalNaN(truncate(asmTerm, width), width)
		oakTerm = floatCanonicalNaN(truncate(oakTerm, width), width)
	}
	if len(exec.loops) > 0 || len(lowering.loops) > 0 {
		if len(exec.cells) > 0 || len(lowering.writtenCells()) > 0 {
			return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (package state written around a data-dependent loop) — trusted per docs/spec/94-assembler.md §5", fn.Name)}
		}
		verdict := verifyLoops(fn, sig, oakBody, exec, lowering, asmTerm, oakTerm, width)
		verdict.Callees = exec.summarized
		return verdict
	}
	if verdict, refuted := trapClaim(); refuted {
		return verdict
	}
	note := ""
	if len(exec.summarized) > 0 {
		note = " (callees taken at their Oak bodies: " + strings.Join(exec.summarized, ", ") + ")"
	}
	verdict := decideEqual(fn, lowering, asmTerm, oakTerm, width, note)
	verdict.Callees = exec.summarized
	if verdict.Kind != VerdictProven {
		return verdict
	}
	effects := decideEffects(fn, lowering, exec, &verdict)
	effects.Callees = exec.summarized
	return effects
}

// decideCells decides, for every package-global cell either side writes,
// that the two sides leave the same value in it (a side that never writes
// a cell leaves its entry value); result is the result's proven verdict
// when the function has one. The proof's message names the cells.
func decideCells(fn *Function, lowering *oakLowering, exec *pathExecutor, result *Verdict) Verdict {
	oakCells := lowering.writtenCells()
	names := map[string]bool{}
	for name := range exec.cells {
		names[name] = true
	}
	for name := range oakCells {
		names[name] = true
	}
	if len(names) == 0 {
		if result != nil {
			return *result
		}
		return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (no integer result) — trusted per docs/spec/94-assembler.md §5", fn.Name)}
	}
	sorted := make([]string, 0, len(names))
	for name := range names {
		sorted = append(sorted, name)
	}
	sort.Strings(sorted)
	for _, name := range sorted {
		global := exec.globals[name]
		asmCell, oakCell := exec.cells[name], oakCells[name]
		if asmCell == nil {
			asmCell = cellEntry(name, global)
		}
		if oakCell == nil {
			oakCell = cellEntry(name, global)
		}
		verdict := decideEqual(fn, lowering, asmCell, oakCell, cellWidth(global), "")
		if verdict.Kind != VerdictProven {
			verdict.Message = strings.Replace(verdict.Message, "asm unit "+fn.Name, fmt.Sprintf("asm unit %s (the package global %s)", fn.Name, name), 1)
			return verdict
		}
	}
	cells := "the package state it writes (" + strings.Join(sorted, ", ") + ")"
	if result != nil {
		return Verdict{Kind: VerdictProven, Message: result.Message + " and " + cells}
	}
	return Verdict{Kind: VerdictProven, Message: fmt.Sprintf("asm unit %s: proven equal to its Oak body in %s", fn.Name, cells)}
}

// summarizeCall takes a call to a program function at the callee's Oak
// body (docs/spec/94-assembler.md §8, call summaries). The arguments are
// the contract registers' terms at the parameters' widths; the callee's
// body lowers to a term over them, with its own calls inlined the same
// way and recursion refused; the result register receives the term in
// the lane's canonical form — on RV64 widened as the psABI does, on
// AArch64 with the bits above the result's width (above the low word for
// a Bool, the C enum) a fresh unknown, since AAPCS64 leaves them
// unspecified; and every caller-saved register and the flags are
// forgotten, as after any call. The caller's verdict is then relative to
// the callee's Oak body, which the callee's own verdict covers, and it
// names the callees taken so. A call the summary cannot take — no callee
// known, a span or record in the signature, a body outside the term
// language — leaves the function trusted with the reason, as before.
// forgetCallerSaved drops the registers a call may clobber: x0–x17, x30
// and the flags, v0–v7 and v16–v31 (the low halves of v8–v15 are
// preserved, kept whole as they were) on AArch64; ra, t0–t6, a0–a7 and
// ft0–ft11, fa0–fa7 (f0–f7, f10–f17, f28–f31) on RV64, where the vector
// file and its configuration are forgotten as the arguments are read.
func (x *pathExecutor) forgetCallerSaved(state *symbolicState) {
	if x.arch == ArchRV64 {
		for _, r := range []int{1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31} {
			delete(state.regs, r)
		}
		for r := 0; r <= 31; r++ {
			if !rv64FloatCalleeSaved(r) {
				delete(state.fregs, r)
			}
		}
		return
	}
	for r := 0; r <= 17; r++ {
		delete(state.regs, r)
	}
	delete(state.regs, 30)
	state.flags = nil
	for r := 0; r <= 31; r++ {
		if !calleeSavedVector(r) {
			delete(state.vregs, r)
		}
	}
}

func (x *pathExecutor) summarizeCall(instr Instruction, state *symbolicState) (string, bool) {
	opaque := "instruction " + instr.Mnemonic
	if x.arch == ArchRV64 {
		opaque = "a call"
	}
	if len(instr.Operands) == 0 || x.fn == nil {
		return opaque, false
	}
	sym, isSym := instr.Operands[0].(Symbol)
	if !isSym {
		return opaque, false
	}
	callee := x.fn.Callees[sym.Name]
	if callee == nil {
		// A vector-contract callee is reached at its native entry, the Oak
		// name under the lane's suffix (VectorEntrySuffix).
		if base, suffixed := strings.CutSuffix(sym.Name, VectorEntrySuffix(x.arch)); suffixed {
			callee = x.fn.Callees[base]
		}
	}
	if callee == nil || callee.Body == nil || callee.Name == nil || callee.Receiver != nil || len(callee.TypeParams) != 0 || callee.ExternSymbol != "" {
		return opaque, false
	}
	name := callee.Name.Value
	// A unit callee (no result) is summarized for the package state and
	// the span memory it writes.
	unit := unitFunction(callee)
	var resultWidth int
	var resultSigned bool
	// A record or union result of up to two register chunks (x0 and x1,
	// a0 and a1) is summarized chunk by chunk from the callee's aggregate
	// value; its padding bits are fresh unknowns, as the ABI leaves them.
	var aggLeaves []compositeLeaf
	aggChunks := 0
	// A record result beyond two chunks is stored leaf by leaf into the
	// caller's frame at the address x8 held (memResultBase).
	memResult := false
	memResultBase := int64(0)
	// A fixed-vector result comes back whole in the lane's vector result
	// register (v0 on AArch64, v8 on RV64 — the RVV psABI; docs/spec/
	// 94-assembler.md §9, vectors across the call boundary): the callee's
	// lanes packed as the register holds them.
	var vecResult *typechecker.SimdShape
	if shape, isVector := vectorShape(callee.ReturnType); isVector && !unit {
		vecResult = &shape
	}
	// An f32/f64 result comes back in the lane's float result register:
	// the low lane of v0 (AAPCS64), fa0 (LP64D); the callee's body lowers
	// as a float at that width (docs/spec/94-assembler.md §8, floats).
	floatResult := 0
	if !unit && vecResult == nil {
		switch typeText(callee.ReturnType) {
		case "f32":
			floatResult = 32
		case "f64":
			floatResult = 64
		}
	}
	if !unit && vecResult == nil {
		w, signed, ok := contractBits(callee.ReturnType)
		if class, isClass := contractClass(callee.ReturnType); !ok || !isClass || (class == ClassV && floatResult == 0) {
			returned := typeText(callee.ReturnType)
			comp, isComposite := x.fn.Composites[returned]
			if !isComposite || len(comp.Fields) == 0 {
				return fmt.Sprintf("a call to %s returning %s", name, returned), false
			}
			leaves, _, ok := compositeLeaves(x.fn.Composites, returned, "", 0, nil)
			if !ok {
				return fmt.Sprintf("a call to %s returning %s (no layout)", name, returned), false
			}
			if comp.Size > 16 {
				// Returned through memory: the caller passed the address of
				// a frame area in x8 (nativegen: `add x8, sp, #off` before
				// the call), and the callee's leaves land there at their
				// offsets and widths; the caller's later loads read them
				// as frame slots (docs/spec/94-assembler.md §9). RV64
				// passes the area in a0, shifting the arguments, outside
				// the subset; a union's inactive payload bytes are left as
				// they were, which the leaf-wise store cannot express.
				if x.arch == ArchRV64 {
					return fmt.Sprintf("a call to %s returning %s through memory on RV64", name, returned), false
				}
				addr, isFrame := frameAddressOf(state.regs[8])
				if !isFrame {
					return fmt.Sprintf("a call to %s returning %s through an area x8 does not address in the frame", name, returned), false
				}
				for _, leaf := range leaves {
					if len(leaf.guards) > 0 {
						return fmt.Sprintf("a call to %s returning %s holding a union", name, returned), false
					}
				}
				memResultBase, memResult = addr, true
			}
			aggLeaves, aggChunks = leaves, int((comp.Size+7)/8)
		}
		resultWidth, resultSigned = w, signed
	}
	// More parameters than the registers hold are read from the caller's
	// outgoing area below (the shared layout), so their count is no bar.
	lo := newLowering(callee)
	lo.arch = x.arch
	lo.records, lo.adts, lo.constants = x.fn.Records, x.fn.ADTs, x.fn.Constants
	// The span arguments bound to the caller's owned frame arrays, written
	// back after the body (asm/span_args.go).
	var frameBorrows []frameBorrow
	lo.functions = x.fn.Callees
	lo.declareTables(x.fn.Tables)
	lo.inlining = map[string]bool{name: true}
	// The callee sees the cells as this path holds them — a store on the
	// path, else the entry value — and its writes come back into the path
	// (docs/spec/94-assembler.md §9).
	lo.globals = x.globals
	lo.declareCells()
	seeds := map[string]*term{}
	for cellName, cell := range lo.cells {
		if written, has := state.globals[cellName]; has {
			cell.value = written
		}
		seeds[cellName] = cell.value
	}
	argBase := 0
	if x.arch == ArchRV64 {
		argBase = 10 // a0
	}
	lo.concrete = x.env // a witness run: the callee's leaves are the caller's constants
	lo.writes = cloneWrites(state.writes)
	// The callee's loop events take the indices this call site's events
	// took the first time the site was reached (loopSite): a second path
	// through the same call merges its events with the first's below.
	callSite := fmt.Sprintf("call@%d", instr.Line)
	priorSite, siteSeen := x.sites[callSite]
	if siteSeen && !priorSite.diverged(state.path) {
		// The same path reaching the call again (an unrolled counted
		// loop's body): a distinct instance, its events its own.
		siteSeen = false
	}
	if siteSeen {
		lo.loopBase = priorSite.base
	} else {
		lo.loopBase = len(x.loops)
	}
	lo.loopStack = append([]int(nil), x.loopStack...)
	lo.writableSpans = map[string]bool{}
	lo.rootContracts = map[string]spanContract{}
	for _, span := range writableSpanParams(x.fn, x.spans) {
		lo.writableSpans[span] = true
		lo.rootContracts[span] = spanContract{elemWidth: int(x.spans[span]) * 8}
	}
	// The arguments by the shared layout (asm/abi.go): registers while
	// they fit, then the caller's outgoing area — slots of this path's
	// frame at the call's sp, which the executor holds as the caller
	// stored them.
	args := classifyArguments(callee.Parameters, x.fn.Composites)
	classes := make([]ArgClass, 0, len(args))
	ints := make([]int, 0, len(args)) // the index into places of each integer-class argument
	for _, arg := range args {
		if arg.param.Variadic {
			return fmt.Sprintf("a call to %s: parameter %s is variadic", name, arg.param.Name.Value), false
		}
		if arg.kind == argRecord && arg.comp.HFA {
			return fmt.Sprintf("a call to %s: parameter %s is a record passed in floating-point registers", name, arg.param.Name.Value), false
		}
		if arg.problem != "" {
			return fmt.Sprintf("a call to %s: parameter %s is not a fixed-width integer", name, arg.param.Name.Value), false
		}
		if arg.kind == argVector && x.arch == ArchRV64 {
			ints = append(ints, -1) // RV64: v8–v23 by count, outside the layout
			continue
		}
		ints = append(ints, len(classes))
		classes = append(classes, arg.class)
	}
	places, _ := LayoutArguments(classes, x.fn.PackedStackArgs)
	// Vector arguments travel in the vector file's argument registers, in
	// declaration order: v0–v7 on AArch64, v8–v23 on RV64.
	vecArg0, vecArgs := 0, 8
	if x.arch == ArchRV64 {
		vecArg0, vecArgs = rv64VectorResultRegister, 16
	}
	nextVec := 0
	// word reads word k of an argument: its register, or its bytes in the
	// outgoing area (a span's length is the 4-byte word after its base;
	// a scalar its natural size, zero-extended as the callee's load is).
	word := func(place ArgPlace, k int, size int64) (*term, bool) {
		if !place.OnStack {
			value, has := state.regs[argBase+place.Reg+k]
			return value, has
		}
		if x.arch == ArchRV64 {
			return nil, false
		}
		value, ok := state.loadSlot(-state.disp+place.Offset+int64(k)*8, size)
		if !ok {
			return nil, false
		}
		return zeroExtend(value, 64), true
	}
	// f32/f64 arguments share v0–v7 with the vector arguments on AArch64
	// and travel in fa0–fa7 (f10–f17) on RV64, in declaration order.
	nextFloat := 0
	for i, arg := range args {
		param := arg.param
		if floatWidth, isFloat := map[string]int{"f32": 32, "f64": 64}[typeText(param.Type)]; isFloat {
			var value *term
			var has bool
			if x.arch == ArchRV64 {
				if nextFloat >= 8 {
					return fmt.Sprintf("a call to %s with floating-point arguments beyond the registers", name), false
				}
				value, has = state.read(Register{Class: ClassRV64F, Num: 10 + nextFloat})
				nextFloat++
				if !has {
					return "unbound floating-point register read", false
				}
			} else if place := places[ints[i]]; place.OnStack {
				// Past v0–v7: its bit pattern in the outgoing area.
				value, has = word(place, 0, int64(floatWidth)/8)
				if !has {
					return "unbound stack argument read", false
				}
			} else {
				vec, bound := state.readVec(place.Reg)
				if !bound {
					return "unbound vector register read", false
				}
				value, has = vec.lanesAt(floatWidth)[0], true
			}
			lo.locals[param.Name.Value] = &oakLocal{value: truncate(value, floatWidth), width: floatWidth}
			lo.floats[param.Name.Value] = floatWidth
			continue
		}
		if arg.kind == argVector {
			shape, _ := vectorShape(param.Type)
			var value vecValue
			switch {
			case x.arch == ArchRV64:
				if nextVec >= vecArgs {
					return fmt.Sprintf("a call to %s with vector arguments beyond the registers", name), false
				}
				var has bool
				value, has = state.readVec(vecArg0 + nextVec)
				nextVec++
				if !has {
					return "unbound vector register read", false
				}
			case places[ints[i]].OnStack:
				// Past v0–v7: sixteen bytes in the outgoing area, the two
				// eight-byte words the caller's `str q` left.
				place := places[ints[i]]
				lo64, hasLo := word(place, 0, 8)
				hi64, hasHi := word(place, 1, 8)
				if !hasLo || !hasHi {
					return "unbound stack argument read", false
				}
				value = vecOfLanes([]*term{lo64, hi64}, 64)
			default:
				var has bool
				value, has = state.readVec(places[ints[i]].Reg)
				if !has {
					return "unbound vector register read", false
				}
			}
			lanes := value.lanesAt(laneWidth(shape))[:shape.Lanes]
			lo.locals[param.Name.Value] = &oakLocal{agg: vectorOfLanes(lanes, lo.vectorType(shape))}
			continue
		}
		place := places[ints[i]]
		switch arg.kind {
		case argRecord:
			// A record argument: by value in one or two register chunks,
			// the callee's parameter is the aggregate unpacked from them;
			// by reference beyond 16 bytes, the word holding the caller's
			// own record parameter's address — the callee's leaves are
			// then the caller's leaves by name.
			if !arg.indirect {
				if place.OnStack {
					return fmt.Sprintf("a call to %s: parameter %s is a record passed by value on the stack", name, param.Name.Value), false
				}
				if _, reason, ok := x.bindAggregateArgument(lo, param, arg.comp, argBase+place.Reg, argBase, state, name); !ok {
					return reason, false
				}
				continue
			}
			base, has := word(place, 0, 8)
			if !has {
				return fmt.Sprintf("a call to %s: the record argument %s is not a record parameter of the caller", name, param.Name.Value), false
			}
			if addr, isFrame := frameAddressOf(base); isFrame || func() bool { addr, isFrame = rvFrameAddrOf(base); return isFrame }() {
				// The caller's copy of the record in its frame (the rv64
				// lane copies a by-reference record it passes on, and a
				// record local passed by reference): the callee's parameter
				// is the aggregate read from the frame slots.
				if reason, ok := x.frameRecordArgument(lo, param, arg.comp, addr, state, name); !ok {
					return reason, false
				}
				continue
			}
			owner, offset, isBase := spanBaseOf(base)
			if _, isRecord := x.records[owner]; !isBase || offset != 0 || !isRecord {
				return fmt.Sprintf("a call to %s: the record argument %s is not a record parameter of the caller", name, param.Name.Value), false
			}
			typ, ok := lo.oakTypeOf(param.Type)
			if !ok || typ.kind == oakScalar {
				return fmt.Sprintf("a call to %s: parameter %s has a type without a model", name, param.Name.Value), false
			}
			agg, ok := lo.paramAggregate(typ, owner)
			if !ok {
				return fmt.Sprintf("a call to %s: parameter %s has a type without a model", name, param.Name.Value), false
			}
			lo.locals[param.Name.Value] = &oakLocal{agg: agg}
		case argSpan:
			// A span argument: the {base, len} pair of one of the caller's
			// span parameters, whole — the callee's parameter is an alias
			// of the caller's span and shares its memory (asm/effects.go).
			base, hasBase := word(place, 0, 8)
			length, hasLen := word(place, 1, 4)
			whole := hasBase && hasLen
			var owner string
			if whole {
				var offset int64
				owner, offset, whole = spanBaseOf(base)
				_, isRecord := x.records[owner]
				whole = whole && !isRecord && offset == 0 && x.spans[owner] == arg.elem && (x.isSpanLength(length, owner) || x.isTableLength(length, owner))
			}
			if !whole && hasBase && hasLen {
				// A derived span of one of the caller's spans (`subslice(v,
				// start, n)`): the base is the span's plus scaled index
				// terms, the length any term — the callee's parameter is an
				// alias at that offset with that length
				// (asm/derived_spans.go).
				if root, offset, isDerived := spanAddressOf(base, arg.elem); isDerived && x.spans[root] == arg.elem {
					if _, isRecord := x.records[root]; !isRecord {
						elemType := typeText(param.Type.(*ast.IndexExpression).Left)
						lo.spans[param.Name.Value] = spanContract{elemWidth: int(arg.elem) * 8, signed: strings.HasPrefix(elemType, "i")}
						if lo.spanAlias == nil {
							lo.spanAlias = map[string]string{}
						}
						lo.spanAlias[param.Name.Value] = root
						if lo.spanOffset == nil {
							lo.spanOffset, lo.spanLen = map[string]*term{}, map[string]*term{}
						}
						if offset != nil {
							lo.spanOffset[param.Name.Value] = offset
						}
						lo.spanLen[param.Name.Value] = truncate(length, 32)
						break
					}
				}
			}
			if !whole {
				// A span or view over the caller's owned frame array
				// (`span(&buf)`): the callee's parameter is the array's
				// contents as an aggregate local, written back after the
				// body when the span is writable (asm/span_args.go).
				borrow, reason, ok := x.frameArrayArgument(state, lo, name, param.Name.Value, param.Type, arg.elem, base, length, hasBase && hasLen)
				if !ok {
					return reason, false
				}
				frameBorrows = append(frameBorrows, borrow)
				break
			}
			if lo.spanAlias == nil {
				lo.spanAlias = map[string]string{}
			}
			if recordArg, isRecordSpan := x.recordSpans[owner]; isRecordSpan {
				// A span of records passed on: the callee's parameter is an
				// alias of the caller's, its leaf memories the caller's.
				if lo.recordSpans == nil {
					lo.recordSpans = map[string]recordSpanArg{}
				}
				lo.recordSpans[param.Name.Value] = recordArg
				lo.spanAlias[param.Name.Value] = owner
				break
			}
			elemType := typeText(param.Type.(*ast.IndexExpression).Left)
			lo.spans[param.Name.Value] = spanContract{elemWidth: int(arg.elem) * 8, signed: strings.HasPrefix(elemType, "i")}
			lo.spanAlias[param.Name.Value] = owner
		default:
			w, signed, _ := contractBits(param.Type)
			value, has := word(place, 0, arg.scalarSz)
			if !has {
				return "unbound register read", false
			}
			lo.locals[param.Name.Value] = &oakLocal{value: truncate(value, w), width: w, signed: signed}
		}
	}
	if x.arch == ArchRV64 {
		// Every vector register is caller-saved and the configuration is
		// not preserved (the RVV psABI): the arguments are read, the file
		// is forgotten, and a vector result is written to v8 below.
		state.vregs, state.rvcfg = nil, nil
	}
	body := callee.Body
	if loop, isTail := tailRecursionAsLoop(callee, body); isTail {
		body = loop
	}
	var result *term
	var aggregate *oakValue
	var vecLanes []*term
	switch {
	case unit:
		if reason, ok := lo.lowerUnitBody(body); !ok {
			return fmt.Sprintf("a call to %s whose body contains %s", name, reason), false
		}
	case vecResult != nil:
		var reason string
		var ok bool
		vecLanes, reason, ok = lo.vectorLanes(body, *vecResult)
		if !ok {
			return fmt.Sprintf("a call to %s whose body contains %s", name, reason), false
		}
	case aggLeaves != nil:
		typ, ok := lo.oakTypeOf(callee.ReturnType)
		if !ok || typ.kind == oakScalar {
			return fmt.Sprintf("a call to %s returning %s (no model)", name, typeText(callee.ReturnType)), false
		}
		var reason string
		aggregate, reason, ok = lo.aggregateValue(body, typ)
		if !ok {
			return fmt.Sprintf("a call to %s whose body contains %s", name, reason), false
		}
	default:
		var reason string
		var ok bool
		result, reason, ok = lo.lower(body, resultWidth)
		if !ok {
			return fmt.Sprintf("a call to %s whose body contains %s", name, reason), false
		}
	}
	// The callee's data-dependent loops are the caller's events: numbered
	// after the caller's (loopBase), nested under the loop being executed,
	// their fresh symbols declared for the verdict; the Oak side inlines
	// the same body and creates the same events, which the coupling pairs
	// by identity (asm/loops.go).
	for _, ev := range lo.loops {
		ev.oakDerived = true
		ev.at = x.callAt
	}
	if siteSeen {
		if len(lo.loops) != priorSite.count {
			return fmt.Sprintf("a call to %s whose loops differ between two paths", name), false
		}
		for k, ev := range lo.loops {
			merged, reason, ok := mergeLoopEvents(state.pathCondition(), ev, x.loops[priorSite.base+k])
			if !ok {
				return fmt.Sprintf("a call to %s %s", name, reason), false
			}
			x.loops[priorSite.base+k] = merged
		}
		priorSite.paths = append(priorSite.paths, state.path)
		x.sites[callSite] = priorSite
	} else {
		if len(lo.loops) > 0 && x.sites[callSite].count == 0 {
			if x.sites == nil {
				x.sites = map[string]loopSite{}
			}
			x.sites[callSite] = loopSite{base: len(x.loops), count: len(lo.loops), paths: []*pathNode{state.path}}
		}
		x.loops = append(x.loops, lo.loops...)
	}
	for symbol, width := range lo.fresh {
		if x.freshSyms == nil {
			x.freshSyms = map[string]int{}
		}
		if _, known := x.freshSyms[symbol]; !known {
			x.freshSyms[symbol] = width
			x.declared[symbol] = width
		}
	}
	state.writes = lo.writes // the callee's stores through the caller's spans
	for _, borrow := range frameBorrows {
		if reason, ok := borrow.writeBack(state, lo); !ok {
			return fmt.Sprintf("a call to %s: %s", name, reason), false
		}
	}
	for cellName, cell := range lo.cells {
		if cell.value != seeds[cellName] {
			if state.globals == nil {
				state.globals = map[string]*term{}
			}
			state.globals[cellName] = cell.value
		}
	}
	if unit {
		// x0–x17 (a0–a7, t0–t6 on rv64) and the caller-saved float and
		// vector registers are dead after the call; no result.
		x.forgetCallerSaved(state)
		for _, seen := range x.summarized {
			if seen == name {
				return "", true
			}
		}
		x.summarized = append(x.summarized, name)
		return "", true
	}
	if vecResult != nil {
		// The caller-saved registers are dead after the call: on RV64 the
		// whole vector file and its configuration, on AArch64 v0–v7 and
		// v16–v31 (the low halves of v8–v15 are preserved, kept as they
		// were). The result register receives the callee's lanes.
		if x.arch == ArchRV64 {
			for _, r := range []int{1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31} {
				delete(state.regs, r)
			}
		} else {
			for r := 0; r <= 17; r++ {
				delete(state.regs, r)
			}
			delete(state.regs, 30)
			state.flags = nil
			for r := 0; r <= 31; r++ {
				if r < 8 || r >= 16 {
					delete(state.vregs, r)
				}
			}
		}
		state.writeVec(vecArg0, vecOfLanes(vecLanes, laneWidth(*vecResult)))
		for _, seen := range x.summarized {
			if seen == name {
				return "", true
			}
		}
		x.summarized = append(x.summarized, name)
		return "", true
	}
	if aggregate != nil && memResult {
		terms := map[string]*term{}
		leafTerms(aggregate, "", terms)
		for _, leaf := range aggLeaves {
			t, has := terms[leaf.name]
			if !has {
				return fmt.Sprintf("a call to %s returning %s with a leaf the layout lacks", name, typeText(callee.ReturnType)), false
			}
			// A Bool leaf is its 4-byte C enum cell holding 0 or 1; every
			// other leaf is stored at its width. The padding bytes between
			// leaves keep what the frame held: the callee's contract says
			// nothing about them and the Oak body never reads them.
			cell := leaf.width
			if cell == 1 {
				cell = 32
			}
			state.storeSlot(memResultBase+leaf.offset, zeroExtend(adaptWidth(t, leaf.width), cell), int64(cell/8))
		}
		x.forgetCallerSaved(state)
		for _, seen := range x.summarized {
			if seen == name {
				return "", true
			}
		}
		x.summarized = append(x.summarized, name)
		return "", true
	}
	if aggregate != nil {
		chunks := make([]*term, aggChunks)
		for k := range chunks {
			chunk, ok := packAggregateChunk(aggregate, aggLeaves, int64(k))
			if !ok {
				return fmt.Sprintf("a call to %s returning %s with a leaf the layout lacks", name, typeText(callee.ReturnType)), false
			}
			if m := definedMask(aggLeaves, int64(k)); m != ^uint64(0) {
				// The padding bytes: unspecified by the ABI, zero in a
				// witness run (the callee's own code cleared them).
				var pad *term
				if x.concrete {
					pad = constTerm(0, 64)
				} else {
					x.callSites++
					padName := fmt.Sprintf("call%d#pad%d", x.callSites, k)
					if x.freshSyms == nil {
						x.freshSyms = map[string]int{}
					}
					x.freshSyms[padName] = 64
					x.declared[padName] = 64
					pad = paramTerm(padName, 64)
				}
				chunk = binaryTerm("or", binaryTerm("and", chunk, constTerm(m, 64)), binaryTerm("and", pad, constTerm(^m, 64)))
			}
			chunks[k] = chunk
		}
		if x.arch == ArchRV64 {
			for _, r := range []int{1, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31} {
				delete(state.regs, r)
			}
			for k, chunk := range chunks {
				state.regs[10+k] = chunk
			}
		} else {
			for r := 0; r <= 17; r++ {
				delete(state.regs, r)
			}
			delete(state.regs, 30)
			state.flags = nil
			for k, chunk := range chunks {
				state.regs[k] = chunk
			}
		}
		for _, seen := range x.summarized {
			if seen == name {
				return "", true
			}
		}
		x.summarized = append(x.summarized, name)
		return "", true
	}
	if floatResult != 0 {
		// The caller-saved registers are dead after the call; the float
		// result register receives the callee's pattern at its width — on
		// AArch64 the low lane of v0, its upper bits unspecified (fresh),
		// the upper half zero as every scalar write leaves it.
		x.forgetCallerSaved(state)
		if x.arch == ArchRV64 {
			state.write(rv64FloatResultRegister, result)
		} else {
			low := zeroExtend(result, 64)
			if floatResult < 64 {
				var upper *term
				if x.concrete {
					upper = constTerm(0, 64-floatResult) // a witness run: the callee's own scalar write cleared them
				} else {
					x.callSites++
					hi := fmt.Sprintf("call%d#hi", x.callSites)
					if x.freshSyms == nil {
						x.freshSyms = map[string]int{}
					}
					x.freshSyms[hi] = 64 - floatResult
					x.declared[hi] = 64 - floatResult
					upper = paramTerm(hi, 64-floatResult)
				}
				low = binaryTerm("or", low, binaryTerm("shl", zeroExtend(upper, 64), constTerm(uint64(floatResult), 64)))
			}
			state.writeVec(0, vecFromLow(low))
		}
		for _, seen := range x.summarized {
			if seen == name {
				return "", true
			}
		}
		x.summarized = append(x.summarized, name)
		return "", true
	}
	value := zeroExtend(result, resultWidth)
	value = zeroExtend(value, 64)
	if x.arch == ArchRV64 {
		for _, r := range []int{1, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31} {
			delete(state.regs, r) // ra, t0–t6, a1–a7: dead after a call
		}
		switch {
		case resultSigned:
			value = extendTerm(value, resultWidth, 64, true)
		case resultWidth == 32:
			value = extendTerm(value, 32, 64, true) // a u32 arrives sign-extended (Oak.RiscV.widen)
		}
		state.regs[10] = value
	} else {
		for r := 1; r <= 17; r++ {
			delete(state.regs, r)
		}
		delete(state.regs, 30)
		state.flags = nil
		defined := resultWidth
		if typeText(callee.ReturnType) == "Bool" {
			defined = 32 // the C enum: the whole low word holds 0 or 1
		}
		if defined < 64 {
			x.callSites++
			hi := fmt.Sprintf("call%d#hi", x.callSites)
			var upper *term
			if x.concrete {
				upper = constTerm(0, 64-defined) // a witness run: the callee's own code cleared them
			} else {
				if x.freshSyms == nil {
					x.freshSyms = map[string]int{}
				}
				x.freshSyms[hi] = 64 - defined
				x.declared[hi] = 64 - defined
				upper = paramTerm(hi, 64-defined)
			}
			value = binaryTerm("or", value, binaryTerm("shl", zeroExtend(upper, 64), constTerm(uint64(defined), 64)))
		}
		state.regs[0] = value
	}
	for _, seen := range x.summarized {
		if seen == name {
			return "", true
		}
	}
	x.summarized = append(x.summarized, name)
	return "", true
}

// prepareLowering builds the Oak side for a function: the signature's
// contract, the program's declarations, the record and union parameters as
// aggregates, and (in a witness run) the concrete inputs.
func prepareLowering(fn *Function, sig *ast.FunctionStatement, concrete map[string]uint64) *oakLowering {
	lowering := newLowering(sig)
	lowering.arch = fn.Arch
	lowering.records, lowering.adts = fn.Records, fn.ADTs
	lowering.constants = fn.Constants
	lowering.globals = fn.Globals
	lowering.bindRecordSpans(fn, sig)
	lowering.functions = fn.Callees // the Oak body's calls inline (inlineCall)
	lowering.declareTables(fn.Tables)
	lowering.concrete = concrete
	lowering.bindAggregateParams(sig)
	lowering.declareCells()
	return lowering
}

// bindRecordSpans registers the span-of-record parameters (the executor
// binds the same shape) and takes them out of the scalar parameters
// newLowering guessed them into.
func (lo *oakLowering) bindRecordSpans(fn *Function, sig *ast.FunctionStatement) {
	lo.bindRecordSpansWith(fn.Composites, sig)
}

func (lo *oakLowering) bindRecordSpansWith(comps map[string]Composite, sig *ast.FunctionStatement) {
	for _, param := range sig.Parameters {
		if param == nil || param.Name == nil {
			continue
		}
		arg, _, isRecordSpan, ok := recordSpanOf(comps, param.Type)
		if !isRecordSpan || !ok {
			continue
		}
		if lo.recordSpans == nil {
			lo.recordSpans = map[string]recordSpanArg{}
		}
		lo.recordSpans[param.Name.Value] = arg
		delete(lo.params, param.Name.Value)
		delete(lo.signed, param.Name.Value)
		if isWritableSpan(param.Type) {
			if lo.writableSpans == nil {
				lo.writableSpans = map[string]bool{}
			}
			lo.writableSpans[param.Name.Value] = true
		}
	}
}

// recordSpanPlace is a leaf of a record span's element named by an
// expression — `v[i].f…` (memory `v.f`, index i) or `v[i].f…[j]` (memory
// `v.f`, index i·N + j): the memory, the index, the leaf's name inside the
// element (for a constant-index parameter) and width; handled reports the
// shape matched.
type recordSpanPlace struct {
	span, memory, leafName string
	index                  *term
	width                  int
}

func (lo *oakLowering) recordSpanPlaceOf(e *ast.IndexExpression) (place recordSpanPlace, handled bool, reason string, ok bool) {
	if len(lo.recordSpans) == 0 {
		return recordSpanPlace{}, false, "", false
	}
	var arrayIndex ast.Expression
	cur := e
	if !cur.Dot {
		left, isIndex := cur.Left.(*ast.IndexExpression)
		if !isIndex || !left.Dot {
			return recordSpanPlace{}, false, "", false
		}
		arrayIndex = cur.Index
		cur = left
	}
	path := ""
	for cur.Dot {
		field, isName := cur.Index.(*ast.Identifier)
		if !isName {
			return recordSpanPlace{}, false, "", false
		}
		path = "." + field.Value + path
		next, isIndex := cur.Left.(*ast.IndexExpression)
		if !isIndex {
			return recordSpanPlace{}, false, "", false
		}
		cur = next
	}
	root, isIdent := cur.Left.(*ast.Identifier)
	if !isIdent {
		return recordSpanPlace{}, false, "", false
	}
	arg, isRecord := lo.recordSpans[root.Value]
	if !isRecord {
		return recordSpanPlace{}, false, "", false
	}
	if _, isLocal := lo.locals[root.Value]; isLocal {
		return recordSpanPlace{}, false, "", false
	}
	idx, reason, okIdx := lo.lower(cur.Index, 32)
	if !okIdx {
		return recordSpanPlace{}, true, reason, false
	}
	span := lo.spanRoot(root.Value)
	if lo.concrete != nil {
		// Past the span's length: Oak traps on this input (noted by the
		// witness run under the path).
		lo.addTrap(cmpTerm("hs", idx, lo.spanLenTerm(root.Value, 32)))
		if lo.witnessTrapped {
			return recordSpanPlace{}, true, fmt.Sprintf("an index past len(%s) on this input", root.Value), false
		}
	}
	if arrayIndex != nil {
		j, reason, okJ := lo.lower(arrayIndex, 32)
		if !okJ {
			return recordSpanPlace{}, true, reason, false
		}
		var length int64
		var elemLeaf compositeLeaf
		found := false
		for _, leaf := range arg.leaves {
			if strings.HasPrefix(leaf.name, path+"[") {
				if !found {
					elemLeaf, found = leaf, true
				}
				length++
			}
		}
		if !found {
			return recordSpanPlace{}, true, fmt.Sprintf("%s is not an array field of %s's element", path, root.Value), false
		}
		if j.kind == termConst && int64(j.value) >= length {
			return recordSpanPlace{}, true, fmt.Sprintf("an index past the %d elements of %s", length, path), false
		}
		linear := binaryTerm("add", binaryTerm("mul", idx, constTerm(uint64(length), 32)), j)
		return recordSpanPlace{span: span, memory: span + path, leafName: path, index: linear, width: elemLeaf.width}, true, "", true
	}
	for _, leaf := range arg.leaves {
		if leaf.name == path {
			return recordSpanPlace{span: span, memory: span + path, leafName: path, index: idx, width: leaf.width}, true, "", true
		}
	}
	return recordSpanPlace{}, true, fmt.Sprintf("%s is not a scalar leaf of %s's element", path, root.Value), false
}

// assignRecordSpanField lowers `v[i].f… = value` (or `v[i].f…[j] = value`)
// over a span parameter of records as a write to the leaf memory's log
// under the path condition — the writer's counterpart of recordSpanField.
func (lo *oakLowering) assignRecordSpanField(s *ast.IndexAssignmentStatement) (handled bool, reason string, ok bool) {
	if s.Target == nil {
		return false, "", false
	}
	place, handled, reason, okPlace := lo.recordSpanPlaceOf(s.Target)
	if !handled {
		return false, "", false
	}
	if !okPlace {
		return true, reason, false
	}
	if !lo.writableSpans[place.span] {
		return true, fmt.Sprintf("a store through the view %s", place.span), false
	}
	value, reason, okValue := lo.lower(s.Value, place.width)
	if !okValue {
		return true, reason, false
	}
	lo.writes = appendWrite(lo.writes, place.memory, place.index, truncate(value, place.width), lo.path)
	return true, "", true
}

// recordSpanField lowers `v[i].f…` (a scalar leaf) or `v[i].f…[j]` (an
// element of an array field) over a span parameter of records to the
// leaf's memory at the index — the newest write on the path, else the
// entry select term; handled reports the shape matched.
func (lo *oakLowering) recordSpanField(e *ast.IndexExpression) (t *term, width int, handled bool, reason string, ok bool) {
	place, handled, reason, okPlace := lo.recordSpanPlaceOf(e)
	if !handled || !okPlace {
		return nil, 0, handled, reason, false
	}
	entry := recordFieldTerm(place.span, place.index, place.leafName, place.width, lo.concrete != nil)
	return memoryAt(lo.writes[place.memory], place.index, entry), place.width, true, "", true
}

// recordLeafWidth is the width of a record span's leaf named by a
// parameter `v[k].f` (elementParam folds it to the memory `v.f`).
func (lo *oakLowering) recordLeafWidth(memory string) (int, bool) {
	dot := strings.IndexByte(memory, '.')
	if dot <= 0 {
		return 0, false
	}
	span := lo.spanRoot(memory[:dot])
	arg, isRecord := lo.recordSpans[span]
	if !isRecord {
		return 0, false
	}
	// A scalar leaf's own memory (`v.f`), or an array field's (`v.a`); the
	// parameter `v[k].a[j]` folds to the memory `v.a[j]`, an element leaf.
	if width, isMemory := arg.memoryWidths(span)[span+memory[dot:]]; isMemory {
		return width, true
	}
	for _, leaf := range arg.leaves {
		if leaf.name == memory[dot:] {
			return leaf.width, true
		}
	}
	return 0, false
}

// declareCells gives every global the body addresses a local at its entry
// value (a parameter of the same name shadows it, as in the body).
func (lo *oakLowering) declareCells() {
	if len(lo.globals) == 0 {
		return
	}
	if lo.locals == nil {
		lo.locals = map[string]*oakLocal{}
	}
	lo.cells = map[string]*oakLocal{}
	for name, global := range lo.globals {
		if _, isParam := lo.params[name]; isParam {
			continue
		}
		if _, isSpan := lo.spans[name]; isSpan {
			continue
		}
		cell := &oakLocal{value: cellEntry(name, global), width: cellWidth(global)}
		lo.locals[name] = cell
		lo.cells[name] = cell
	}
}

// writtenCells are the cells whose final value is not their entry value:
// the package state the body writes.
func (lo *oakLowering) writtenCells() map[string]*term {
	out := map[string]*term{}
	for name, cell := range lo.cells {
		entry := cellEntry(name, lo.globals[name])
		if cell.value != nil && !(cell.value.kind == termParam && cell.value.name == entry.name) {
			out[name] = cell.value
		}
	}
	return out
}

// lowerUnitBody lowers the statements of a body with no result: the
// package state it writes is what the verdict compares.
func (lo *oakLowering) lowerUnitBody(body ast.Expression) (string, bool) {
	block, isBlock := body.(*ast.BlockExpression)
	if !isBlock || block.Block == nil {
		return "a unit body that is not a block", false
	}
	if lo.locals == nil {
		lo.locals = map[string]*oakLocal{}
	}
	for _, stmt := range block.Block.Statements {
		switch s := stmt.(type) {
		case *ast.ExpressionStatement:
			if match, isMatch := s.Expression.(*ast.MatchExpression); isMatch {
				if reason, ok := lo.lowerConditionalStatement(match); !ok {
					return reason, false
				}
				continue
			}
			if reason, isAssert, ok := lo.lowerAssert(s.Expression); isAssert {
				if !ok {
					return reason, false
				}
				continue
			}
			if handled, reason, ok := lo.lowerUnitCall(s.Expression); handled {
				if !ok {
					return reason, false
				}
				continue
			}
			return "an expression statement for its effect", false
		case *ast.VariableDeclaration:
			if reason, ok := lo.declareLocal(s); !ok {
				return reason, false
			}
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
		default:
			return fmt.Sprintf("%T", stmt), false
		}
	}
	return "", true
}

// resultComposite is the function's record or union result when the
// executor binds it (one register chunk), with its leaves.
func resultComposite(fn *Function, sig *ast.FunctionStatement) ([]compositeLeaf, int, bool) {
	name := typeText(sig.ReturnType)
	comp, isComposite := fn.Composites[name]
	if !isComposite || len(comp.Fields) == 0 {
		return nil, 0, false
	}
	leaves, _, ok := compositeLeaves(fn.Composites, name, "", 0, nil)
	return leaves, int((comp.Size + 7) / 8), ok
}

// resultTerm lowers the Oak body to the term the executor's result is
// compared with: a scalar at the contract width, or a record's register
// chunk (lo.resultChunk: the first for a one-chunk record) packed from
// its leaves (width 64).
func (lo *oakLowering) resultTerm(fn *Function, sig *ast.FunctionStatement, oakBody ast.Expression) (*term, int, string, bool) {
	if leaves, _, isComposite := resultComposite(fn, sig); isComposite {
		typ, ok := lo.oakTypeOf(sig.ReturnType)
		if !ok || typ.kind == oakScalar {
			return nil, 0, "a result whose type has no model", false
		}
		value, reason, ok := lo.aggregateValue(oakBody, typ)
		if !ok {
			return nil, 0, reason, false
		}
		packed, ok := packAggregateChunk(value, leaves, int64(lo.resultChunk))
		if !ok {
			return nil, 0, "a record result with a leaf the layout lacks", false
		}
		return packed, 64, "", true
	}
	width, _, _ := contractBits(sig.ReturnType)
	t, reason, ok := lo.lower(oakBody, width)
	return t, width, reason, ok
}

// maskResult hides the padding bytes of a record result's chunk (the Oak
// side never reads them, so the comparison is over the fields alone).
func maskResult(fn *Function, sig *ast.FunctionStatement, asmTerm *term, chunk int) *term {
	leaves, _, isComposite := resultComposite(fn, sig)
	if !isComposite {
		return asmTerm
	}
	return binaryTerm("and", zeroExtend(asmTerm, 64), constTerm(leafMask(leaves, int64(chunk)), 64))
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
	// locals is created here so every path that declares one — a statement
	// body, or a block or match in result position (resultTerm through
	// aggregateValue) — writes into a map; the dbs pilot's `-native` panic
	// was a nil map on the result path (docs/notes/dbs-feedback-2026-09.md).
	lowering := &oakLowering{params: map[string]int{}, signed: map[string]bool{}, spans: map[string]spanContract{}, fresh: map[string]int{}, floats: map[string]int{}, locals: map[string]*oakLocal{}, writableSpans: map[string]bool{}, rootContracts: map[string]spanContract{}}
	for _, param := range sig.Parameters {
		if elem, _, isSpan := spanShape(param.Type); isSpan {
			if isWritableSpan(param.Type) {
				lowering.writableSpans[param.Name.Value] = true
				lowering.rootContracts[param.Name.Value] = lowering.spans[param.Name.Value]
			}
			elemType := typeText(param.Type.(*ast.IndexExpression).Left)
			lowering.spans[param.Name.Value] = spanContract{elemWidth: int(elem) * 8, signed: strings.HasPrefix(elemType, "i"), float: elemType == "f32" || elemType == "f64"}
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
// witnessVisitBudget bounds the node visits of decideEqual's witness pass
// (the terms' DAG size times the inputs evaluated).
const witnessVisitBudget = 4000000

// canonical rewrites a term for the decision so that one value has one
// spelling on both sides: a product by a constant power of two is the
// shift the backend's strength reduction emits (`n * 8` against `lsl
// #3`), rebuilt through the constructors so their folds apply. The
// lowering itself keeps the product, which the refinement model renders
// (Oak.LoweringRefinement); only the comparison canonicalizes.
func canonical(t *term) *term {
	return canonicalMemo(t, map[*term]*term{}, map[*term]bool{})
}

func canonicalMemo(t *term, memo map[*term]*term, boolean map[*term]bool) *term {
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
	case termFloat, termQuant:
		out = t // an operation's spelling is its identity; a binder's body stays as built
	default:
		left, right, cond := canonicalMemo(t.left, memo, boolean), canonicalMemo(t.right, memo, boolean), canonicalMemo(t.cond, memo, boolean)
		switch t.kind {
		case termBinary:
			if t.op == "mul" && left.width == t.width {
				switch {
				case right.kind == termConst && right.value != 0 && right.value&(right.value-1) == 0:
					out = binaryTerm("shl", left, constTerm(uint64(bits.TrailingZeros64(right.value)), t.width))
				case left.kind == termConst && left.value != 0 && left.value&(left.value-1) == 0 && right.width == t.width:
					out = binaryTerm("shl", right, constTerm(uint64(bits.TrailingZeros64(left.value)), t.width))
				}
			}
			if out == nil && t.op == "and" && right.kind == termConst && isLowMask(right.value) {
				switch {
				case left.kind == termIte:
					// A mask over a conditional is a conditional of masked
					// arms (pushMask's rule): the two sides' arms then meet
					// arm for arm where one side masks the whole.
					// The arms are canonical already (children first); the
					// mask is applied to each without re-entering the
					// canonicalizer, a nested conditional arm by arm.
					var arm func(x *term) *term
					arm = func(x *term) *term {
						if x.kind == termIte {
							return iteTerm(x.cond, arm(x.left), arm(x.right))
						}
						switch {
						case right.value == mask(left.width) && left.width < t.width:
							return zeroExtend(adaptWidth(x, left.width), t.width)
						case right.value == mask(t.width):
							return adaptWidth(x, t.width)
						}
						return adaptWidth(binaryTerm("and", adaptWidth(x, t.width), right), t.width)
					}
					out = iteTerm(left.cond, arm(left.left), arm(left.right))
				case right.value == mask(t.width) && left.width > t.width:
					// A full mask at the term's width over a wider operand is
					// its truncation, which folds a zero-extension away; a
					// truncation that only wraps the operand again is left.
					if tr := truncate(left, t.width); !(tr.kind == termBinary && tr.op == "and" && tr.left == left) {
						out = canonicalMemo(tr, memo, boolean)
					}
				}
			}
			if out == nil && (t.op == "and" || t.op == "or") && left.width == right.width && right.width == t.width {
				// Boolean algebra the machine's branches leave behind: a
				// path condition and its complement, joined where the two
				// paths merge, are a tautology (`here != n or here == n`)
				// or a contradiction; a conjunct with zero is zero, a
				// disjunct with every bit set is every bit.
				switch {
				case t.op == "and" && ((left.kind == termConst && left.value == 0) || (right.kind == termConst && right.value == 0)):
					out = constTerm(0, t.width)
				case t.op == "or" && ((left.kind == termConst && left.value == mask(t.width)) || (right.kind == termConst && right.value == mask(t.width))):
					out = constTerm(mask(t.width), t.width)
				case t.width == 1 && complementary(left, right):
					if t.op == "or" {
						out = constTerm(1, 1)
					} else {
						out = constTerm(0, 1)
					}
				}
			}
			if out == nil && t.op == "and" && t.width == 1 && right.kind == termConst && right.value == 1 && left.width > 1 && left.kind == termBinary && (left.op == "and" || left.op == "or" || left.op == "xor") && booleanValued(left, boolean) {
				// A 1/0 value's low bit is the value: the truncation of a
				// bitwise combination of 1/0 values to one bit is the
				// combination of their truncations (`eor w, w, #1` then
				// the bit: the negation of the bit), so the machine's
				// negations and the Oak body's meet at one width.
				out = canonicalMemo(binaryTerm(left.op, truncate(left.left, 1), truncate(left.right, 1)), memo, boolean)
			}
			if out == nil && t.op == "xor" && t.width == 1 && right.kind == termConst && right.value == 1 && left.kind == termBinary && left.op == "xor" && left.width == 1 && left.right.kind == termConst && left.right.value == 1 {
				out = left.left // a double negation
			}
			if out == nil && t.op == "xor" && t.width == 1 {
				// The negation of a comparison is the opposite comparison:
				// `here < found` as the Oak body writes it, against the
				// machine's `not (here >= found)` from a branch taken the
				// other way, spell one term.
				switch {
				case left.kind == termCmp && left.width == 1 && right.kind == termConst && right.value == 1:
					out = negatedCmp(left)
				case right.kind == termCmp && right.width == 1 && left.kind == termConst && left.value == 1:
					out = negatedCmp(right)
				}
			}
			if out == nil && left.width == right.width {
				// One operand order for a product or a sum with a constant
				// — the constant first in a product (`96 * g`, as the Oak
				// body writes it, against the machine's `g * 96`), last in
				// a sum (`x + 1`); an or or xor with zero is its operand (a
				// fold from zero starts `0 | x`), an and with a full mask
				// too. The two sides then spell one term where they meant
				// one, and meet in equalTerms rather than in a diagram.
				switch {
				case t.op == "mul" && right.kind == termConst && left.kind != termConst:
					out = adaptWidth(binaryTerm("mul", right, left), t.width)
				case t.op == "add" && left.kind == termConst && right.kind != termConst:
					out = adaptWidth(binaryTerm("add", right, left), t.width)
				case (t.op == "or" || t.op == "xor") && left.kind == termConst && left.value == 0 && right.width == t.width:
					out = right
				case (t.op == "or" || t.op == "xor") && right.kind == termConst && right.value == 0 && left.width == t.width:
					out = left
				case t.op == "and" && right.kind == termConst && right.value == mask(t.width) && left.width == t.width:
					out = left
				case t.op == "and" && left.kind == termConst && left.value == mask(t.width) && right.width == t.width:
					out = right
				}
			}
			if out == nil {
				if left == t.left && right == t.right {
					out = t
				} else {
					out = binaryTerm(t.op, left, right)
					out = adaptWidth(out, t.width)
				}
			}
		case termCmp:
			if narrow := narrowComparison(t, left, right); narrow != nil {
				// An unsigned comparison of zero-extended values at a wide
				// width is the comparison at their own (`cmp x1, x0` over
				// two u32 parameters, against the Oak body's `start > n`).
				left, right = narrow.left, narrow.right
			}
			switch {
			case right.kind == termConst && right.value == 0 && t.op == "ne" && booleanValued(left, boolean):
				// A zero test of a 1/0 value is the value (the machine's
				// `cset` then `cmp #0`); of its negation, the negation.
				out = adaptWidth(left, t.width)
			case right.kind == termConst && right.value == 0 && t.op == "eq" && booleanValued(left, boolean):
				out = adaptWidth(binaryTerm("xor", left, constTerm(1, left.width)), t.width)
			case left == t.left && right == t.right:
				out = t
			default:
				out = &term{kind: termCmp, width: t.width, op: t.op, left: left, right: right}
			}
		case termIte:
			if cond.kind == termCmp && cond.width != 1 {
				// A conditional's comparison at one bit: the Oak body's
				// `start > n ? n : start` and the machine's `csel` meet
				// whatever width each compared at.
				cond = truncate(cond, 1)
			}
			budget := sameTermBudget
			if left.kind == termConst && right.kind == termConst && left.value == 1 && right.value == 0 && booleanValued(cond, boolean) {
				// `c ? 1 : 0` (the machine's cset) of a 1/0 condition is
				// the condition, at the conditional's width; `c ? 0 : 1`
				// its negation. The Oak side's `any` (an or of lane
				// tests) and the machine's (a reduction, cset, cmp) then
				// meet as one shape.
				out = adaptWidth(cond, t.width)
			} else if left.kind == termConst && right.kind == termConst && left.value == 0 && right.value == 1 && booleanValued(cond, boolean) {
				out = adaptWidth(binaryTerm("xor", cond, constTerm(1, cond.width)), t.width)
			} else if left.width == right.width && sameTerm(left, right, &budget) {
				// A conditional with one value on both arms is that value:
				// the join of two paths that agree.
				out = adaptWidth(left, t.width)
			} else if left == t.left && right == t.right && cond == t.cond {
				out = t
			} else {
				out = iteTerm(cond, left, right)
				out = adaptWidth(out, t.width)
			}
		case termSelect:
			if left == t.left {
				out = t
			} else {
				out = selectTerm(t.name, left, t.width)
			}
		default:
			out = t
		}
	}
	memo[t] = out
	return out
}

func decideEqual(fn *Function, lowering *oakLowering, asmTerm, oakTerm *term, width int, note string) Verdict {
	asmTerm = canonical(truncate(asmTerm, width))
	oakTerm = canonical(adaptWidth(oakTerm, width))
	// The input domain — every union tag one of its variants, the machine
	// not trapping — restricts the equality: it is checked on the
	// witnesses and conjoined at the bit level only once a bit differs,
	// as the reads' consistency is, since equality everywhere is equality
	// inside the domain and most bodies prove without it (wrapping both
	// terms in the domain cost the diagrams a quarter of the proofs).
	domain := lowering.domainCondition()

	// The unknowns are every parameter either side mentions: scalars, span
	// lengths, span elements, and span bases — at the width each is
	// declared (a span element's width is its element type's).
	mentioned := map[string]bool{}
	collectParams(asmTerm, mentioned)
	collectParams(oakTerm, mentioned)
	if domain != nil {
		// The domain's own unknowns (a union tag, the operands of the
		// guard the machine traps on) are variables of the decision too;
		// a parameter the blaster does not know would blast to a constant
		// and the domain to false, and every difference with it.
		collectParams(domain, mentioned)
	}
	params := map[string]int{}
	names := make([]string, 0, len(mentioned))
	for name := range mentioned {
		names = append(names, name)
		params[name] = lowering.declaredWidth(name)
	}
	sort.Strings(names)

	// Witnesses first: a disagreement is a definite mismatch regardless of
	// what normalization would say. The terms are numbered once and
	// evaluated through slices (termEvaluator); a memory built by a chain
	// of summarized stores is a large DAG, and the pass is thinned so that
	// it visits a bounded number of nodes — the witnesses are the early
	// refutation, the decision below is the proof.
	evaluator := newTermEvaluator(asmTerm, oakTerm)
	inputs := witnessInputs(names, params)
	if visits := len(evaluator.terms) * len(inputs); visits > witnessVisitBudget {
		stride := (visits + witnessVisitBudget - 1) / witnessVisitBudget
		thinned := inputs[:0:0]
		for i := 0; i < len(inputs); i += stride {
			thinned = append(thinned, inputs[i])
		}
		inputs = thinned
	}
	for _, env := range inputs {
		if !lowering.inDomain(env) || (domain != nil && domain.eval(env)&1 == 0) {
			continue
		}
		got := evaluator.evaluate(asmTerm, env)
		want := evaluator.evaluate(oakTerm, env)
		if got != want {
			return Verdict{Kind: VerdictMismatch, Message: fmt.Sprintf("asm unit %s disagrees with its Oak body at %s: asm yields %d, Oak yields %d (asm term %s; Oak term %s)", fn.Name, describeEnv(names, env), got, want, asmTerm, oakTerm)}
		}
	}
	if a, o := asmTerm.linearAt(width), oakTerm.linearAt(width); a != nil && o != nil && a.equal(o) {
		return Verdict{Kind: VerdictProven, Message: fmt.Sprintf("asm unit %s: proven equal to its Oak body (linear normal form %s)%s", fn.Name, a, note)}
	}
	if equalTerms(asmTerm, adaptWidth(oakTerm, width)) {
		// The same term on both sides (a memory both sides built from the
		// same stores, a call summary's result): no diagram needed.
		if os.Getenv("OAK_VERIFY_TRACE") != "" {
			fmt.Fprintf(os.Stderr, "verify %s: the same term on both sides (%d nodes)\n", fn.Name, termSize(asmTerm, map[*term]int{}))
		}
		return Verdict{Kind: VerdictProven, Message: fmt.Sprintf("asm unit %s: proven equal to its Oak body (the same term on both sides)%s", fn.Name, note)}
	}

	// Beyond the linear form: bit-blast both sides. Equal canonical nodes
	// for every bit is a proof at the bit level; a differing bit gives a
	// concrete counterexample; exceeding the node budget under every
	// variable order keeps the labeled evidence verdict. The orders run
	// together over the same terms and the first to decide stops the
	// others (decideLowered's pattern): a proof does not depend on the
	// order, and a body that is small under some order is decided in that
	// order's time.
	blasters := equalityBlasters(names, params, asmTerm, oakTerm)
	var stop atomic.Bool
	type attempt struct {
		verdict  Verdict
		exceeded bool
	}
	results := make(chan attempt, len(blasters))
	for _, bl := range blasters {
		bl.bdd.stop = &stop
		go func(bl *blaster) {
			verdict, exceeded := blastEqual(bl, fn, names, asmTerm, oakTerm, domain, width, note)
			results <- attempt{verdict, exceeded}
		}(bl)
	}
	for range blasters {
		if a := <-results; !a.exceeded {
			stop.Store(true)
			return a.verdict
		}
	}
	if termEquivalent(truncate(asmTerm, width), truncate(oakTerm, width), width, map[[3]any]bool{}) {
		// The same term on both sides up to the width adapters' masks (a
		// quotient times a divisor, say, whose diagram no budget affords):
		// equal by structure (asm/loops.go termEquivalent).
		return Verdict{Kind: VerdictProven, Message: fmt.Sprintf("asm unit %s: proven equal to its Oak body (the same term on both sides, beyond the diagrams' budget)%s", fn.Name, note)}
	}
	// Past the budget under every order: a case split on the largest
	// branch, each case decided with the branches it settles pruned
	// (splitDecide). A proof there is a proof; a refutation or an
	// undecided case keeps the evidence verdict, the witnesses having
	// agreed.
	if holds, decided := splitDecide(constTerm(1, 1), asmTerm, adaptWidth(oakTerm, width), lowering.declaredWidth, nil, 0); decided && holds {
		return Verdict{Kind: VerdictProven, Message: fmt.Sprintf("asm unit %s: proven equal to its Oak body at the bit level (%d-bit result, under a case split on its branch conditions)%s", fn.Name, width, note)}
	}
	return Verdict{Kind: VerdictWitnessed, Message: fmt.Sprintf("asm unit %s: agrees with its Oak body on every witness input (evidence, not proof: the bit-level decision exceeded its node budget)", fn.Name)}
}

// equalityBlasters builds the variable orders for an equality: interleaved
// always; per-parameter blocks when there is more than one root parameter;
// each leaf's bits in a block of its own when the parameters are aggregate
// leaves or span elements (a lane-wise computation resolves each lane's
// contribution as its bits are read); control bits first when a proper
// subset of the parameters decides comparisons (a table lookup at a
// symbolic index is a selection, linear once the index is read).
func equalityBlasters(names []string, widths map[string]int, asmTerm, oakTerm *term) []*blaster {
	blasters := []*blaster{newBlaster(names, widths)}
	if paramGroups(names) > 1 {
		blasters = append(blasters, newGroupedBlaster(names, widths))
	}
	leaves := 0
	for _, name := range names {
		if rootParam(name) != name {
			leaves++
		}
	}
	if leaves > 1 {
		blasters = append(blasters, newBlockedBlaster(names, widths, func(name string) string { return name }, nil, "each leaf's bits in a block"))
	}
	control := controlParams([]*term{asmTerm, oakTerm})
	if len(control) > 0 && len(control) < len(names) {
		blasters = append(blasters, newControlFirstBlaster(names, widths, control))
	}
	selectors := selectorParams([]*term{asmTerm, oakTerm})
	if len(selectors) > 0 && len(selectors) < len(names) {
		blasters = append(blasters, newSelectorFirstBlaster(names, widths, selectors))
	}
	return blasters
}

// hasUninterpreted reports a term with an uninterpreted operation node
// (termFloat: a floating-point operation or an integer quotient).
func hasUninterpreted(t *term) bool {
	seen := map[*term]bool{}
	var walk func(t *term) bool
	walk = func(t *term) bool {
		if t == nil || seen[t] {
			return false
		}
		seen[t] = true
		if t.kind == termFloat {
			return true
		}
		return walk(t.left) || walk(t.right) || walk(t.cond)
	}
	return walk(t)
}

// blastEqual decides the equality under one variable order: proof, a
// counterexample, or the budget exceeded (also when another order finished
// first and stopped this one).
func blastEqual(bl *blaster, fn *Function, names []string, asmTerm, oakTerm, domain *term, width int, note string) (Verdict, bool) {
	asmBits := bl.blast(asmTerm)
	if os.Getenv("OAK_VERIFY_TRACE") != "" {
		fmt.Fprintf(os.Stderr, "verify %s: (%s) asm: %d term nodes, %d selects, %d bdd nodes, exceeded=%v\n", fn.Name, bl.label, termSize(asmTerm, map[*term]int{}), len(bl.selects), len(bl.bdd.nodes), bl.bdd.exceeded)
	}
	oakBits := bl.blast(oakTerm)
	if os.Getenv("OAK_VERIFY_TRACE") != "" {
		fmt.Fprintf(os.Stderr, "verify %s: (%s) oak: %d term nodes, %d selects, %d bdd nodes, exceeded=%v\n", fn.Name, bl.label, termSize(oakTerm, map[*term]int{}), len(bl.selects), len(bl.bdd.nodes), bl.bdd.exceeded)
	}
	if asmBits == nil || oakBits == nil || bl.bdd.exceeded {
		return Verdict{}, true
	}
	// The input domain joins the constraint a differing bit is judged
	// under, built once with the consistency constraint.
	inDomain := func() int {
		if domain == nil {
			return bddTrue
		}
		bits := bl.blast(domain)
		if bits == nil || len(bits) == 0 {
			return bddTrue
		}
		return bits[0]
	}
	// Element reads at different index terms are independent values in the
	// diagrams (sound for a proof); a differing bit is a counterexample
	// only under the reads' functional consistency (blaster.consistency),
	// which one memory can realize. The constraint is built only once a
	// bit differs: most bodies prove node for node without it.
	cons, consBuilt := bddTrue, false
	for i := 0; i < width; i++ {
		if asmBits[i] == oakBits[i] {
			continue
		}
		if !consBuilt {
			cons, consBuilt = bl.apply(opAnd, bl.consistency(), inDomain()), true
			if bl.bdd.exceeded {
				return Verdict{}, true // the budget: another order may still decide
			}
		}
		differs := bl.apply(opAnd, cons, bl.apply(opXor, asmBits[i], oakBits[i]))
		if bl.bdd.exceeded {
			return Verdict{}, true // the budget: another order may still decide
		}
		if differs == bddFalse {
			continue // equal under every memory, though not node for node
		}
		env := bl.counterexampleOf(differs)
		if asmTerm.eval(env) == oakTerm.eval(env) && (hasUninterpreted(asmTerm) || hasUninterpreted(oakTerm)) {
			// The diagrams abstract an uninterpreted operation — a quotient
			// at another width, or one under an arm the other side folds
			// away — as an independent value, so this counterexample is the
			// abstraction's, not the terms': the evaluation agrees on it.
			// The bit level cannot decide such a pair; the verdict is the
			// witness set's (asm/floats_ops.go, docs/spec/94-assembler.md
			// §8, the thirty-first increment).
			return Verdict{}, true
		}
		return Verdict{Kind: VerdictMismatch, Message: fmt.Sprintf("asm unit %s disagrees with its Oak body at %s (bit %d differs): asm yields %d, Oak yields %d (asm term %s; Oak term %s)", fn.Name, describeEnv(names, env), i, asmTerm.eval(env), oakTerm.eval(env), asmTerm, oakTerm)}, false
	}
	order := ""
	if bl.grouped {
		order = ", " + bl.label
	}
	return Verdict{Kind: VerdictProven, Message: fmt.Sprintf("asm unit %s: proven equal to its Oak body at the bit level (%d-bit result, %d BDD nodes%s)%s", fn.Name, width, len(bl.bdd.nodes), order, note)}, false
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
	if strings.HasPrefix(name, globalParamPrefix) {
		if global, isGlobal := lo.globals[name[len(globalParamPrefix):]]; isGlobal {
			return cellWidth(global)
		}
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
		if memory, _, isElement := elementParam(name); isElement {
			if w, isLeaf := lo.recordLeafWidth(memory); isLeaf {
				return w
			}
		}
	}
	return 64
}

func describeEnv(names []string, env map[string]uint64) string {
	parts := make([]string, 0, len(names))
	for _, name := range names {
		if quantifierBound(name) {
			continue // a quantifier's binder: the body ranged over it
		}
		parts = append(parts, fmt.Sprintf("%s=%d", name, env[name]))
	}
	return strings.Join(parts, ", ")
}
