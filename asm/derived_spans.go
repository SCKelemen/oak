package asm

import "github.com/SCKelemen/oak/ast"

// subsliceCall is `subslice(span, start, count)` over a named span.
type subsliceCall struct {
	span         string
	start, count ast.Expression
}

// subsliceOf recognizes a subslice argument over a named span.
func subsliceOf(arg ast.Expression) (subsliceCall, bool) {
	call, isCall := arg.(*ast.InvocationExpression)
	if !isCall || len(call.Arguments) != 3 {
		return subsliceCall{}, false
	}
	fn, isIdent := call.Function.(*ast.Identifier)
	src, srcIsIdent := call.Arguments[0].(*ast.Identifier)
	if !isIdent || fn.Value != "subslice" || !srcIsIdent {
		return subsliceCall{}, false
	}
	return subsliceCall{span: src.Value, start: call.Arguments[1], count: call.Arguments[2]}, true
}

// Derived spans in the verifier (docs/spec/94-assembler.md §8, derived
// spans). `subslice(v, start, n)` yields the pair {&v + start·elem, n}: a
// base that is the span's base plus scaled index terms and constants
// (nested, when a derived span is re-sliced), and a length that is any
// 32-bit term. spanAddressOf flattens such a base into the root span and
// the sum of its indices, so a load or store through it — with or without
// a further scaled index in the addressing mode — reaches the element
// start + i of the root span on either lane; the call summary and the Oak
// side's inline bind a callee's span parameter to a derived span as an
// alias of the root with an index offset and a length term (spanIndex,
// spanLenTerm), so the callee's reads, writes, and `len` translate to the
// root (Oak.Subslice.derived_index_in_bounds, reslice_in_bounds).

// spanAddressOf reads a term as an address into a span of elem-byte
// elements: the span's base parameter, plus any number of scaled 32-bit
// index terms (`idx << s` with 2^s = elem, or a bare term when elem is 1)
// and constants that are whole elements. The index is the sum at 32 bits;
// nil when the address is the base itself.
func spanAddressOf(t *term, elem int64) (param string, index *term, ok bool) {
	if elem <= 0 {
		return "", nil, false
	}
	var leaves []*term
	var walk func(*term) bool
	walk = func(u *term) bool {
		if u.kind == termBinary && u.op == "add" {
			return walk(u.left) && walk(u.right)
		}
		leaves = append(leaves, u)
		return len(leaves) <= 8
	}
	if !walk(t) {
		return "", nil, false
	}
	var constant int64
	for _, leaf := range leaves {
		switch {
		case leaf.kind == termParam && spanBaseParam(leaf) != "":
			if param != "" {
				return "", nil, false // two bases
			}
			param = spanBaseParam(leaf)
		case leaf.kind == termConst:
			if int64(leaf.value)%elem != 0 {
				return "", nil, false
			}
			constant += int64(leaf.value) / elem
		case leaf.kind == termBinary && leaf.op == "shl" && leaf.right.kind == termConst && int64(1)<<leaf.right.value == elem:
			index = addIndex(index, truncate(leaf.left, 32))
		case elem == 1:
			index = addIndex(index, truncate(leaf, 32))
		default:
			return "", nil, false
		}
	}
	if param == "" {
		return "", nil, false
	}
	if constant != 0 {
		index = addIndex(index, constTerm(uint64(constant)&mask(32), 32))
	}
	return param, index, true
}

// spanBaseParam names the span a base term is the address of (`&v`), or "".
func spanBaseParam(t *term) string {
	if name, offset, isBase := spanBaseOf(t); isBase && offset == 0 && t.kind == termParam {
		return name
	}
	return ""
}

// addIndex sums two 32-bit index terms, either possibly nil.
func addIndex(a, b *term) *term {
	switch {
	case a == nil:
		return b
	case b == nil:
		return a
	}
	return binaryTerm("add", a, b)
}

// spanIndex translates a callee's index into an aliased span parameter to
// the root span's index: the alias's offset added, when the parameter
// stands for a derived span.
func (lo *oakLowering) spanIndex(name string, index *term) *term {
	if offset, derived := lo.spanOffset[name]; derived {
		return binaryTerm("add", truncate(offset, 32), truncate(index, 32))
	}
	return index
}

// spanLenTerm is `len(v)` over a span parameter: the derived span's length
// term when the parameter stands for one, else the root's length parameter.
func (lo *oakLowering) spanLenTerm(name string, width int) *term {
	if length, derived := lo.spanLen[name]; derived {
		return adaptWidth(length, width)
	}
	return adaptWidth(paramTerm(spanLenName(lo.spanRoot(name)), 32), width)
}
