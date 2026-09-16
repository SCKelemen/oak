package asm

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
)

// frameBorrow is a callee's span or view parameter bound, for the call
// summary, to the contents of the caller's owned frame array
// (docs/spec/94-assembler.md §8, span arguments over owned arrays;
// Oak.SpanArguments): the array at the entry-relative address addr, n
// elements of elem bytes, and whether the callee may write through it
// (a `[*]T` parameter).
type frameBorrow struct {
	param    string
	addr     int64
	n, elem  int64
	writable bool
	// leaves: the element's scalar leaves when the elements are records
	// (nil for scalars) — each element's leaf lives at its offset inside
	// the element, read and written back at the leaf's width.
	leaves []compositeLeaf
}

// leafBytes is the frame bytes a leaf occupies: a Bool leaf is its 4-byte
// C enum cell, every other its width.
func leafBytes(leaf compositeLeaf) int64 {
	if leaf.width == 1 {
		return 4
	}
	return int64(leaf.width+7) / 8
}

// frameArrayBudget bounds the array a summary binds element by element.
const frameArrayBudget = 4096

// frameArrayArgument binds a span argument that is `span(&buf)` or
// `view(&buf)` over the caller's owned frame array — its base a frame
// address (`add xN, sp, #off`, `addi rN, sp, off`), its length a
// constant — as the Oak side's inline binds it (inlineCall): the callee's
// parameter becomes an aggregate local holding the array's elements read
// from the frame slots, so the body's element reads and writes, its
// `len`, and its data-dependent loops (which carry the leaves as fresh
// symbols) are the aggregate's; a writable span's final contents are
// stored back into the slots after the body (frameBorrow.writeBack). The
// array must lie below the frame's unknown region: a store at a
// data-dependent index left those slots opaque.
func (x *pathExecutor) frameArrayArgument(state *symbolicState, lo *oakLowering, callee, param string, paramType ast.Expression, elem int64, base, length *term, bound bool) (frameBorrow, string, bool) {
	refuse := func(why string) (frameBorrow, string, bool) {
		return frameBorrow{}, fmt.Sprintf("a call to %s: the span argument %s is not one of the caller's span parameters passed whole (%s)", callee, param, why), false
	}
	if !bound {
		return refuse("unbound register read")
	}
	addr, isFrame := frameAddressOf(base)
	if !isFrame {
		addr, isFrame = rvFrameAddrOf(base)
	}
	if !isFrame {
		return refuse("its base is not a frame address")
	}
	if length.kind != termConst {
		return refuse("its length is not a constant")
	}
	n := int64(length.value)
	if n < 0 || elem <= 0 || n*elem > frameArrayBudget {
		return refuse("an array beyond the summary's budget")
	}
	if state.unknownFrom != nil && addr+n*elem > *state.unknownFrom {
		return refuse("the array's contents follow a store at a data-dependent index")
	}
	spanType, isSpan := paramType.(*ast.IndexExpression)
	if !isSpan {
		return refuse("a parameter that is not a span")
	}
	elemType, ok := lo.oakTypeOf(spanType.Left)
	if !ok {
		return refuse("elements without a model")
	}
	agg := &oakValue{typ: &oakType{kind: oakArray, elem: elemType, length: n}, elems: make([]*oakValue, n)}
	_, writable, _ := spanShapeIn(paramType, x.fn.Composites)
	if elemType.kind != oakScalar {
		// An array of records (`span(&stages)` over `stages: [2]Stage`):
		// each element's leaves are read from the frame at their offsets
		// inside the element (the layout the checker and the backend
		// share, compositeLeaves), as frameRecordArgument reads one
		// record; a writable span's final leaves are stored back the same
		// way (frameBorrow.writeBack).
		leaves, _, okLeaves := compositeLeaves(x.fn.Composites, typeText(spanType.Left), "", 0, nil)
		comp, isComposite := x.fn.Composites[typeText(spanType.Left)]
		if !okLeaves || !isComposite || comp.Size != elem {
			return refuse("elements without a layout at the span's stride")
		}
		byName := map[string]compositeLeaf{}
		for _, leaf := range leaves {
			byName[leaf.name] = leaf
		}
		for i := int64(0); i < n; i++ {
			base := addr + i*elem
			missing := ""
			value, okValue := aggregateFrom(elemType, "", func(name string, leafType *oakType) *term {
				leaf, has := byName[name]
				if !has {
					missing = name
					return nil
				}
				slot, held := state.loadSlot(base+leaf.offset, leafBytes(leaf))
				if !held {
					missing = name
					return nil
				}
				return truncate(slot, leafType.width)
			})
			if !okValue {
				return refuse(fmt.Sprintf("element %d's leaf %s is not in the frame", i, missing))
			}
			agg.elems[i] = value
		}
		lo.locals[param] = &oakLocal{agg: agg}
		return frameBorrow{param: param, addr: addr, n: n, elem: elem, writable: writable, leaves: leaves}, "", true
	}
	if int64(elemType.width) != elem*8 {
		return refuse("elements without a scalar model at the span's width")
	}
	for i := int64(0); i < n; i++ {
		value, has := state.loadSlot(addr+i*elem, elem)
		if !has {
			return refuse(fmt.Sprintf("element %d is not in the frame", i))
		}
		agg.elems[i] = &oakValue{typ: elemType, scalar: truncate(value, elemType.width)}
	}
	lo.locals[param] = &oakLocal{agg: agg}
	return frameBorrow{param: param, addr: addr, n: n, elem: elem, writable: writable}, "", true
}

// writeBack stores a writable borrow's final contents into the caller's
// frame slots, element by element (the conditional lowering re-points
// locals at copies, so the final aggregate is read from the lowering's
// locals, as the Oak side's inline reads it).
func (b frameBorrow) writeBack(state *symbolicState, lo *oakLowering) (string, bool) {
	if !b.writable {
		return "", true
	}
	final, has := lo.locals[b.param]
	if !has || final.agg == nil || int64(len(final.agg.elems)) != b.n {
		return fmt.Sprintf("the span parameter %s lost its array", b.param), false
	}
	for i, element := range final.agg.elems {
		if element == nil {
			return fmt.Sprintf("the span parameter %s has an element without a value", b.param), false
		}
		if b.leaves != nil {
			// A record element: each leaf at its offset, a Bool leaf
			// zero-extended into its 4-byte cell (as a record result is
			// stored into the caller's area).
			terms := map[string]*term{}
			leafTerms(element, "", terms)
			base := b.addr + int64(i)*b.elem
			for _, leaf := range b.leaves {
				t, has := terms[leaf.name]
				if !has {
					continue // a union payload's leaf the value does not carry
				}
				state.storeSlot(base+leaf.offset, zeroExtend(adaptWidth(t, leaf.width), int(leafBytes(leaf))*8), leafBytes(leaf))
			}
			continue
		}
		if element.scalar == nil {
			return fmt.Sprintf("the span parameter %s has an element without a value", b.param), false
		}
		state.storeSlot(b.addr+int64(i)*b.elem, truncate(element.scalar, int(b.elem)*8), b.elem)
	}
	return "", true
}
