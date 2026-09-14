package asm

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
)

// An aggregate view (docs/spec/94-assembler.md §8, views over aggregates):
// a span or view local — `w: []T = view(&buf)`, `field: []T = subslice(v,
// start, n)` — whose owner is an aggregate local (an owned array, or a
// span parameter the call summary or the inline bound to a caller's
// array). The view names its owner, resolved through the locals at every
// use (the conditional lowering re-points locals at copies), a 32-bit
// index offset into it, and a length term: `w[i]` reads the owner's
// element under `offset + i`, `w[i] = e` writes it, `len(w)` is the
// length, and a view passed on binds the callee's parameter to the same
// view over a copy of the owner that is written back on return
// (Oak.Subslice.derived_index_in_bounds, alias_offset_assoc).
type aggView struct {
	owner  string
	offset *term // nil: the owner's start
	length *term // 32 bits
}

// viewOf recognizes an identifier naming an aggregate view.
func (lo *oakLowering) viewOf(expr ast.Expression) (aggView, bool) {
	ident, isIdent := expr.(*ast.Identifier)
	if !isIdent {
		return aggView{}, false
	}
	view, isView := lo.views[ident.Value]
	return view, isView
}

// viewOwner is the view's owner as it stands now: an array aggregate.
func (lo *oakLowering) viewOwner(view aggView) (*oakValue, string, bool) {
	local, isLocal := lo.locals[view.owner]
	if !isLocal || local.agg == nil || local.agg.typ.kind != oakArray {
		return nil, fmt.Sprintf("the view's owner %s is not an array local", view.owner), false
	}
	return local.agg, "", true
}

// viewIndex is the owner's index for the view's index.
func viewIndex(view aggView, index *term) *term {
	if view.offset == nil {
		return truncate(index, 32)
	}
	return binaryTerm("add", truncate(view.offset, 32), truncate(index, 32))
}

// declareView declares a view local over an aggregate local or another
// view: `w: []T = v` shares v's extent; `w: []T = subslice(v, start, n)`
// is v's extent from start for n, the C helper's check a trap obligation.
// It reports false when the source is neither.
func (lo *oakLowering) declareView(s *ast.VariableDeclaration, elem int64) (handled bool, reason string, ok bool) {
	name := s.Name.Value
	source := func(src string) (aggView, bool) {
		if view, isView := lo.views[src]; isView {
			return view, true
		}
		if local, isLocal := lo.locals[src]; isLocal && local.agg != nil && local.agg.typ.kind == oakArray {
			return aggView{owner: src, length: constTerm(uint64(local.agg.typ.length), 32)}, true
		}
		return aggView{}, false
	}
	fits := func(view aggView) (string, bool) {
		owner, reason, ok := lo.viewOwner(view)
		if !ok {
			return reason, false
		}
		if int64(owner.typ.elem.width) != elem*8 {
			return fmt.Sprintf("the view %s over %d-bit elements where %d-bit ones are declared", name, owner.typ.elem.width, elem*8), false
		}
		return "", true
	}
	bind := func(view aggView) (bool, string, bool) {
		if reason, ok := fits(view); !ok {
			return true, reason, false
		}
		if lo.views == nil {
			lo.views = map[string]aggView{}
		}
		delete(lo.locals, name)
		delete(lo.spans, name)
		delete(lo.spanAlias, name)
		delete(lo.spanOffset, name)
		delete(lo.spanLen, name)
		lo.views[name] = view
		return true, "", true
	}
	if src := addressOfOperand(s.Value); src != "" {
		// `w: []T = v`, `view(&buf)`, `span(&buf)`: the whole extent.
		view, isSource := source(src)
		if !isSource {
			return false, "", false
		}
		return bind(view)
	}
	sub, isSub := subsliceOf(s.Value)
	if !isSub {
		return false, "", false
	}
	base, isSource := source(sub.span)
	if !isSource {
		return false, "", false
	}
	start, reason, ok := lo.lower(sub.start, 32)
	if !ok {
		return true, reason, false
	}
	count, reason, ok := lo.lower(sub.count, 32)
	if !ok {
		return true, reason, false
	}
	lo.addTrap(cmpTerm("hi", start, base.length))
	lo.addTrap(cmpTerm("hi", count, binaryTerm("sub", base.length, start)))
	return bind(aggView{owner: base.owner, offset: viewIndex(base, start), length: count})
}

// subsliceView is `subslice(v, start, n)` over an aggregate local or a view
// as a view: the owner's extent from start for n, the guards trap
// obligations. ok is false with an empty reason when v is neither.
func (lo *oakLowering) subsliceView(sub subsliceCall) (aggView, *oakValue, string, bool) {
	var base aggView
	if view, isView := lo.views[sub.span]; isView {
		base = view
	} else if local, isLocal := lo.locals[sub.span]; isLocal && local.agg != nil && local.agg.typ.kind == oakArray {
		base = aggView{owner: sub.span, length: constTerm(uint64(local.agg.typ.length), 32)}
	} else {
		return aggView{}, nil, "", false
	}
	ownerAgg, reason, ok := lo.viewOwner(base)
	if !ok {
		return aggView{}, nil, reason, false
	}
	start, reason, ok := lo.lower(sub.start, 32)
	if !ok {
		return aggView{}, nil, reason, false
	}
	count, reason, ok := lo.lower(sub.count, 32)
	if !ok {
		return aggView{}, nil, reason, false
	}
	lo.addTrap(cmpTerm("hi", start, base.length))
	lo.addTrap(cmpTerm("hi", count, binaryTerm("sub", base.length, start)))
	return aggView{owner: base.owner, offset: viewIndex(base, start), length: count}, ownerAgg, "", true
}
