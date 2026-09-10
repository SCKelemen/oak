package borrowchecker

// Region-indexed borrowed returns, increment 1 (docs/spec/50-borrowing.md
// section 8c): a function whose return type is a read-only view and which
// has exactly one view parameter of the same element type returns a view
// borrowed from that parameter. The parameter's owner outlives the call, so
// this is `Oak.Escape.return_param_borrow_wf`, the safe escape; a returned
// borrow of anything else — a local owner, another parameter, an unknown
// source — is OAK-B0113. At the caller the result is a reborrow of the
// argument (`Oak.Escape.reborrow_wf`): same owner, read-only, bound at the
// caller's block depth, so every owner-exclusivity and lexical-scope rule
// applies to it as to a view the caller took directly.

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// regionCandidate is the elision rule: a `[]T` return and exactly one `[]T`
// parameter with the same element type name that parameter as the region.
// Variadic functions have no candidate — the bundled trailing view is
// caller-stack storage that lives only for the call.
func regionCandidate(fn *typechecker.FunctionType) (int, bool) {
	if fn == nil || fn.Variadic {
		return -1, false
	}
	ret, isArray := fn.ReturnType.(*typechecker.ArrayType)
	if !isArray || !ret.IsSlice || ret.ElementType == nil {
		return -1, false
	}
	candidate := -1
	for i, param := range fn.Parameters {
		p, ok := param.(*typechecker.ArrayType)
		if !ok || !p.IsSlice || p.ElementType == nil || !p.ElementType.Equals(ret.ElementType) {
			continue
		}
		if candidate >= 0 {
			return -1, false
		}
		candidate = i
	}
	return candidate, candidate >= 0
}

// returnContract is the region a function's returned view must come from.
type returnContract struct {
	function string
	param    string
	owner    string // the parameter's synthetic owner
	checked  bool
}

// functionType looks up a declared function's checked type.
func functionType(name string, env *typechecker.TypeEnvironment) *typechecker.FunctionType {
	scheme, ok := env.Get(name)
	if !ok || scheme == nil {
		return nil
	}
	fn, isFn := scheme.Type.(*typechecker.FunctionType)
	if !isFn {
		return nil
	}
	return fn
}

// returnContractFor computes a function's contract, or nil when its
// signature is not region-indexed under the elision rule.
func returnContractFor(stmt *ast.FunctionStatement, env *typechecker.TypeEnvironment) *returnContract {
	if stmt == nil || stmt.Name == nil {
		return nil
	}
	fn := functionType(stmt.Name.Value, env)
	idx, ok := regionCandidate(fn)
	if !ok || idx >= len(stmt.Parameters) || stmt.Parameters[idx].Name == nil {
		return nil
	}
	param := stmt.Parameters[idx].Name.Value
	return &returnContract{function: stmt.Name.Value, param: param, owner: "$parameter:" + param}
}

// checkReturnedProvenance is the callee's obligation: the result expression
// must be a borrow of the contract's parameter. Runs while the body's
// borrows are still live.
func (bc *BorrowChecker) checkReturnedProvenance(result ast.Expression, contract *returnContract, env *typechecker.TypeEnvironment) {
	if contract == nil || contract.checked {
		return
	}
	contract.checked = true
	if result == nil {
		return
	}
	owner, ok := bc.provenanceOwner(result, env)
	if ok && owner == contract.owner {
		return
	}
	d := bc.reportBorrow(result, CodeReturnedBorrowRegion,
		fmt.Sprintf("function %q returns a view that does not borrow from its parameter %q", contract.function, contract.param))
	switch {
	case !ok:
		d.AddNote("the returned expression is not a view, subslice, slice, or conditional over one whose source the checker can trace")
	case owner == "":
		d.AddNote("the returned view has no tracked owner")
	default:
		d.AddNote(fmt.Sprintf("the returned view borrows %s, which does not outlive the call", describeOwner(owner)))
	}
	d.AddHelp(fmt.Sprintf("return a view of %q (the parameter, a subslice of it, or a local bound from it), or return owned data", contract.param))
}

// describeOwner renders a synthetic or real owner name for a diagnostic.
func describeOwner(owner string) string {
	const parameterPrefix = "$parameter:"
	if len(owner) > len(parameterPrefix) && owner[:len(parameterPrefix)] == parameterPrefix {
		return fmt.Sprintf("parameter %q", owner[len(parameterPrefix):])
	}
	if owner != "" && owner[0] == '$' {
		return "a temporary"
	}
	return fmt.Sprintf("local owner %q", owner)
}

// provenanceOwner traces a view-valued expression to the owner it borrows:
// a tracked binding, `view(&owner)`, a subslice or reinterpretation of a
// traced view, a slice expression over one, a conditional whose arms agree,
// a block's result, or a region-indexed call traced through its candidate
// argument. Reports false when the source cannot be traced.
func (bc *BorrowChecker) provenanceOwner(expr ast.Expression, env *typechecker.TypeEnvironment) (string, bool) {
	switch e := expr.(type) {
	case *ast.Identifier:
		if info, tracked := bc.activeBorrows[e.Value]; tracked {
			return info.owner, true
		}
		if _, isOwner := bc.ownerStates[e.Value]; isOwner {
			return e.Value, true
		}
		return "", false
	case *ast.SliceExpression:
		if ident, isIdent := e.Seq.(*ast.Identifier); isIdent {
			if _, isOwner := bc.ownerStates[ident.Value]; isOwner {
				return ident.Value, true
			}
		}
		return bc.provenanceOwner(e.Seq, env)
	case *ast.BlockExpression:
		return bc.provenanceOwner(e.Result(), env)
	case *ast.MatchExpression:
		if len(e.Arms) == 0 {
			return "", false
		}
		owner := ""
		for i, arm := range e.Arms {
			armOwner, ok := bc.provenanceOwner(arm.Body, env)
			if !ok {
				return "", false
			}
			if i == 0 {
				owner = armOwner
			} else if armOwner != owner {
				return "", false
			}
		}
		return owner, true
	case *ast.InvocationExpression:
		callee, isIdent := e.Function.(*ast.Identifier)
		if !isIdent {
			return "", false
		}
		switch callee.Value {
		case "view", "span":
			if len(e.Arguments) == 1 {
				if owner := bc.extractOwnerName(e.Arguments[0]); owner != "" {
					return owner, true
				}
			}
			return "", false
		case "subslice", "view_as":
			if len(e.Arguments) >= 1 {
				return bc.provenanceOwner(e.Arguments[0], env)
			}
			return "", false
		}
		if idx, ok := regionCandidate(functionType(callee.Value, env)); ok && idx < len(e.Arguments) {
			return bc.provenanceOwner(e.Arguments[idx], env)
		}
		return "", false
	}
	return "", false
}

// bindRegionCall is the caller's side: when a call to a region-indexed
// function initializes a binding, the binding becomes a read-only reborrow
// of the argument in the region position. An argument whose view the
// checker cannot trace to a tracked read-only source fails closed.
func (bc *BorrowChecker) bindRegionCall(call *ast.InvocationExpression, callee string, targetVar string, env *typechecker.TypeEnvironment) bool {
	idx, ok := regionCandidate(functionType(callee, env))
	if !ok || idx >= len(call.Arguments) {
		return false
	}
	if bc.bindDerivedView(targetVar, call.Arguments[idx], call, env) {
		return true
	}
	d := bc.reportBorrow(call.Arguments[idx], CodeReturnedBorrowRegion,
		fmt.Sprintf("cannot bind %q: the region argument of %q is not a traceable read-only view", targetVar, callee))
	d.AddNote("the result of a region-indexed call borrows the argument's owner; the argument must be a tracked view binding, view(&owner), a subslice or slice of one, or another region-indexed call")
	d.AddHelp("bind the view first, then pass the binding")
	return true
}

// bindDerivedView makes targetVar a read-only borrow of the owner that
// expr borrows. Regions are not propagated (unknown, fail-closed for
// disjointness), which is exact for read-only borrows.
func (bc *BorrowChecker) bindDerivedView(targetVar string, expr ast.Expression, origin ast.Node, env *typechecker.TypeEnvironment) bool {
	switch e := expr.(type) {
	case *ast.Identifier:
		info, tracked := bc.activeBorrows[e.Value]
		if !tracked || info.kind != BorrowView {
			return false
		}
		bc.createSubsliceWithRegion(e.Value, targetVar, nil, origin)
		return true
	case *ast.SliceExpression:
		if ident, isIdent := e.Seq.(*ast.Identifier); isIdent {
			if _, isOwner := bc.ownerStates[ident.Value]; isOwner {
				bc.createViewBorrowWithRegion(ident.Value, targetVar, nil, origin)
				return true
			}
		}
		return bc.bindDerivedView(targetVar, e.Seq, origin, env)
	case *ast.InvocationExpression:
		callee, isIdent := e.Function.(*ast.Identifier)
		if !isIdent {
			return false
		}
		switch callee.Value {
		case "view":
			if len(e.Arguments) != 1 {
				return false
			}
			owner := bc.extractOwnerName(e.Arguments[0])
			if owner == "" {
				return false
			}
			bc.createViewBorrowWithRegion(owner, targetVar, bc.wholeOwnerRegion(owner, env), origin)
			return true
		case "subslice", "view_as":
			if len(e.Arguments) < 1 {
				return false
			}
			return bc.bindDerivedView(targetVar, e.Arguments[0], origin, env)
		}
		if idx, ok := regionCandidate(functionType(callee.Value, env)); ok && idx < len(e.Arguments) {
			return bc.bindDerivedView(targetVar, e.Arguments[idx], origin, env)
		}
		return false
	}
	return false
}
