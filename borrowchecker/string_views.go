package borrowchecker

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

func literalStringResult(expr ast.Expression) bool {
	switch value := expr.(type) {
	case *ast.StringLiteral:
		return true
	case *ast.BlockExpression:
		return literalStringResult(value.Result())
	case *ast.MatchExpression:
		if len(value.Arms) == 0 {
			return false
		}
		for _, arm := range value.Arms {
			if !literalStringResult(arm.Body) {
				return false
			}
		}
		return true
	}
	return false
}

func isDirectBorrowType(typ typechecker.Type) bool {
	switch t := typ.(type) {
	case *typechecker.StringType:
		return true
	case *typechecker.ArrayType:
		return t.IsSlice || t.IsSpan
	}
	return false
}

// Parameters borrow storage owned by the caller. Their synthetic owners cannot
// name Oak variables and are discarded with the function's borrow state.
func (bc *BorrowChecker) registerBorrowParameter(name string, typ typechecker.Type, origin ast.Node) {
	if !isDirectBorrowType(typ) {
		return
	}
	owner := "$parameter:" + name
	if array, ok := typ.(*typechecker.ArrayType); ok && array.IsSpan {
		bc.createSpanBorrowWithRegion(owner, name, nil, origin)
	} else {
		bc.createViewBorrowWithRegion(owner, name, nil, origin)
	}
}

// isStringViewConversion recognizes `str_bytes(x)`: the bridge whose result
// may stand directly as a call argument (F9). `str_from_utf8` yields a
// string, which is bound like any other value.
func isStringViewConversion(call *ast.InvocationExpression) bool {
	name, ok := call.Function.(*ast.Identifier)
	return ok && name.Value == "str_bytes" && len(call.Arguments) == 1
}

// Both bridges derive an immutable borrow from the same backing owner. Binding
// the source and result explicitly keeps the lexical lifetime visible; temporary
// and block-result conversions are rejected until expression regions exist.
func (bc *BorrowChecker) checkStringViewCall(call *ast.InvocationExpression, env *typechecker.TypeEnvironment, target string) {
	if len(call.Arguments) != 1 {
		return // The typechecker owns arity diagnostics.
	}
	if target == "" {
		bc.reportBorrow(call, CodeBorrowEscape, "string view conversion requires an explicit new binding")
		return
	}
	if _, literal := call.Arguments[0].(*ast.StringLiteral); literal {
		if name, ok := call.Function.(*ast.Identifier); ok && name.Value == "str_bytes" {
			bc.createViewBorrowWithRegion("$literal:"+target, target, nil, call)
			return
		}
	}
	source, named := call.Arguments[0].(*ast.Identifier)
	if named {
		if info, tracked := bc.activeBorrows[source.Value]; tracked && info.kind == BorrowView {
			bc.createSubsliceWithRegion(source.Value, target, info.region, call)
			return
		}
	}
	bc.reportBorrow(call.Arguments[0], CodeBorrowEscape, "string view conversion requires a named, tracked read-only source")
}
