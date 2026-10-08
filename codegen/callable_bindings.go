package codegen

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// inferredCallableDeclaration preserves the checked signature of inferred
// function values. The initializer's syntax need not be a function literal:
// it may be a named function, another binding, or a record-field projection.
// Work on an emitter-private copy; do not change checked source authority.
func (cg *CodeGenerator) inferredCallableDeclaration(stmt *ast.VariableDeclaration, tc *typechecker.TypeChecker) *ast.VariableDeclaration {
	if stmt.Type != nil || tc == nil {
		return stmt
	}
	checked := tc.Env().CheckedDeclarationType(stmt)
	if checked == nil {
		checked = tc.Env().CheckedExpressionType(stmt.Value)
	}
	if checked == nil {
		if tok, ok := ast.ExpressionToken(stmt.Value); ok {
			checked, _ = tc.ExpressionTypeAt(tok)
		}
	}
	if _, callable := checked.(*typechecker.FunctionType); !callable {
		return stmt
	}
	signature, ok := callableTypeExpression(checked)
	if !ok {
		cg.globalErrors = append(cg.globalErrors, fmt.Errorf("codegen: inferred callable %s has no supported C signature", stmt.Name.Value))
		return stmt
	}
	copy := *stmt
	copy.Type = signature
	return &copy
}

// Keep this conversion separate from scalar sequencing temporaries: a C
// function-pointer declarator cannot be spelled as a scalar type prefix.
func callableTypeExpression(typ typechecker.Type) (ast.Expression, bool) {
	switch t := typ.(type) {
	case *typechecker.UnitType:
		return &ast.Identifier{Value: "()"}, true
	case *typechecker.FunctionType:
		result, ok := callableTypeExpression(t.ReturnType)
		if !ok {
			return nil, false
		}
		fn := &ast.FunctionTypeExpression{Return: result}
		for _, parameter := range t.Parameters {
			p, ok := callableTypeExpression(parameter)
			if !ok {
				return nil, false
			}
			fn.Parameters = append(fn.Parameters, p)
		}
		return fn, true
	default:
		return checkedTypeExpression(typ)
	}
}

// Variadic is a property of the checked function value, not of its name.
// The C pointer signature already contains the final view parameter; calls
// through aliases must construct that view just like a direct call does.
func (cg *CodeGenerator) emitIndirectVariadicCall(call *ast.InvocationExpression, tc *typechecker.TypeChecker) bool {
	if tc == nil {
		return false
	}
	checked := tc.Env().CheckedExpressionType(call.Function)
	if checked == nil {
		if tok, ok := ast.ExpressionToken(call.Function); ok {
			checked, _ = tc.ExpressionTypeAt(tok)
		}
	}
	fn, ok := checked.(*typechecker.FunctionType)
	if !ok || !fn.Variadic {
		return false
	}
	if len(fn.Parameters) == 0 {
		cg.globalErrors = append(cg.globalErrors, fmt.Errorf("codegen: variadic callable has no tail parameter"))
		return true
	}
	fixed := len(fn.Parameters) - 1
	tail, ok := fn.Parameters[fixed].(*typechecker.ArrayType)
	if !ok || !tail.IsSlice {
		cg.globalErrors = append(cg.globalErrors, fmt.Errorf("codegen: variadic callable tail is not a view"))
		return true
	}
	element, ok := callableTypeExpression(tail.ElementType)
	if !ok {
		cg.globalErrors = append(cg.globalErrors, fmt.Errorf("codegen: variadic callable element has no supported C type"))
		return true
	}
	cg.emitExpressionFragment(call.Function, tc)
	cg.emitVariadicArguments(fixed, cg.parseTypeExpression(element), call, tc)
	return true
}
