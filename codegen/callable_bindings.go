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
