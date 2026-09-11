package compiler

import (
	"reflect"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// rewriteOperatorCalls replaces each infix expression the type checker
// resolved through an operator binding (docs/spec/10-syntax.md section 14)
// with the invocation it denotes: `a + b` bound to add becomes add(a, b),
// carrying the operator's token so diagnostics and line directives keep
// the source position. The rewrite is the whole lowering of operator
// definitions: no later phase knows they exist.
func rewriteOperatorCalls(program *ast.Program, tc *typechecker.TypeChecker) {
	visitor := &syntaxVisitor{expr: func(slot reflect.Value) {
		infix, isInfix := slot.Interface().(*ast.InfixExpression)
		if !isInfix {
			return
		}
		callee, bound := tc.OperatorCallee(infix.Token)
		if !bound {
			return
		}
		call := &ast.InvocationExpression{
			Token:     infix.Token,
			Function:  &ast.Identifier{Token: infix.Token, Value: callee},
			Arguments: []ast.Expression{infix.Left, infix.Right},
		}
		slot.Set(reflect.ValueOf(ast.Expression(call)))
	}}
	visitor.walk(reflect.ValueOf(program), false)
}
