package compiler

import (
	"reflect"

	"github.com/SCKelemen/oak/ast"
)

// lowerStdlibFluent rewrites the bootstrap builder's fluent spellings into
// ordinary free calls before type, borrow and discipline checking. The receiver
// appears exactly once as the first argument. This is static sugar, not dynamic
// method lookup, and is enabled only by import(std).
func lowerStdlibFluent(program *ast.Program) error {
	names := map[string]bool{"append_bytes": true, "append_byte": true, "finish_bytes": true, "append_text": true, "append_rune": true, "append_u64": true, "finish_text": true}
	return transformSyntax(reflect.ValueOf(program), func(expr ast.Expression) (ast.Expression, error) {
		call, ok := expr.(*ast.InvocationExpression)
		if !ok {
			return expr, nil
		}
		member, ok := call.Function.(*ast.IndexExpression)
		if !ok || !member.Dot {
			return expr, nil
		}
		name, ok := member.Index.(*ast.Identifier)
		if !ok || !names[name.Value] {
			return expr, nil
		}
		lowered := *call
		lowered.Function = &ast.Identifier{Token: name.Token, Value: name.Value}
		lowered.Arguments = append([]ast.Expression{member.Left}, call.Arguments...)
		return &lowered, nil
	})
}
