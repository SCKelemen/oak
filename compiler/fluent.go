package compiler

import (
	"fmt"
	"reflect"

	"github.com/SCKelemen/oak/ast"
)

// lowerStdlibFluent rewrites the bootstrap builder's fluent spellings into
// ordinary free calls before type, borrow and discipline checking. The receiver
// appears exactly once as the first argument. This is static sugar, not dynamic
// method lookup; names resolve through the loaded library (compiler/stdlib.go).
func lowerStdlibFluent(program *ast.Program, names libraryNames) error {
	fluent := map[string]bool{"append_bytes": true, "append_byte": true, "finish_bytes": true, "append_text": true, "append_rune": true, "append_u64": true, "finish_text": true, "append_json_string": true, "finish_json": true}
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
		if !ok || !fluent[name.Value] {
			return expr, nil
		}
		target, err := names.resolve(name.Value)
		if err != nil {
			return nil, fmt.Errorf("fluent call .%s: %w", name.Value, err)
		}
		lowered := *call
		lowered.Function = &ast.Identifier{Token: name.Token, Value: target}
		lowered.Arguments = append([]ast.Expression{member.Left}, call.Arguments...)
		return &lowered, nil
	})
}
