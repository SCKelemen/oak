package compiler

import (
	"fmt"
	"reflect"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// lowerTextLiterals materializes UTF-8 literal bytes as static owned arrays.
// Ordinary view(&owner) lowering/checking then supplies the borrow contract;
// no general string-to-view cast or borrow escape rule is introduced.
func lowerTextLiterals(program *ast.Program) error {
	used := map[string]bool{}
	for _, stmt := range program.Statements {
		used[declarationName(stmt)] = true
	}
	if err := transformSyntax(reflect.ValueOf(program), func(expr ast.Expression) (ast.Expression, error) {
		if id, ok := expr.(*ast.Identifier); ok {
			used[id.Value] = true
		}
		return expr, nil
	}); err != nil {
		return err
	}
	literalNames := map[string]string{}
	var globals []ast.Statement
	next := 0
	err := transformSyntax(reflect.ValueOf(program), func(expr ast.Expression) (ast.Expression, error) {
		call, ok := expr.(*ast.InvocationExpression)
		if !ok {
			return expr, nil
		}
		name, ok := call.Function.(*ast.Identifier)
		if !ok || name.Value != "text_literal" {
			return expr, nil
		}
		if len(call.Arguments) != 1 {
			return nil, fmt.Errorf("text_literal requires one UTF-8 string literal")
		}
		literal, ok := call.Arguments[0].(*ast.StringLiteral)
		if !ok {
			return nil, fmt.Errorf("text_literal requires a literal; use an explicit byte view for runtime text")
		}
		owner, exists := literalNames[literal.Value]
		if !exists {
			for {
				owner = fmt.Sprintf("__oak_text_literal_%d", next)
				next++
				if !used[owner] {
					break
				}
			}
			used[owner] = true
			literalNames[literal.Value] = owner
			var source strings.Builder
			fmt.Fprintf(&source, "%s: [%d]u8", owner, len(literal.Value))
			if len(literal.Value) != 0 {
				fmt.Fprintf(&source, " = [%d]u8{", len(literal.Value))
				for i, b := range []byte(literal.Value) {
					if i > 0 {
						source.WriteString(", ")
					}
					fmt.Fprintf(&source, "%d", b)
				}
				source.WriteString("}")
			}
			tree, err := New().WithSource("text_literal.oak", source.String()).Parse().Get()
			if err != nil {
				return nil, err
			}
			globals = append(globals, tree.Root.Statements...)
		}
		tree, err := New().WithSource("text_literal.oak", "view(&"+owner+")").Parse().Get()
		if err != nil {
			return nil, err
		}
		statement, ok := tree.Root.Statements[0].(*ast.ExpressionStatement)
		if !ok {
			return nil, fmt.Errorf("text_literal: expected generated view expression")
		}
		return statement.Expression, nil
	})
	if err != nil {
		return err
	}
	program.Statements = append(globals, program.Statements...)
	return nil
}
