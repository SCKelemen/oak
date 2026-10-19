package compiler

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
)

// validatePublicCallableRows checks source type annotations before checked
// function types erase callable rows. It follows local transparent aliases,
// never opaque representations, and does not inspect function bodies or their
// outer effects/forbids clauses. Callable-row API identity remains unsupported.
func validatePublicCallableRows(program *ast.Program) error {
	aliases := make(map[string]*ast.ADTType)
	for _, statement := range program.Statements {
		declaration, ok := statement.(*ast.ADTType)
		if !ok || declaration.Name == nil || declaration.Opaque || len(declaration.Variants) != 1 {
			continue
		}
		variant := declaration.Variants[0]
		if variant != nil && variant.Name != nil && variant.Name.Value == declaration.Name.Value && variant.Payload != nil && variant.Literal == nil {
			aliases[declaration.Name.Value] = declaration
		}
	}
	boundNames := func(parameters []*ast.TypeParameter) map[string]bool {
		names := make(map[string]bool, len(parameters))
		for _, parameter := range parameters {
			if parameter != nil && parameter.Name != nil {
				names[parameter.Name.Value] = true
			}
		}
		return names
	}
	visiting := make(map[string]bool)
	var check func(ast.Expression, map[string]bool) error
	check = func(expression ast.Expression, bound map[string]bool) error {
		switch value := expression.(type) {
		case *ast.Identifier:
			if bound[value.Value] {
				return nil
			}
			if alias, ok := aliases[value.Value]; ok {
				if visiting[value.Value] {
					return fmt.Errorf("cyclic type alias %q in public API", value.Value)
				}
				visiting[value.Value] = true
				// An alias's parameters belong to its own lexical scope, not
				// the caller's potentially shadowing type parameters.
				err := check(alias.Variants[0].Payload, boundNames(alias.TypeParams))
				delete(visiting, value.Value)
				return err
			}
		case *ast.FunctionTypeExpression:
			if value.EffectsDeclared || len(value.Effects) != 0 {
				return fmt.Errorf("API snapshots do not yet cover callable effect rows")
			}
			for _, parameter := range value.Parameters {
				if err := check(parameter, bound); err != nil {
					return err
				}
			}
			return check(value.Return, bound)
		case *ast.IndexExpression:
			if err := check(value.Left, bound); err != nil {
				return err
			}
			if value.TypeForm == ast.IndexGenericType {
				return check(value.Index, bound)
			}
		case *ast.RecordLiteral:
			for _, field := range value.OrderedFields() {
				if err := check(field.Value, bound); err != nil {
					return err
				}
			}
		case *ast.PrefixExpression:
			return check(value.Right, bound)
		case *ast.InfixExpression:
			if err := check(value.Left, bound); err != nil {
				return err
			}
			return check(value.Right, bound)
		}
		return nil
	}
	checkFunction := func(function *ast.FunctionStatement) error {
		bound := boundNames(function.TypeParams)
		if function.Receiver != nil {
			if err := check(function.Receiver.Type, bound); err != nil {
				return err
			}
		}
		for _, parameter := range function.Parameters {
			if err := check(parameter.Type, bound); err != nil {
				return err
			}
		}
		return check(function.ReturnType, bound)
	}
	for _, statement := range program.Statements {
		switch declaration := statement.(type) {
		case *ast.FunctionStatement:
			if declaration.Exported {
				if err := checkFunction(declaration); err != nil {
					return fmt.Errorf("public function %q: %w", declaration.Name.Value, err)
				}
			}
		case *ast.VariableDeclaration:
			if declaration.Exported {
				if err := check(declaration.Type, nil); err != nil {
					return fmt.Errorf("public value %q: %w", declaration.Name.Value, err)
				}
			}
		case *ast.ADTType:
			if declaration.Exported && !declaration.Opaque {
				bound := boundNames(declaration.TypeParams)
				for _, variant := range declaration.Variants {
					for _, expression := range []ast.Expression{variant.Payload, variant.Result, variant.Literal} {
						if err := check(expression, bound); err != nil {
							return fmt.Errorf("public type %q: %w", declaration.Name.Value, err)
						}
					}
				}
			}
		case *ast.InterfaceType:
			if declaration.Exported {
				bound := boundNames(declaration.TypeParams)
				for _, method := range declaration.Methods {
					expressions := []ast.Expression{method.ReceiverType, method.ReturnType}
					for _, parameter := range method.Parameters {
						expressions = append(expressions, parameter.Type)
					}
					for _, expression := range expressions {
						if err := check(expression, bound); err != nil {
							return fmt.Errorf("public interface %q: %w", declaration.Name.Value, err)
						}
					}
				}
			}
		}
	}
	return nil
}
