package compiler

import (
	"fmt"
	"strconv"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/semir"
	"github.com/SCKelemen/oak/token"
)

// TypeModel projects the currently implemented Oak type declarations into the
// Semantic IR after ordinary semantic analysis succeeds.
//
// This is intentionally narrower than the eventual full SemanticIR stage: it
// lowers ADTs, records, aliases, generics, and interfaces, while executable
// function bodies remain in the existing typed AST/lowering pipeline.
func (comp Compilation) TypeModel() Stage[*semir.Module] {
	return comp.Check().Then(func(model *SemanticModel) (*semir.Module, error) {
		module, err := BuildTypeModel(model.Tree.Root)
		if err != nil {
			return nil, fmt.Errorf("semantic type projection failed: %w", err)
		}
		return module, nil
	})
}

// BuildTypeModel projects type-level declarations from an already parsed Oak
// program. It never invents representation information that the AST cannot
// justify. Record source order is preserved; concrete ABI offsets remain unknown
// until a representation pass has all required target facts.
func BuildTypeModel(program *ast.Program) (*semir.Module, error) {
	module := &semir.Module{}
	for _, statement := range program.Statements {
		switch declaration := statement.(type) {
		case *ast.ADTType:
			definition, err := buildADTDefinition(declaration)
			if err != nil {
				return nil, err
			}
			module.Definitions = append(module.Definitions, definition)
		case *ast.InterfaceType:
			definition, err := buildInterfaceDefinition(declaration)
			if err != nil {
				return nil, err
			}
			module.Definitions = append(module.Definitions, definition)
		}
	}
	if err := module.Validate(); err != nil {
		return nil, err
	}
	return module, nil
}

func buildADTDefinition(declaration *ast.ADTType) (semir.Definition, error) {
	if declaration == nil || declaration.Name == nil || declaration.Name.Value == "" {
		return semir.Definition{}, fmt.Errorf("ADT declaration has no name")
	}

	parameters, err := buildTypeParameters(declaration.TypeParams)
	if err != nil {
		return semir.Definition{}, fmt.Errorf("type %q: %w", declaration.Name.Value, err)
	}

	definition := semir.Definition{Name: declaration.Name.Value}
	definition.Type.Parameters = parameters

	if len(declaration.Variants) == 1 {
		variant := declaration.Variants[0]
		if variant == nil {
			return semir.Definition{}, fmt.Errorf("type %q has nil variant", declaration.Name.Value)
		}

		if record, ok := variant.Literal.(*ast.RecordLiteral); ok && variant.Name != nil && variant.Name.Value == declaration.Name.Value {
			fields, err := buildRecordFields(record)
			if err != nil {
				return semir.Definition{}, fmt.Errorf("record %q: %w", declaration.Name.Value, err)
			}
			definition.Type.Kind = semir.TypeRecord
			definition.Type.Fields = fields

			// Plain { ... } is semantic product/shape only. struct { ... } selects
			// concrete natural ordered storage, but target-specific field sizes and
			// offsets are still unresolved at this stage.
			if record.Token.TokenKind == token.STRUCT {
				definition.Representation = semir.Representation{
					Kind:     semir.RepresentationRecord,
					Policy:   semir.RepresentationPolicyNaturalOrdered,
					Resolved: false,
				}
			}
			return definition, nil
		}

		if variant.Literal == nil && variant.Payload != nil && variant.Name != nil && variant.Name.Value == declaration.Name.Value {
			base, err := semanticTypeName(variant.Payload)
			if err != nil {
				return semir.Definition{}, fmt.Errorf("alias %q: %w", declaration.Name.Value, err)
			}
			definition.Type.Kind = semir.TypeAlias
			definition.Type.Base = base
			return definition, nil
		}
	}

	definition.Type.Kind = semir.TypeSum
	definition.Type.Variants = make([]semir.Variant, 0, len(declaration.Variants))
	for _, variant := range declaration.Variants {
		if variant == nil || variant.Name == nil || variant.Name.Value == "" {
			return semir.Definition{}, fmt.Errorf("type %q has unnamed variant", declaration.Name.Value)
		}
		if variant.Literal != nil {
			return semir.Definition{}, fmt.Errorf(
				"type %q variant %q uses legacy literal syntax whose semantics are ambiguous; split payload/default/discriminant semantics before projecting it",
				declaration.Name.Value,
				variant.Name.Value,
			)
		}
		semanticVariant := semir.Variant{Name: variant.Name.Value}
		if variant.Payload != nil {
			payload, err := semanticTypeName(variant.Payload)
			if err != nil {
				return semir.Definition{}, fmt.Errorf("type %q variant %q: %w", declaration.Name.Value, variant.Name.Value, err)
			}
			semanticVariant.Payload = payload
		}
		definition.Type.Variants = append(definition.Type.Variants, semanticVariant)
	}
	return definition, nil
}

func buildInterfaceDefinition(declaration *ast.InterfaceType) (semir.Definition, error) {
	if declaration == nil || declaration.Name == nil || declaration.Name.Value == "" {
		return semir.Definition{}, fmt.Errorf("interface declaration has no name")
	}
	parameters, err := buildTypeParameters(declaration.TypeParams)
	if err != nil {
		return semir.Definition{}, fmt.Errorf("interface %q: %w", declaration.Name.Value, err)
	}
	definition := semir.Definition{
		Name: declaration.Name.Value,
		Type: semir.Type{
			Kind:       semir.TypeInterface,
			Parameters: parameters,
		},
	}

	for _, method := range declaration.Methods {
		if method == nil || method.Name == nil || method.Name.Value == "" {
			return semir.Definition{}, fmt.Errorf("interface %q has unnamed method", declaration.Name.Value)
		}
		semanticMethod := semir.Method{Name: method.Name.Value}
		if method.ReceiverType != nil {
			receiver, err := semanticTypeName(method.ReceiverType)
			if err != nil {
				return semir.Definition{}, fmt.Errorf("interface %q method %q receiver: %w", declaration.Name.Value, method.Name.Value, err)
			}
			semanticMethod.Receiver = receiver
		}
		for _, parameter := range method.Parameters {
			if parameter == nil || parameter.Name == nil {
				return semir.Definition{}, fmt.Errorf("interface %q method %q has invalid parameter", declaration.Name.Value)
			}
			parameterType, err := semanticTypeName(parameter.Type)
			if err != nil {
				return semir.Definition{}, fmt.Errorf("interface %q method %q parameter %q: %w", declaration.Name.Value, method.Name.Value, parameter.Name.Value, err)
			}
			semanticMethod.Parameters = append(semanticMethod.Parameters, semir.Field{
				Name: parameter.Name.Value,
				Type: parameterType,
			})
		}
		returnType, err := semanticTypeName(method.ReturnType)
		if err != nil {
			return semir.Definition{}, fmt.Errorf("interface %q method %q return type: %w", declaration.Name.Value, method.Name.Value, err)
		}
		semanticMethod.Return = returnType
		definition.Type.Methods = append(definition.Type.Methods, semanticMethod)
	}
	return definition, nil
}

func buildTypeParameters(parameters []*ast.TypeParameter) ([]semir.TypeParameter, error) {
	result := make([]semir.TypeParameter, 0, len(parameters))
	for _, parameter := range parameters {
		if parameter == nil || parameter.Name == nil || parameter.Name.Value == "" {
			return nil, fmt.Errorf("unnamed type parameter")
		}
		semanticParameter := semir.TypeParameter{Name: parameter.Name.Value}
		if parameter.Constraint != nil {
			constraint, err := semanticTypeName(parameter.Constraint)
			if err != nil {
				return nil, fmt.Errorf("type parameter %q constraint: %w", parameter.Name.Value, err)
			}
			semanticParameter.Constraint = constraint
		}
		// Whether a parameter is phantom is a checked semantic property, not
		// something this syntax-only projection should guess.
		result = append(result, semanticParameter)
	}
	return result, nil
}

func buildRecordFields(record *ast.RecordLiteral) ([]semir.Field, error) {
	if record == nil {
		return nil, fmt.Errorf("nil record")
	}
	ordered := record.OrderedFields()
	if len(record.Fields) > 0 && len(ordered) == 0 {
		return nil, fmt.Errorf("record source order is unavailable")
	}

	fields := make([]semir.Field, 0, len(ordered))
	for _, field := range ordered {
		fieldType, err := semanticTypeName(field.Value)
		if err != nil {
			return nil, fmt.Errorf("field %q: %w", field.Name, err)
		}
		fields = append(fields, semir.Field{Name: field.Name, Type: fieldType})
	}
	return fields, nil
}

func semanticTypeName(expression ast.Expression) (string, error) {
	switch expression := expression.(type) {
	case *ast.Identifier:
		if expression == nil || expression.Value == "" {
			return "", fmt.Errorf("empty type identifier")
		}
		return expression.Value, nil

	case *ast.PrefixExpression:
		if expression == nil || expression.Operator != "*" {
			return "", fmt.Errorf("unsupported type prefix %q", expression.Operator)
		}
		right, err := semanticTypeName(expression.Right)
		if err != nil {
			return "", err
		}
		return "*" + right, nil

	case *ast.InfixExpression:
		if expression == nil || expression.Operator != "&" {
			return "", fmt.Errorf("unsupported type operator %q", expression.Operator)
		}
		left, err := semanticTypeName(expression.Left)
		if err != nil {
			return "", err
		}
		right, err := semanticTypeName(expression.Right)
		if err != nil {
			return "", err
		}
		return left + " & " + right, nil

	case *ast.IndexExpression:
		if expression == nil {
			return "", fmt.Errorf("nil indexed type")
		}
		base, err := semanticTypeName(expression.Left)
		if err != nil {
			return "", err
		}
		switch index := expression.Index.(type) {
		case *ast.Identifier:
			if index.Value == "" {
				return "[]" + base, nil
			}
			if index.Value == "*" {
				return "[*]" + base, nil
			}
			return appendGenericArgument(base, index.Value), nil
		case *ast.IntegerLiteral:
			return "[" + strconv.FormatInt(index.Value, 10) + "]" + base, nil
		default:
			argument, err := semanticTypeName(expression.Index)
			if err != nil {
				return "", err
			}
			return appendGenericArgument(base, argument), nil
		}

	case *ast.RecordLiteral:
		fields, err := buildRecordFields(expression)
		if err != nil {
			return "", err
		}
		parts := make([]string, 0, len(fields))
		for _, field := range fields {
			parts = append(parts, field.Name+": "+field.Type)
		}
		return "{" + strings.Join(parts, ", ") + "}", nil

	default:
		return "", fmt.Errorf("unsupported type expression %T", expression)
	}
}

func appendGenericArgument(base, argument string) string {
	if strings.HasSuffix(base, "]") {
		if open := strings.LastIndex(base, "["); open >= 0 {
			return base[:len(base)-1] + ", " + argument + "]"
		}
	}
	return base + "[" + argument + "]"
}
