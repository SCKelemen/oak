package compiler

// Type-qualified variant construction (docs/spec/30-adts-patterns.md,
// docs/spec/83-modules.md section 3.4): `Shape.Line(3)` and `Shape.Dot` are
// spelled as member access on a type name. The parser cannot know that
// `Shape` names an ADT, so it produces the same nodes as a method call or a
// field access; this pass — run after module elaboration, so
// `geo.Shape.Line(3)` has already become `<internal>.Line(3)` — rewrites
// those shapes into VariantExpression nodes, which the checker, lowering, and
// backend already handle. Only names declared as ADTs in the program are
// rewritten, and only members that are variants of that ADT; everything else
// is left for the checker to judge.

import (
	"reflect"

	"github.com/SCKelemen/oak/ast"
)

func lowerQualifiedVariants(program *ast.Program) error {
	adts := map[string]map[string]bool{}
	for _, stmt := range program.Statements {
		adt, ok := stmt.(*ast.ADTType)
		if !ok || adt.Name == nil {
			continue
		}
		variants := map[string]bool{}
		for _, variant := range adt.Variants {
			if variant.Name != nil {
				variants[variant.Name.Value] = true
			}
		}
		adts[adt.Name.Value] = variants
	}
	if len(adts) == 0 {
		return nil
	}
	qualified := func(expr ast.Expression) (*ast.Identifier, *ast.Identifier, bool) {
		access, isAccess := expr.(*ast.IndexExpression)
		if !isAccess || !access.Dot {
			return nil, nil, false
		}
		typeName, isType := access.Left.(*ast.Identifier)
		variant, isVariant := access.Index.(*ast.Identifier)
		if !isType || !isVariant {
			return nil, nil, false
		}
		variants, isADT := adts[typeName.Value]
		if !isADT || !variants[variant.Value] {
			return nil, nil, false
		}
		return typeName, variant, true
	}
	return transformSyntax(reflect.ValueOf(program), func(e ast.Expression) (ast.Expression, error) {
		switch n := e.(type) {
		case *ast.InvocationExpression:
			// Type.Variant(payload): exactly one argument is a payload.
			if typeName, variant, ok := qualified(n.Function); ok && len(n.Arguments) == 1 {
				return &ast.VariantExpression{
					BaseNode: n.BaseNode,
					Token:    n.Token,
					TypeName: typeName,
					Variant:  variant,
					Payload:  n.Arguments[0],
				}, nil
			}
		case *ast.IndexExpression:
			// Type.Variant without payload.
			if typeName, variant, ok := qualified(n); ok {
				return &ast.VariantExpression{
					BaseNode: n.BaseNode,
					Token:    n.Token,
					TypeName: typeName,
					Variant:  variant,
				}, nil
			}
		}
		return e, nil
	})
}
