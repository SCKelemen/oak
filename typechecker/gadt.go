package typechecker

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
)

// flattenTypeApplicationSyntax decodes the parser's left-associated
// IndexExpression representation: F[A][B] becomes F with arguments A, B.
func flattenTypeApplicationSyntax(expr ast.Expression) (string, []ast.Expression, bool) {
	switch e := expr.(type) {
	case *ast.Identifier:
		return e.Value, nil, e.Value != ""
	case *ast.IndexExpression:
		name, args, ok := flattenTypeApplicationSyntax(e.Left)
		if !ok || e.Index == nil {
			return "", nil, false
		}
		if marker, ok := e.Index.(*ast.Identifier); ok && (marker.Value == "" || marker.Value == "*") {
			return "", nil, false
		}
		if _, arrayLength := e.Index.(*ast.IntegerLiteral); arrayLength {
			return "", nil, false
		}
		return name, append(args, e.Index), true
	default:
		return "", nil, false
	}
}

func (tc *TypeChecker) parseGenericTypeApplication(expr ast.Expression) (Type, bool) {
	name, argExprs, ok := flattenTypeApplicationSyntax(expr)
	if !ok || len(argExprs) == 0 {
		return nil, false
	}
	args := make([]Type, 0, len(argExprs))
	for _, argExpr := range argExprs {
		arg := tc.parseTypeExpression(argExpr)
		if arg == nil {
			return nil, true
		}
		args = append(args, arg)
	}
	return &GenericType{Name: name, TypeArgs: args}, true
}

func adtInstantiation(typ Type) (name, onlyVariant string, args []Type, ok bool) {
	switch t := typ.(type) {
	case *ADTType:
		return t.Name, "", nil, true
	case *GenericType:
		return t.Name, "", t.TypeArgs, true
	case *NarrowedADTVariantType:
		return t.ADTName, t.VariantName, t.TypeArgs, true
	default:
		return "", "", nil, false
	}
}

func (tc *TypeChecker) storedIndexType(spelling string) Type {
	return tc.parseTypeExpression(&ast.Identifier{Value: spelling})
}

func typeListsEqual(left, right []Type) bool {
	if len(left) != len(right) {
		return false
	}
	for i := range left {
		if !left[i].Equals(right[i]) {
			return false
		}
	}
	return true
}

func (tc *TypeChecker) instantiateStoredType(spelling string, bindings map[string]Type) Type {
	if bound, ok := bindings[spelling]; ok {
		return bound
	}
	return tc.storedIndexType(spelling)
}

// variantIndexBindings is the first concrete GADT solver. Constructor result
// parameters bind once and repeated occurrences must agree; concrete result
// indices must equal the scrutinee indices exactly.
func (tc *TypeChecker) variantIndexBindings(
	adt *object.ADTType,
	variant *object.ADTVariantDef,
	actual []Type,
) (map[string]Type, bool) {
	if adt == nil || variant == nil {
		return nil, false
	}
	if variant.ResultName != "" && variant.ResultName != adt.Name {
		return nil, false
	}
	indices := variant.ResultIndices
	if len(indices) == 0 && len(adt.TypeParams) > 0 {
		indices = adt.TypeParams
	}
	if len(indices) != len(actual) {
		return nil, len(indices) == 0 && len(actual) == 0
	}
	params := make(map[string]bool, len(adt.TypeParams))
	for _, name := range adt.TypeParams {
		params[name] = true
	}
	bindings := make(map[string]Type)
	apply := func(sub Substitution) {
		for name, bound := range bindings {
			bindings[name] = sub.Apply(bound)
		}
	}
	for i, expected := range indices {
		if params[expected] {
			if prior, exists := bindings[expected]; exists {
				sub := NewUnifier().Unify(prior, actual[i])
				if sub == nil {
					return nil, false
				}
				apply(sub)
				bindings[expected] = sub.Apply(prior)
			} else {
				bindings[expected] = actual[i]
			}
			continue
		}
		concrete := tc.storedIndexType(expected)
		if concrete == nil {
			return nil, false
		}
		sub := NewUnifier().Unify(actual[i], concrete)
		if sub == nil {
			return nil, false
		}
		apply(sub)
		// Record the refined ADT index position as well as applying the
		// substitution to any constructor-parameter bindings.
		bindings[adt.TypeParams[i]] = concrete
	}
	return bindings, true
}

func (tc *TypeChecker) variantReachable(typ Type, adtName string, variant *object.ADTVariantDef) bool {
	name, _, args, ok := adtInstantiation(typ)
	if !ok || name != adtName {
		return false
	}
	adt := tc.adtTypes[adtName]
	_, reachable := tc.variantIndexBindings(adt, variant, args)
	return reachable
}

func (tc *TypeChecker) variantResultType(
	adt *object.ADTType,
	variant *object.ADTVariantDef,
	expected Type,
) Type {
	if expected != nil {
		if name, _, _, ok := adtInstantiation(expected); ok && name == adt.Name && tc.variantReachable(expected, adt.Name, variant) {
			return expected
		}
	}
	if len(variant.ResultIndices) == 0 {
		return &ADTType{Name: adt.Name}
	}
	args := make([]Type, 0, len(variant.ResultIndices))
	param := make(map[string]bool, len(adt.TypeParams))
	for _, name := range adt.TypeParams {
		param[name] = true
	}
	for _, spelling := range variant.ResultIndices {
		if param[spelling] {
			return &ADTType{Name: adt.Name}
		}
		arg := tc.storedIndexType(spelling)
		if arg == nil {
			return nil
		}
		args = append(args, arg)
	}
	return &GenericType{Name: adt.Name, TypeArgs: args}
}

func constructorResultSyntax(result ast.Expression) (string, []string, error) {
	name, args, ok := flattenTypeApplicationSyntax(result)
	if !ok || len(args) == 0 {
		return "", nil, fmt.Errorf("result must be an applied ADT type")
	}
	indices := make([]string, 0, len(args))
	for _, arg := range args {
		ident, atomic := arg.(*ast.Identifier)
		if !atomic || ident.Value == "" {
			return "", nil, fmt.Errorf("result indices must be atomic type names or parameters")
		}
		indices = append(indices, ident.Value)
	}
	return name, indices, nil
}
