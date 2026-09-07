package typechecker

import (
	"fmt"
	"strings"

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
	if name == "Atomic" {
		if len(argExprs) != 1 {
			tc.addError(expr, "Atomic[...] expects exactly one fixed-width integer carrier")
			return nil, true
		}
		element := tc.parseTypeExpression(argExprs[0])
		if element == nil {
			return nil, true
		}
		atomicType, err := NewAtomicType(element)
		if err != nil {
			tc.addError(expr, "%v", err)
			return nil, true
		}
		return atomicType, true
	}
	args := make([]Type, 0, len(argExprs))
	for _, argExpr := range argExprs {
		arg := tc.parseTypeExpression(argExpr)
		if arg == nil {
			return nil, true
		}
		args = append(args, arg)
	}
	// A concrete application of a declared generic ADT (Option[i32] in an
	// annotation) is an instantiation the backend must monomorphize
	// (typechecker/mono.go); type-variable arguments record nothing.
	if _, isDeclaredADT := tc.adtTypes[name]; isDeclaredADT {
		tc.recordADTInstantiation(name, args)
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

// variantIndexBindings is the first concrete GADT solver. Constructor-result
// equations are solved under one accumulated substitution. Named result
// parameters and fixed positional indices must agree with every prior equation.
func (tc *TypeChecker) variantIndexBindings(
	adt *object.ADTType,
	variant *object.ADTVariantDef,
	actual []Type,
) (map[string]Type, Substitution, bool) {
	if adt == nil || variant == nil {
		return nil, nil, false
	}
	if variant.ResultName != "" && variant.ResultName != adt.Name {
		return nil, nil, false
	}
	indices := variant.ResultIndices
	if len(indices) == 0 && len(adt.TypeParams) > 0 {
		indices = adt.TypeParams
	}
	if len(indices) != len(actual) {
		return nil, nil, len(indices) == 0 && len(actual) == 0
	}

	params := make(map[string]bool, len(adt.TypeParams))
	for _, name := range adt.TypeParams {
		params[name] = true
	}
	bindings := make(map[string]Type)
	substitution := make(Substitution)
	applyBindings := func() {
		for name, bound := range bindings {
			bindings[name] = substitution.Apply(bound)
		}
	}
	unify := func(left, right Type) bool {
		equation := NewUnifier().Unify(substitution.Apply(left), substitution.Apply(right))
		if equation == nil {
			return false
		}
		substitution = substitution.Compose(equation)
		applyBindings()
		return true
	}
	bind := func(name string, value Type) bool {
		value = substitution.Apply(value)
		if prior, exists := bindings[name]; exists {
			if !unify(prior, value) {
				return false
			}
			bindings[name] = substitution.Apply(prior)
			return true
		}
		bindings[name] = value
		return true
	}

	for i, expected := range indices {
		actualIndex := substitution.Apply(actual[i])
		if params[expected] {
			if !bind(expected, actualIndex) {
				return nil, nil, false
			}
			continue
		}

		concrete := tc.storedIndexType(expected)
		if concrete == nil || !unify(actualIndex, concrete) {
			return nil, nil, false
		}
		// A fixed result at position i also refines the ADT parameter occupying
		// that position. Compose it with any equation already established for
		// that parameter; never overwrite an earlier binding.
		if i < len(adt.TypeParams) && !bind(adt.TypeParams[i], concrete) {
			return nil, nil, false
		}
	}
	return bindings, substitution, true
}

func (tc *TypeChecker) variantReachable(typ Type, adtName string, variant *object.ADTVariantDef) bool {
	name, _, args, ok := adtInstantiation(typ)
	if !ok || name != adtName {
		return false
	}
	adt := tc.adtTypes[adtName]
	_, _, reachable := tc.variantIndexBindings(adt, variant, args)
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

func variantResultString(adt *object.ADTType, variant *object.ADTVariantDef) string {
	name := variant.ResultName
	if name == "" && adt != nil {
		name = adt.Name
	}
	if len(variant.ResultIndices) == 0 {
		return name
	}
	return fmt.Sprintf("%s[%s]", name, strings.Join(variant.ResultIndices, ", "))
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
