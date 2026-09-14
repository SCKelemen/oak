package evaluator

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
)

// evalQuantifierExpression decides a bounded quantifier by enumeration
// (docs/spec/10-syntax.md section 3e): the binders range over their finite
// domains in declaration order, the body is evaluated in a scope of its
// own for each assignment, and the enumeration stops at the first
// assignment that decides the result — a false body under `forall`, a
// true one under `exists`. An error in the body is the quantifier's error.
func evalQuantifierExpression(node *ast.QuantifierExpression, env *object.Environment) object.Object {
	domains := make([][]object.Object, len(node.Binders))
	for i, binder := range node.Binders {
		values, err := quantifierDomain(binder.Type, env)
		if err != nil {
			return err
		}
		domains[i] = values
	}
	if node.Body == nil || node.Body.Block == nil {
		return newError("quantifier without a body")
	}
	scope := object.NewEnclosedEnvironment(env)
	defer object.ReleaseEnvironment(scope)
	var walk func(i int) object.Object
	walk = func(i int) object.Object {
		if i == len(node.Binders) {
			result := evalBlockStatement(node.Body.Block, scope)
			if isError(result) {
				return result
			}
			truth, isBool := result.(*object.Boolean)
			if !isBool {
				return newError("quantifier body is %s, not Bool", result.Type())
			}
			if truth.Value != node.Universal {
				return truth // the deciding assignment: false under forall, true under exists
			}
			return nil
		}
		name := node.Binders[i].Name.Value
		for _, value := range domains[i] {
			scope.Set(name, value)
			if decided := walk(i + 1); decided != nil {
				return decided
			}
		}
		return nil
	}
	if decided := walk(0); decided != nil {
		return decided
	}
	return nativeBoolToBooleanObject(node.Universal)
}

// quantifierDomain lists a binder type's values: Bool, the 8- and 16-bit
// integers (byte included), and a payload-free sum type's variants. The
// type checker has refused every other type; an unchecked program gets
// the error here.
func quantifierDomain(typeExpr ast.Expression, env *object.Environment) ([]object.Object, *object.Error) {
	ident, isIdent := typeExpr.(*ast.Identifier)
	if !isIdent {
		return nil, newError("quantifier over %s: not a finite domain", typeExpr.String())
	}
	var lo, hi int64
	switch ident.Value {
	case "Bool":
		return []object.Object{FALSE, TRUE}, nil
	case "u8", "byte":
		lo, hi = 0, 255
	case "i8":
		lo, hi = -128, 127
	case "u16":
		lo, hi = 0, 65535
	case "i16":
		lo, hi = -32768, 32767
	default:
		adt, isADT := env.GetADTType(ident.Value)
		if !isADT {
			return nil, newError("quantifier over %s: not a finite domain", ident.Value)
		}
		values := make([]object.Object, 0, len(adt.Variants))
		for _, variant := range adt.Variants {
			if variant.Payload != "" {
				return nil, newError("quantifier over %s: variant %s carries a payload", ident.Value, variant.Name)
			}
			values = append(values, &object.ADTValue{TypeName: ident.Value, Variant: variant.Name})
		}
		return values, nil
	}
	values := make([]object.Object, 0, hi-lo+1)
	for v := lo; v <= hi; v++ {
		values = append(values, &object.Integer{Value: v})
	}
	return values, nil
}
