package typechecker

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
)

// checkQuantifierExpression types a bounded quantifier
// (docs/spec/10-syntax.md section 3e): every binder ranges over a finite
// domain — Bool, an 8- or 16-bit integer, or a payload-free sum type — the
// body is a Bool block over the binders in a scope of its own, and the
// whole is Bool. The finiteness rule is the one the theorem prover's
// enumeration rung applies to a theorem's parameters, so a quantifier is
// never a claim the interpreter cannot evaluate.
func (tc *TypeChecker) checkQuantifierExpression(expr *ast.QuantifierExpression) Type {
	if len(expr.Binders) == 0 {
		tc.addError(expr, "a quantifier binds at least one name")
		return &BoolType{}
	}
	oldEnv := tc.env
	tc.env = NewEnclosedTypeEnvironment(oldEnv)
	defer func() { tc.env = oldEnv }()
	for _, binder := range expr.Binders {
		if binder == nil || binder.Name == nil {
			continue
		}
		typ := tc.ParseTypeExpression(binder.Type)
		if typ == nil {
			tc.addError(binder.Name, "quantifier binder %s: %s is not a type", binder.Name.Value, binder.Type)
			continue
		}
		if reason := tc.QuantifierDomainReason(typ); reason != "" {
			tc.addError(binder.Name, "quantifier binder %s ranges over %s, which is not a finite domain: %s", binder.Name.Value, typ, reason)
		}
		tc.env.SetType(binder.Name.Value, typ)
	}
	if expr.Body == nil || expr.Body.Block == nil {
		return &BoolType{}
	}
	bodyType := tc.checkBlockExpression(expr.Body.Block, &BoolType{})
	switch bodyType.(type) {
	case nil, *BoolType, *NeverType:
	default:
		tc.addError(expr.Body, "a quantifier body is Bool, not %s", bodyType)
	}
	return &BoolType{}
}

// QuantifierDomainReason says why a type is not a quantifier's domain, or
// "" when it is: Bool, the unrefined 8- and 16-bit integers, and sum types
// whose variants carry no payload are finite and small enough to
// enumerate (at most 65536 values per binder).
func (tc *TypeChecker) QuantifierDomainReason(typ Type) string {
	switch t := typ.(type) {
	case *BoolType:
		return ""
	case *PrimitiveType:
		switch t.Name {
		case "u8", "i8", "u16", "i16":
			if t.Refinement != "" {
				return fmt.Sprintf("%s is a refinement of %s; quantify over %s and state the refinement in the body", t.Refinement, t.Name, t.Name)
			}
			return ""
		case "u32", "i32", "u64", "i64", "u128", "int", "uint":
			return fmt.Sprintf("%s has more than 65536 values", t.Name)
		}
	case *ADTType:
		variants, ok := tc.ADTVariants(t.Name)
		if !ok {
			return fmt.Sprintf("%s is generic or undeclared", t.Name)
		}
		for _, variant := range variants {
			if variant.Payload == nil {
				continue
			}
			if _, isUnit := variant.Payload.(*UnitType); isUnit {
				continue
			}
			return fmt.Sprintf("variant %s.%s carries a payload", t.Name, variant.Name)
		}
		return ""
	}
	return fmt.Sprintf("%s is not Bool, an 8- or 16-bit integer, or a payload-free sum type", typ)
}
