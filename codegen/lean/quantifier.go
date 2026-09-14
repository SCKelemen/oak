package lean

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
)

// quantifier renders a bounded quantifier (docs/spec/10-syntax.md section
// 3e) as the computable fold the interpreter performs: `List.all` for
// `forall`, `List.any` for `exists`, over the explicit list of the binder's
// domain — `[false, true]`, the 8- and 16-bit integers as `List.range`
// mapped through the constructor, a payload-free sum type's constructors —
// with the binders bound innermost last, so `decide` evaluates the same
// enumeration the program does. The body is a single expression; one with
// statements is outside the extracted subset.
func (em *emitter) quantifier(e *ast.QuantifierExpression) (string, error) {
	if e.Body == nil || em.needsDo(e.Body) {
		return "", fmt.Errorf("quantifier %s: a body with statements is outside the extracted subset", e.String())
	}
	inner := newScope(em.scope)
	em.scope = inner
	defer func() { em.scope = inner.outer }()
	domains := make([]string, len(e.Binders))
	for i, binder := range e.Binders {
		leanType, err := em.leanType(binder.Type)
		if err != nil {
			return "", err
		}
		domain, err := em.quantifierDomain(binder.Type, leanType)
		if err != nil {
			return "", err
		}
		domains[i] = domain
		em.scope.declare(binder.Name.Value, leanType)
	}
	out, err := em.armValue(e.Body, "Bool")
	if err != nil {
		return "", err
	}
	fold := "any"
	if e.Universal {
		fold = "all"
	}
	for i := len(e.Binders) - 1; i >= 0; i-- {
		out = fmt.Sprintf("(%s.%s (fun %s => %s))", domains[i], fold, ident(e.Binders[i].Name.Value), out)
	}
	return out, nil
}

// quantifierDomain is the Lean list of a binder type's values, in the
// interpreter's order (false before true, integers ascending, variants in
// declaration order).
func (em *emitter) quantifierDomain(typ ast.Expression, leanType string) (string, error) {
	switch leanType {
	case "Bool":
		return "[false, true]", nil
	case "UInt8":
		return "((List.range 256).map (fun n => UInt8.ofNat n))", nil
	case "UInt16":
		return "((List.range 65536).map (fun n => UInt16.ofNat n))", nil
	case "Int8":
		return "((List.range 256).map (fun n => Int8.ofInt (Int.ofNat n - 128)))", nil
	case "Int16":
		return "((List.range 65536).map (fun n => Int16.ofInt (Int.ofNat n - 32768)))", nil
	}
	ident, isIdent := typ.(*ast.Identifier)
	if !isIdent {
		return "", fmt.Errorf("quantifier over %s is outside the extracted subset", typ.String())
	}
	adt, declared := em.adts[ident.Value]
	if !declared {
		return "", fmt.Errorf("quantifier over %s is outside the extracted subset", ident.Value)
	}
	leanName, ok := em.adtLeanName(ident.Value)
	if !ok {
		return "", fmt.Errorf("quantifier over %s is outside the extracted subset", ident.Value)
	}
	out := "["
	for i, variant := range adt.Variants {
		if variant.Payload != nil {
			return "", fmt.Errorf("quantifier over %s: variant %s carries a payload", ident.Value, variant.Name.Value)
		}
		if i > 0 {
			out += ", "
		}
		out += fmt.Sprintf("%s.%s", leanName, variant.Name.Value)
	}
	return out + "]", nil
}
