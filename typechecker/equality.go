package typechecker

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// Equality on aggregates (docs/spec/30-adts-patterns.md §14, docs/spec/40-records.md
// §16). `==` and `!=` on sum-type and record values compare structurally:
// the variant tags, then the payloads; the fields in declaration order. The
// checker admits the comparison when every part has an equality of its own
// — machine integers, `Bool`, `f32`/`f64` (IEEE, so NaN differs from
// itself), nested named sum types and records, fixed arrays of integers or
// `Bool` — and records the aggregate's name at the operator so the C backend
// emits that type's equality function; the interpreter compares the same way.
// Views and spans, anonymous record shapes, storage floats, and generic
// instantiations are refused (`OAK-T0601`) rather than compared by identity
// or by bits.

// CodeEqualityUndefined reports `==`/`!=` on a type without an equality.
const CodeEqualityUndefined = "OAK-T0601"

// EqualityVariant is one variant of a sum type as the backend's equality
// function sees it: the name and the payload type, nil when there is none.
type EqualityVariant struct {
	Name    string
	Payload Type
}

// checkAggregateEquality admits or refuses `==`/`!=` at an aggregate type
// and records the admitted aggregate's name for the backend.
func (tc *TypeChecker) checkAggregateEquality(expr *ast.InfixExpression, typ Type) bool {
	name, isAggregate := aggregateName(typ)
	if !isAggregate {
		return true
	}
	if reason := tc.equalityReason(typ, map[string]bool{}); reason != "" {
		tc.addTypeDiagnostic(expr, CodeEqualityUndefined,
			fmt.Sprintf("operator %s is not defined on %s: %s", expr.Operator, typ.String(), reason))
		return false
	}
	if tc.equalityTypes == nil {
		tc.equalityTypes = map[string]string{}
	}
	tc.equalityTypes[positionKey(expr.Token)] = name
	return true
}

// EqualityType reports the named aggregate an `==`/`!=` at tok compares.
func (tc *TypeChecker) EqualityType(tok token.Token) (string, bool) {
	name, ok := tc.equalityTypes[positionKey(tok)]
	return name, ok
}

func aggregateName(typ Type) (string, bool) {
	switch t := typ.(type) {
	case *ADTType:
		return t.Name, true
	case *NarrowedADTVariantType:
		return t.ADTName, true
	case *RecordType:
		if t.Name != "" {
			return t.Name, true
		}
	case *StringType:
		// Strings compare by their bytes (docs/spec/70-strings.md): one
		// helper, named like an aggregate's.
		return "string", true
	}
	return "", false
}

// equalityReason is empty when typ has an equality, else why it has none.
func (tc *TypeChecker) equalityReason(typ Type, visiting map[string]bool) string {
	switch t := typ.(type) {
	case *BoolType, *UnitType, *StringType:
		return ""
	case *PrimitiveType:
		if IsFloatName(t.Name) && t.Name != "f32" && t.Name != "f64" {
			return fmt.Sprintf("%s is a storage format; widen it before comparing", t.Name)
		}
		return ""
	case *NarrowedADTVariantType:
		return tc.equalityReason(&ADTType{Name: t.ADTName}, visiting)
	case *ADTType:
		if visiting[t.Name] {
			return ""
		}
		visiting[t.Name] = true
		variants, ok := tc.ADTVariants(t.Name)
		if !ok {
			return fmt.Sprintf("%s is generic or unknown; equality is defined on concrete sum types", t.Name)
		}
		for _, variant := range variants {
			if variant.Payload == nil {
				continue
			}
			if reason := tc.equalityReason(variant.Payload, visiting); reason != "" {
				return fmt.Sprintf("variant %s: %s", variant.Name, reason)
			}
		}
		return ""
	case *RecordType:
		if t.Name == "" {
			return "an anonymous record shape has no equality; declare it as a struct"
		}
		if visiting[t.Name] {
			return ""
		}
		visiting[t.Name] = true
		order, fields, ok := tc.RecordFields(t.Name)
		if !ok {
			return fmt.Sprintf("%s is not a declared record", t.Name)
		}
		for _, field := range order {
			if reason := tc.equalityReason(fields[field], visiting); reason != "" {
				return fmt.Sprintf("field %s: %s", field, reason)
			}
		}
		return ""
	case *ArrayType:
		if t.IsSlice || t.IsSpan {
			return "a view compares by identity, not by contents; compare the elements"
		}
		switch e := t.ElementType.(type) {
		case *BoolType:
			return ""
		case *PrimitiveType:
			if IsFloatName(e.Name) {
				return "arrays of floats have no equality; compare the elements"
			}
			return ""
		}
		return "arrays compare element by element only over integers and Bool"
	}
	return fmt.Sprintf("%s has no equality", typ.String())
}

// ADTVariants lists a concrete sum type's variants with their payload
// types, for the backend's equality function.
func (tc *TypeChecker) ADTVariants(name string) ([]EqualityVariant, bool) {
	adt, ok := tc.adtTypes[name]
	if !ok || len(adt.TypeParams) != 0 {
		return nil, false
	}
	var out []EqualityVariant
	for _, variant := range adt.Variants {
		item := EqualityVariant{Name: variant.Name}
		if variant.Payload != "" {
			item.Payload = tc.variantPayloadType(&ADTType{Name: name}, variant)
			if item.Payload == nil {
				return nil, false
			}
		}
		out = append(out, item)
	}
	return out, true
}

// RecordFields lists a declared record's fields in declaration order, for
// the backend's equality function.
func (tc *TypeChecker) RecordFields(name string) ([]string, map[string]Type, bool) {
	scheme, ok := tc.env.Get(name)
	if !ok || scheme == nil {
		return nil, nil, false
	}
	record, isRecord := scheme.Type.(*RecordType)
	if !isRecord || len(record.Order) != len(record.Fields) {
		return nil, nil, false
	}
	return record.Order, record.Fields, true
}

// EqualityTypes lists the named aggregates whose equality functions the
// program needs: every type an `==`/`!=` compares, closed under the
// aggregates nested in their payloads and fields.
func (tc *TypeChecker) EqualityTypes() map[string]bool {
	needed := map[string]bool{}
	var visit func(typ Type)
	visit = func(typ Type) {
		switch t := typ.(type) {
		case *StringType:
			needed["string"] = true
		case *NarrowedADTVariantType:
			visit(&ADTType{Name: t.ADTName})
		case *ADTType:
			if needed[t.Name] {
				return
			}
			needed[t.Name] = true
			if variants, ok := tc.ADTVariants(t.Name); ok {
				for _, variant := range variants {
					if variant.Payload != nil {
						visit(variant.Payload)
					}
				}
			}
		case *RecordType:
			if t.Name == "" || needed[t.Name] {
				return
			}
			needed[t.Name] = true
			if order, fields, ok := tc.RecordFields(t.Name); ok {
				for _, field := range order {
					visit(fields[field])
				}
			}
		}
	}
	for _, name := range tc.equalityTypes {
		if name == "string" {
			needed[name] = true
		} else if _, isADT := tc.adtTypes[name]; isADT {
			visit(&ADTType{Name: name})
		} else {
			visit(&RecordType{Name: name})
		}
	}
	return needed
}
