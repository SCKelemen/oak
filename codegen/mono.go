package codegen

// Generic-ADT monomorphization (docs/spec/20-types.md, docs/spec/30-adts):
// the type checker records every concrete instantiation and the
// instantiation each variant/match was checked against (typechecker/mono.go,
// the single resolution authority); the backend emits one specialized
// tagged union per instantiation by substituting the type parameters in the
// declared variants' payload types. Generic templates themselves are never
// emitted. All names derive from parser-validated identifiers; collisions
// with declared types and unsupported argument shapes fail closed.
// Substitution structure is modeled in Oak.Monomorphization (Lean).

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// instantiateGenericADTs specializes and registers every recorded
// instantiation, then emits its tagged union. Called after concrete ADT
// collection, before function prototypes.
func (cg *CodeGenerator) instantiateGenericADTs(tc *typechecker.TypeChecker) {
	for _, inst := range tc.ADTInstantiations() {
		template, declared := cg.adtTypes[inst.ADT]
		if !declared || len(template.TypeParams) == 0 {
			continue
		}
		mangled := inst.MangledName()
		if existing, collision := cg.adtTypes[mangled]; collision && len(existing.TypeParams) == 0 && existing != template {
			// A declared type already owns this name: never silently merge.
			cg.write(fmt.Sprintf("OAK_MONOMORPHIZATION_NAME_COLLISION(%s);\n\n", cg.cTypeName(mangled)))
			continue
		}
		specialized, ok := specializeADT(template, inst)
		if !ok {
			cg.write(fmt.Sprintf("OAK_UNSUPPORTED_INSTANTIATION(%s);\n\n", cg.cTypeName(mangled)))
			continue
		}
		cg.adtTypes[mangled] = specialized
		cg.emitADTType(specialized, tc)
	}
}

// specializeADT builds the concrete ADT for one instantiation: the mangled
// name, and every variant's payload type with the template's parameters
// substituted by the argument atoms (which are ordinary Oak type names).
func specializeADT(template *ast.ADTType, inst typechecker.Instantiation) (*ast.ADTType, bool) {
	if len(template.TypeParams) != len(inst.Args) {
		return nil, false
	}
	bindings := make(map[string]ast.Expression, len(inst.Args))
	for i, param := range template.TypeParams {
		if param == nil || param.Name == nil {
			return nil, false
		}
		bindings[param.Name.Value] = argumentExpression(inst.Args[i])
	}

	specialized := &ast.ADTType{
		BaseNode: template.BaseNode,
		Token:    template.Token,
		EndToken: template.EndToken,
		Name:     &ast.Identifier{Token: template.Name.Token, Value: inst.MangledName()},
	}
	for _, variant := range template.Variants {
		payload, ok := typechecker.SubstituteTypeAST(variant.Payload, bindings)
		if !ok {
			return nil, false
		}
		literal := variant.Literal
		// Record templates substitute inside the field list, so the
		// specialized declaration routes to struct emission with concrete
		// field types (one substitution authority: SubstituteTypeAST).
		if recordLit, isRecord := variant.Literal.(*ast.RecordLiteral); isRecord {
			substitutedRecord := &ast.RecordLiteral{
				BaseNode: recordLit.BaseNode,
				Token:    recordLit.Token,
				EndToken: recordLit.EndToken,
				Fields:   make(map[string]ast.Expression, len(recordLit.Fields)),
			}
			for _, field := range recordLit.FieldOrder {
				substituted, okField := typechecker.SubstituteTypeAST(field.Value, bindings)
				if !okField {
					return nil, false
				}
				substitutedRecord.Fields[field.Name] = substituted
				substitutedRecord.FieldOrder = append(substitutedRecord.FieldOrder, ast.RecordField{
					Token: field.Token, Name: field.Name, Value: substituted,
				})
			}
			literal = substitutedRecord
		}
		specialized.Variants = append(specialized.Variants, &ast.ADTVariant{
			Token:   variant.Token,
			Name:    variant.Name,
			Payload: payload,
			Literal: literal,
			// Indexed results (GADTs) are a checker concept; representation
			// is the enclosing instantiation.
		})
	}
	return specialized, true
}

// argumentExpression renders a mangled argument atom back to type syntax:
// numeric atoms are const parameters, everything else a type name.
func argumentExpression(atom string) ast.Expression {
	numeric := len(atom) > 0
	for i := 0; i < len(atom); i++ {
		if atom[i] < '0' || atom[i] > '9' {
			numeric = false
			break
		}
	}
	if numeric {
		value := int64(0)
		for i := 0; i < len(atom); i++ {
			value = value*10 + int64(atom[i]-'0')
		}
		return &ast.IntegerLiteral{Value: value}
	}
	return &ast.Identifier{Value: atom}
}

// genericAnnotationName resolves a generic type annotation expression
// (Option[i32], Ring[u8, 16]) to its mangled Oak-level name. The declared
// template's parameter count is the disambiguator against array syntax:
// [4]Option[i32] flattens to Option with two arguments, matches no
// two-parameter template, and stays an array.
func (cg *CodeGenerator) genericAnnotationName(typeExpr ast.Expression) (string, bool) {
	name, args, ok := flattenAnnotationApplication(typeExpr)
	if !ok || len(args) == 0 {
		return "", false
	}
	template, declared := cg.adtTypes[name]
	if !declared || len(template.TypeParams) != len(args) {
		return "", false
	}
	mangled := name
	for _, arg := range args {
		atom, okAtom := annotationAtom(arg)
		if !okAtom {
			return "", false
		}
		mangled += "_" + atom
	}
	return mangled, true
}

// flattenAnnotationApplication decodes F[A][B]... (integer arguments
// admitted; view/span markers rejected).
func flattenAnnotationApplication(expr ast.Expression) (string, []ast.Expression, bool) {
	switch t := expr.(type) {
	case *ast.Identifier:
		return t.Value, nil, t.Value != ""
	case *ast.IndexExpression:
		name, args, ok := flattenAnnotationApplication(t.Left)
		if !ok || t.Index == nil {
			return "", nil, false
		}
		if marker, isIdent := t.Index.(*ast.Identifier); isIdent && (marker.Value == "" || marker.Value == "*") {
			return "", nil, false
		}
		return name, append(args, t.Index), true
	default:
		return "", nil, false
	}
}

// annotationAtom flattens one syntactic type argument to its name atom.
func annotationAtom(expr ast.Expression) (string, bool) {
	switch t := expr.(type) {
	case *ast.IntegerLiteral:
		return fmt.Sprintf("%d", t.Value), true
	case *ast.Identifier:
		if t.Value == "" || t.Value == "*" {
			return "", false // view/span markers are not type arguments
		}
		return t.Value, true
	case *ast.IndexExpression:
		base, isIdent := t.Left.(*ast.Identifier)
		if !isIdent {
			return "", false
		}
		inner, ok := annotationAtom(t.Index)
		if !ok {
			return "", false
		}
		return base.Value + "_" + inner, true
	}
	return "", false
}
