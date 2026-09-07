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
	substitution := make(map[string]string, len(inst.Args))
	for i, param := range template.TypeParams {
		if param == nil || param.Name == nil {
			return nil, false
		}
		substitution[param.Name.Value] = inst.Args[i]
	}

	specialized := &ast.ADTType{
		BaseNode: template.BaseNode,
		Token:    template.Token,
		EndToken: template.EndToken,
		Name:     &ast.Identifier{Token: template.Name.Token, Value: inst.MangledName()},
	}
	for _, variant := range template.Variants {
		payload, ok := substituteTypeExpr(variant.Payload, substitution)
		if !ok {
			return nil, false
		}
		specialized.Variants = append(specialized.Variants, &ast.ADTVariant{
			Token:   variant.Token,
			Name:    variant.Name,
			Payload: payload,
			Literal: variant.Literal,
			// Indexed results (GADTs) are a checker concept; representation
			// is the enclosing instantiation.
		})
	}
	return specialized, true
}

// substituteTypeExpr rewrites type-parameter identifiers inside a payload
// type expression. Unsupported payload shapes report false (fail closed).
func substituteTypeExpr(expr ast.Expression, substitution map[string]string) (ast.Expression, bool) {
	switch t := expr.(type) {
	case nil:
		return nil, true
	case *ast.Identifier:
		if replacement, isParam := substitution[t.Value]; isParam {
			return &ast.Identifier{Token: t.Token, Value: replacement}, true
		}
		return t, true
	case *ast.IndexExpression:
		// Array/view/span payloads over a parameter: [4]T, []T, [*]T.
		left, okLeft := substituteTypeExpr(t.Left, substitution)
		index, okIndex := substituteTypeExpr(t.Index, substitution)
		if !okLeft || !okIndex {
			return nil, false
		}
		return &ast.IndexExpression{Token: t.Token, Left: left, Index: index, Dot: t.Dot}, true
	case *ast.IntegerLiteral:
		return t, true
	}
	return nil, false
}

// genericAnnotationName resolves a generic type annotation expression
// (Option[i32] as IndexExpression syntax) to its mangled Oak-level name.
// Reports false for non-generic annotations; unregistered instantiations
// still resolve (the emission pass registers all recorded ones — anything
// else fails closed at C compile time via the unknown type name).
func (cg *CodeGenerator) genericAnnotationName(typeExpr ast.Expression) (string, bool) {
	indexExpr, isIndex := typeExpr.(*ast.IndexExpression)
	if !isIndex {
		return "", false
	}
	base, isIdent := indexExpr.Left.(*ast.Identifier)
	if !isIdent {
		// Nested application: Result[i32, E][...] — flatten left first.
		if inner, ok := cg.genericAnnotationName(indexExpr.Left); ok {
			atom, okAtom := annotationAtom(indexExpr.Index)
			if !okAtom {
				return "", false
			}
			return inner + "_" + atom, true
		}
		return "", false
	}
	template, declared := cg.adtTypes[base.Value]
	if !declared || len(template.TypeParams) == 0 {
		return "", false
	}
	atom, ok := annotationAtom(indexExpr.Index)
	if !ok {
		return "", false
	}
	return base.Value + "_" + atom, true
}

// annotationAtom flattens one syntactic type argument to its name atom.
func annotationAtom(expr ast.Expression) (string, bool) {
	switch t := expr.(type) {
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
