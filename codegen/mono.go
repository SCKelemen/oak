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

// specializeADT builds the concrete ADT for one instantiation: the mangled
// name, and every variant's payload type with the template's parameters
// substituted by the argument atoms (which are ordinary Oak type names).
func (cg *CodeGenerator) specializeADT(template *ast.ADTType, inst typechecker.Instantiation) (*ast.ADTType, bool) {
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
		payload = cg.normalizeTypeExpression(payload)
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
				// Declared layout (packed/align) is part of the template and
				// carries to every instantiation unchanged.
				Layout: recordLit.Layout,
			}
			for _, field := range recordLit.FieldOrder {
				substituted, okField := typechecker.SubstituteTypeAST(field.Value, bindings)
				if !okField {
					return nil, false
				}
				substituted = cg.normalizeTypeExpression(substituted)
				substitutedRecord.Fields[field.Name] = substituted
				substitutedRecord.FieldOrder = append(substitutedRecord.FieldOrder, ast.RecordField{
					Token: field.Token, Name: field.Name, Value: substituted, Align: field.Align,
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

// typeEmissionUnit is one pending type definition: a declared concrete
// type, or a recorded instantiation of a generic template.
type typeEmissionUnit struct {
	name          string
	declared      *ast.ADTType
	instantiation *typechecker.Instantiation
}

// emitTypesInDependencyOrder emits records (concrete and instantiated) to
// a fixpoint — a record emits once every field type it references is
// placed — then tagged-union ADTs (concrete and instantiated), which may
// carry any of the records as payloads. Types that never become placeable
// fail closed with a compile-breaking marker.
func (cg *CodeGenerator) emitTypesInDependencyOrder(program *ast.Program, tc *typechecker.TypeChecker) {
	var records []typeEmissionUnit
	var unions []typeEmissionUnit

	for _, stmt := range program.Statements {
		adt, isADT := stmt.(*ast.ADTType)
		if !isADT || len(adt.TypeParams) > 0 {
			continue
		}
		unit := typeEmissionUnit{name: adt.Name.Value, declared: adt}
		if adt.Refinement != nil {
			// A refinement is a typedef of a primitive and a guard: nothing
			// depends before it, and a record field may name it, so it is
			// emitted ahead of every record.
			cg.emitTypeUnit(unit, tc)
			continue
		}
		if _, isRecord := recordDefinitionShape(adt); isRecord {
			records = append(records, unit)
		} else {
			unions = append(unions, unit)
		}
	}
	for _, inst := range tc.ADTInstantiations() {
		template, declared := cg.adtTypes[inst.ADT]
		if !declared || len(template.TypeParams) == 0 {
			continue
		}
		instantiation := inst
		unit := typeEmissionUnit{name: inst.MangledName(), instantiation: &instantiation}
		if _, isRecord := recordDefinitionShape(template); isRecord {
			records = append(records, unit)
		} else {
			unions = append(unions, unit)
		}
	}

	// Records: fixpoint on field placeability.
	pending := records
	emittedUnions := map[string]bool{}
	for len(pending) > 0 {
		progressed := false
		var stuck []typeEmissionUnit
		for _, unit := range pending {
			recordLit, ok := cg.emissionRecordLiteral(unit)
			if ok && !cg.recordPlaceable(recordLit) {
				// A record field of tagged-union type depends on that union
				// and its proven layout. Emit only those dependencies here,
				// preserving existing order for programs without such fields.
				if cg.emitRecordUnions(recordLit, unions, emittedUnions, tc) {
					progressed = true
				}
			}
			if ok && cg.recordPlaceable(recordLit) {
				cg.emitTypeUnit(unit, tc)
				progressed = true
				continue
			}
			stuck = append(stuck, unit)
		}
		pending = stuck
		if !progressed {
			break
		}
	}
	for _, unit := range pending {
		// Fail closed: a record whose field types never became placeable.
		cg.write(fmt.Sprintf("OAK_UNSUPPORTED_RECORD_LAYOUT(%s);\n\n", cg.cTypeName(unit.name)))
	}

	// Tagged unions after every record they might carry.
	for _, unit := range unions {
		if !emittedUnions[unit.name] {
			cg.emitTypeUnit(unit, tc)
		}
	}
	cg.emitAbstractAliases()
}

// emitRecordUnions emits, ahead of a stuck record, the tagged unions its
// fields name — a nullable field's concrete Option, or any declared union —
// provided every payload is placeable, so the union's proven layout
// (semir.TaggedUnionLayout, asserted by emitUnionLayout) makes the record
// placeable in turn. A union with an unplaceable payload is left for the
// ordinary emission pass and the record fails closed as before.
func (cg *CodeGenerator) emitRecordUnions(record *ast.RecordLiteral, unions []typeEmissionUnit, emitted map[string]bool, tc *typechecker.TypeChecker) bool {
	progressed := false
	for _, field := range record.FieldOrder {
		name, generic := cg.genericAnnotationName(field.Value)
		if !generic {
			ident, isIdent := field.Value.(*ast.Identifier)
			if !isIdent {
				continue
			}
			name = ident.Value
		}
		if _, placed := cg.recordLayouts[name]; placed {
			continue
		}
		for _, unit := range unions {
			if unit.name != name || emitted[unit.name] {
				continue
			}
			adt := unit.declared
			if adt == nil {
				specialized, ok := cg.specializeADT(cg.adtTypes[unit.instantiation.ADT], *unit.instantiation)
				if !ok {
					continue
				}
				adt = specialized
			}
			if _, ok := cg.unionPayloadRepresentations(adt); !ok {
				continue
			}
			cg.emitTypeUnit(unit, tc)
			emitted[unit.name] = true
			progressed = true
		}
	}
	return progressed
}

// emissionRecordLiteral resolves the (specialized) record literal a unit
// would emit, without emitting.
func (cg *CodeGenerator) emissionRecordLiteral(unit typeEmissionUnit) (*ast.RecordLiteral, bool) {
	if unit.declared != nil {
		return recordDefinitionShape(unit.declared)
	}
	template, declared := cg.adtTypes[unit.instantiation.ADT]
	if !declared {
		return nil, false
	}
	specialized, ok := cg.specializeADT(template, *unit.instantiation)
	if !ok {
		return nil, false
	}
	return recordDefinitionShape(specialized)
}

// recordPlaceable reports whether every field's representation is known —
// the emission-order dependency test.
func (cg *CodeGenerator) recordPlaceable(recordLit *ast.RecordLiteral) bool {
	if len(recordLit.FieldOrder) == 0 {
		return false
	}
	for _, field := range recordLit.FieldOrder {
		if _, ok := cg.fieldRepresentation(field.Name, field.Value, field.Align); !ok {
			return false
		}
	}
	return true
}

// emitTypeUnit emits one unit: declared types through emitADTType,
// instantiations through specialization (mirroring instantiateGenericADTs
// for a single instantiation).
func (cg *CodeGenerator) emitTypeUnit(unit typeEmissionUnit, tc *typechecker.TypeChecker) {
	if unit.declared != nil {
		cg.emitADTType(unit.declared, tc)
		return
	}
	inst := *unit.instantiation
	template, declared := cg.adtTypes[inst.ADT]
	if !declared || len(template.TypeParams) == 0 {
		return
	}
	mangled := inst.MangledName()
	if existing, collision := cg.adtTypes[mangled]; collision && len(existing.TypeParams) == 0 && existing != template {
		cg.write(fmt.Sprintf("OAK_MONOMORPHIZATION_NAME_COLLISION(%s);\n\n", cg.cTypeName(mangled)))
		return
	}
	specialized, ok := cg.specializeADT(template, inst)
	if !ok {
		cg.write(fmt.Sprintf("OAK_UNSUPPORTED_INSTANTIATION(%s);\n\n", cg.cTypeName(mangled)))
		return
	}
	cg.adtTypes[mangled] = specialized
	cg.emitADTType(specialized, tc)
}

// normalizeTypeExpression rewrites an application of a generic refinement
// to literals, left behind by template substitution (IrqId[N] with N := 4),
// to the name of its specialization; other type syntax is kept, arrays of
// such applications included.
func (cg *CodeGenerator) normalizeTypeExpression(expr ast.Expression) ast.Expression {
	index, isIndex := expr.(*ast.IndexExpression)
	if !isIndex || index.Dot {
		return expr
	}
	if cg.refinementName != nil {
		if name, ok := cg.refinementName(index); ok {
			return &ast.Identifier{Token: index.Token, Value: name}
		}
	}
	left := cg.normalizeTypeExpression(index.Left)
	inner := cg.normalizeTypeExpression(index.Index)
	if left == index.Left && inner == index.Index {
		return expr
	}
	return &ast.IndexExpression{Token: index.Token, Left: left, Index: inner, Dot: index.Dot}
}
