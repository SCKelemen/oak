package codegen

// C backend lowering for declared record types (docs/spec/40-records.md,
// docs/spec/45-representations.md): each record declaration emits a struct
// typedef in declaration order, and the placement proven by
// Oak.RecordLayout / Oak.RecordLayoutRefinement (computed by the
// transliterated semir.NaturalRecordLayout) is enforced against the C
// compiler with C99 negative-array-size assertions on sizeof and every
// field's offsetof. A record the layout table cannot place fails closed
// with a compile-breaking marker, never with a guessed layout.

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/semir"
)

// recordDefinitionShape recognizes a record type declaration, which the
// parser represents as an ADT with a single record-literal variant.
func recordDefinitionShape(adt *ast.ADTType) (*ast.RecordLiteral, bool) {
	if adt == nil || len(adt.Variants) != 1 || adt.Variants[0].Literal == nil {
		return nil, false
	}
	recordLit, ok := adt.Variants[0].Literal.(*ast.RecordLiteral)
	return recordLit, ok
}

// fixedFieldRepresentations maps the field types the v1 record backend can
// place: the fixed-width integers (and their aliases). Everything else is
// either a nested declared record (resolved via the registry) or
// unsupported (fail closed).
var fixedFieldRepresentations = map[string]semir.RecordFieldRepresentation{
	"u8": {Size: 1, Alignment: 1}, "i8": {Size: 1, Alignment: 1},
	"u16": {Size: 2, Alignment: 2}, "i16": {Size: 2, Alignment: 2},
	"u32": {Size: 4, Alignment: 4}, "i32": {Size: 4, Alignment: 4},
	"u64": {Size: 8, Alignment: 8}, "i64": {Size: 8, Alignment: 8},
	"byte": {Size: 1, Alignment: 1}, "rune": {Size: 4, Alignment: 4},
}

// fieldRepresentation resolves one field's size and alignment, reporting
// failure for types the v1 table cannot place.
func (cg *CodeGenerator) fieldRepresentation(name string, typeExpr ast.Expression) (semir.RecordFieldRepresentation, bool) {
	ident, isIdent := typeExpr.(*ast.Identifier)
	if !isIdent {
		return semir.RecordFieldRepresentation{}, false
	}
	if fixed, ok := fixedFieldRepresentations[ident.Value]; ok {
		fixed.Name = name
		return fixed, true
	}
	// Nested declared record: its resolved representation must already be
	// emitted (declaration before use, checked here, enforced by C).
	if nested, ok := cg.recordLayouts[ident.Value]; ok {
		return semir.RecordFieldRepresentation{Name: name, Size: nested.Size, Alignment: nested.Alignment}, true
	}
	return semir.RecordFieldRepresentation{}, false
}

// emitRecordTypeDef emits the struct typedef for a declared record type and
// the layout assertions binding the emitted C to the proven placement.
func (cg *CodeGenerator) emitRecordTypeDef(typeName string, recordLit *ast.RecordLiteral) {
	cName := cg.cTypeName(typeName)

	fields := make([]semir.RecordFieldRepresentation, 0, len(recordLit.FieldOrder))
	supported := true
	for _, field := range recordLit.FieldOrder {
		fieldRep, ok := cg.fieldRepresentation(field.Name, field.Value)
		if !ok {
			supported = false
			break
		}
		fields = append(fields, fieldRep)
	}

	var layout semir.Representation
	if supported {
		computed, err := semir.NaturalRecordLayout(fields)
		if err != nil {
			supported = false
		} else {
			layout = computed
		}
	}

	if !supported || len(recordLit.FieldOrder) == 0 {
		// Fail closed: no layout is guessed for what cannot be placed.
		cg.write(fmt.Sprintf("OAK_UNSUPPORTED_RECORD_LAYOUT(%s);\n\n", cName))
		return
	}

	if cg.recordLayouts == nil {
		cg.recordLayouts = make(map[string]semir.Representation)
	}
	cg.recordLayouts[typeName] = layout

	cg.write(fmt.Sprintf("typedef struct %s {\n", cName))
	for _, field := range recordLit.FieldOrder {
		cg.write(fmt.Sprintf("  %s %s;\n", cg.parseTypeExpression(field.Value), field.Name))
	}
	cg.write(fmt.Sprintf("} %s;\n", cName))

	// The proven layout (Oak.RecordLayoutRefinement), enforced at C compile
	// time: a mismatch makes the array type negative and cc fails.
	cg.write(fmt.Sprintf("typedef char oak_layout_size_%s[ (sizeof(%s) == %du) ? 1 : -1 ];\n",
		typeName, cName, layout.Size))
	for _, placed := range layout.Fields {
		cg.write(fmt.Sprintf("typedef char oak_layout_off_%s_%s[ (offsetof(%s, %s) == %du) ? 1 : -1 ];\n",
			typeName, placed.Name, cName, placed.Name, placed.Offset))
	}
	cg.write("\n")
}
