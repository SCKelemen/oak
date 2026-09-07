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
	// Bool lowers to a C enum, int-sized on the recorded ILP32/LP64 target
	// model (docs/spec/92-ffi.md section 2.4); the emitted sizeof/offsetof
	// assertions verify this against the actual ABI at C compile time.
	"Bool": {Size: 4, Alignment: 4},
}

// fieldRepresentation resolves one field's size and alignment, reporting
// failure for types the v1 table cannot place. A declared per-field
// alignment (head(align: 64): Atomic[u32]) raises the natural alignment;
// declaring one BELOW natural is under-alignment — packing semantics — and
// fails closed rather than being approximated.
func (cg *CodeGenerator) fieldRepresentation(name string, typeExpr ast.Expression, declaredAlign uint32) (semir.RecordFieldRepresentation, bool) {
	rep, ok := cg.naturalFieldRepresentation(name, typeExpr)
	if !ok {
		return semir.RecordFieldRepresentation{}, false
	}
	if declaredAlign != 0 {
		if declaredAlign < rep.Alignment {
			return semir.RecordFieldRepresentation{}, false
		}
		rep.Alignment = declaredAlign
	}
	return rep, true
}

func (cg *CodeGenerator) naturalFieldRepresentation(name string, typeExpr ast.Expression) (semir.RecordFieldRepresentation, bool) {
	// Atomic cell fields take their carrier's size and alignment on the
	// recorded target model (lock-free C11 _Atomic over fixed-width
	// integers); the emitted sizeof/offsetof assertions verify this
	// against the actual ABI at C compile time.
	if carrier, isAtomic := atomicTypeCarrier(typeExpr); isAtomic {
		if fixed, ok := fixedFieldRepresentations[carrier]; ok {
			fixed.Name = name
			return fixed, true
		}
		return semir.RecordFieldRepresentation{}, false
	}
	// Generic-record instantiation fields (Idx[Thread], Ring[u8, 4])
	// resolve through the layout registry once their struct is emitted —
	// the dependency the fixpoint emission order satisfies.
	if mangled, isGeneric := cg.genericAnnotationName(typeExpr); isGeneric {
		if nested, placed := cg.recordLayouts[mangled]; placed {
			return semir.RecordFieldRepresentation{Name: name, Size: nested.Size, Alignment: nested.Alignment}, true
		}
		return semir.RecordFieldRepresentation{}, false
	}
	// Owned-array fields: [N]T occupies N contiguous elements at the
	// element's alignment (buffer: [16]u8 — the Ring shape).
	if indexExpr, isIndex := typeExpr.(*ast.IndexExpression); isIndex {
		if length, isFixed := indexExpr.Index.(*ast.IntegerLiteral); isFixed && length.Value > 0 {
			element, ok := cg.naturalFieldRepresentation(name, indexExpr.Left)
			if !ok {
				return semir.RecordFieldRepresentation{}, false
			}
			total := uint64(element.Size) * uint64(length.Value)
			if total > uint64(^uint32(0)) {
				return semir.RecordFieldRepresentation{}, false
			}
			return semir.RecordFieldRepresentation{Name: name, Size: uint32(total), Alignment: element.Alignment}, true
		}
	}
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
		fieldRep, ok := cg.fieldRepresentation(field.Name, field.Value, field.Align)
		if !ok {
			supported = false
			break
		}
		fields = append(fields, fieldRep)
	}

	// The declared layout spec (struct(packed), struct(align: N)) routes to
	// the spec-aware placement; the packed-atomic combination the checker
	// rejects also fails closed here (misaligned _Atomic is UB).
	spec := semir.RecordLayoutSpec{}
	if recordLit.Layout != nil {
		spec.Packed = recordLit.Layout.Packed
		spec.Align = recordLit.Layout.Align
	}
	if spec.Packed {
		for _, field := range recordLit.FieldOrder {
			if _, isAtomic := atomicTypeCarrier(field.Value); isAtomic {
				supported = false
			}
			if field.Align != 0 {
				supported = false
			}
		}
	}

	var layout semir.Representation
	if supported {
		computed, err := semir.RecordLayoutWithSpec(fields, spec)
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
		// Declared per-field alignment lands on the member declarator
		// (GNU attribute form, valid in every mode of the recorded C
		// targets); the offsetof assertions below make cc ratify it.
		memberAlign := ""
		if field.Align != 0 {
			memberAlign = fmt.Sprintf(" __attribute__((aligned(%d)))", field.Align)
		}
		// Array fields need the C declarator form: u8 buffer[ 16 ];
		if indexExpr, isIndex := field.Value.(*ast.IndexExpression); isIndex {
			if length, isFixed := indexExpr.Index.(*ast.IntegerLiteral); isFixed {
				cg.write(fmt.Sprintf("  %s %s[ %d ]%s;\n", cg.parseTypeExpression(indexExpr.Left), field.Name, length.Value, memberAlign))
				continue
			}
		}
		cg.write(fmt.Sprintf("  %s %s%s;\n", cg.parseTypeExpression(field.Value), field.Name, memberAlign))
	}
	// GNU attribute syntax (GCC/Clang, the recorded C targets): the layout
	// attributes sit between the member list and the typedef name.
	attributes := ""
	if spec.Packed {
		attributes += " __attribute__((packed))"
	}
	if spec.Align != 0 {
		attributes += fmt.Sprintf(" __attribute__((aligned(%d)))", spec.Align)
	}
	cg.write(fmt.Sprintf("}%s %s;\n", attributes, cName))

	// The proven layout (Oak.RecordLayoutRefinement / Oak.LayoutSpec),
	// enforced at C compile time: a mismatch makes the array type negative
	// and cc fails. Declared layout also pins the record's alignment.
	cg.write(fmt.Sprintf("typedef char oak_layout_size_%s[ (sizeof(%s) == %du) ? 1 : -1 ];\n",
		typeName, cName, layout.Size))
	if recordLit.Layout != nil {
		cg.write(fmt.Sprintf("typedef char oak_layout_align_%s[ (_Alignof(%s) == %du) ? 1 : -1 ];\n",
			typeName, cName, layout.Alignment))
	}
	for _, placed := range layout.Fields {
		cg.write(fmt.Sprintf("typedef char oak_layout_off_%s_%s[ (offsetof(%s, %s) == %du) ? 1 : -1 ];\n",
			typeName, placed.Name, cName, placed.Name, placed.Offset))
	}
	cg.write("\n")
}
