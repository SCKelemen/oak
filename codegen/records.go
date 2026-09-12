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
	"strings"

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
	// unsigned __int128 on every LP64 ABI Oak targets: 16 bytes, 16-aligned
	// (docs/spec/20-types.md section 11); the emitted sizeof/_Alignof
	// assertions ratify it.
	"u128": {Size: 16, Alignment: 16},
	"byte": {Size: 1, Alignment: 1}, "rune": {Size: 4, Alignment: 4},
	// Bool lowers to a C enum, int-sized on the recorded ILP32/LP64 target
	// model (docs/spec/92-ffi.md section 2.4); the emitted sizeof/offsetof
	// assertions verify this against the actual ABI at C compile time.
	"Bool": {Size: 4, Alignment: 4},
	// Floating-point fields (docs/spec/20-types.md section 11.3.1): the IEEE
	// binary32 and binary64 formats at their natural LP64 alignment, and the
	// f16/bf16 storage formats in their uint16_t carriers (section 11.3.8).
	"f32": {Size: 4, Alignment: 4}, "f64": {Size: 8, Alignment: 8},
	"f16": {Size: 2, Alignment: 2}, "bf16": {Size: 2, Alignment: 2},
	"f8e4m3": {Size: 1, Alignment: 1}, "f8e5m2": {Size: 1, Alignment: 1},
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
	// A function-typed field is a plain function pointer (docs/spec/90-
	// backend.md section 9): pointer-sized on the recorded LP64 target
	// model, the captured step of a record (ml F4); no closure environment
	// is ever stored.
	if _, isFn := typeExpr.(*ast.FunctionTypeExpression); isFn {
		return semir.RecordFieldRepresentation{Name: name, Size: 8, Alignment: 8}, true
	}
	// View and span fields are the {base, len} structs the backend emits: a
	// pointer and a u32 on the recorded LP64 target model, placed by the
	// natural layout (docs/spec/92-ffi.md section 2.4); the emitted
	// assertions make cc ratify the numbers.
	if indexExpr, isIndex := typeExpr.(*ast.IndexExpression); isIndex {
		// A Buffer field (docs/spec/92-ffi.md section 2.8.6) is the span
		// struct over its element type, the buffer's one representation.
		_, isBuffer := bufferElementSyntax(indexExpr)
		if marker, isMarker := indexExpr.Index.(*ast.Identifier); isBuffer || (isMarker && (marker.Value == "" || marker.Value == "*")) {
			layout, err := semir.NaturalRecordLayout([]semir.RecordFieldRepresentation{{Name: "base", Size: 8, Alignment: 8}, {Name: "len", Size: 4, Alignment: 4}})
			if err != nil {
				return semir.RecordFieldRepresentation{}, false
			}
			return semir.RecordFieldRepresentation{Name: name, Size: layout.Size, Alignment: layout.Alignment}, true
		}
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
	// A refinement-typed field has its base's representation (the typedef
	// of the base, docs/spec/20-types.md section 12).
	if adt, declared := cg.adtTypes[ident.Value]; declared && adt.Refinement != nil && len(adt.Variants) == 1 && adt.Variants[0].Payload != nil {
		return cg.naturalFieldRepresentation(name, adt.Variants[0].Payload)
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

// unionPayloadRepresentations resolves the size and alignment of every
// payload of a tagged union, reporting failure when one has no placeable
// representation (a string, a view, a record whose layout is unknown).
func (cg *CodeGenerator) unionPayloadRepresentations(adt *ast.ADTType) ([]semir.RecordFieldRepresentation, bool) {
	payloads := []semir.RecordFieldRepresentation{}
	for _, variant := range adt.Variants {
		if variant.Payload == nil {
			continue
		}
		rep, ok := cg.naturalFieldRepresentation(variant.Name.Value, variant.Payload)
		if !ok {
			return nil, false
		}
		payloads = append(payloads, rep)
	}
	return payloads, true
}

// emitUnionLayout binds an emitted tagged union to its proven layout
// (semir.TaggedUnionLayout): the u32 tag, then the payload union, as a C
// compile-time assertion cc ratifies. The layout is registered so records
// may embed the union and the boundary may rely on it
// (docs/spec/92-ffi.md section 2.6). A union with an unplaceable payload
// gets no assertion and no registration: it is fine inside Oak and simply
// has no proven shape at the boundary.
func (cg *CodeGenerator) emitUnionLayout(typeName, cName string, adt *ast.ADTType) {
	payloads, ok := cg.unionPayloadRepresentations(adt)
	if !ok {
		return
	}
	layout, err := semir.TaggedUnionLayout(payloads)
	if err != nil {
		return
	}
	if cg.recordLayouts == nil {
		cg.recordLayouts = make(map[string]semir.Representation)
	}
	cg.recordLayouts[typeName] = layout
	claims := fmt.Sprintf("sizeof(%s) == %du && _Alignof(%s) == %du && offsetof(%s, tag) == 0u", cName, layout.Size, cName, layout.Alignment, cName)
	if len(payloads) > 0 {
		claims += fmt.Sprintf(" && offsetof(%s, payload) == %du", cName, layout.Fields[1].Offset)
	}
	cg.write(fmt.Sprintf("typedef char oak_union_layout_%s[ (%s) ? 1 : -1 ];\n\n", cIdent(typeName), claims))
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
		spec.NoPadding = recordLit.Layout.NoPadding
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

	// Member types resolve before the struct opens: an owned-array field's
	// wrapper typedef (codegen/arrays.go) and a view field's typedef must
	// precede the record that embeds them.
	fieldTypes := make([]string, len(recordLit.FieldOrder))
	for i, field := range recordLit.FieldOrder {
		fieldTypes[i] = cg.parseTypeExpression(field.Value)
	}

	cg.write(fmt.Sprintf("typedef struct %s {\n", cName))
	for i, field := range recordLit.FieldOrder {
		// Declared per-field alignment lands on the member declarator
		// (GNU attribute form, valid in every mode of the recorded C
		// targets); the offsetof assertions below make cc ratify it.
		memberAlign := ""
		if field.Align != 0 {
			memberAlign = fmt.Sprintf(" __attribute__((aligned(%d)))", field.Align)
		}
		if fn, isFn := field.Value.(*ast.FunctionTypeExpression); isFn {
			cg.write(fmt.Sprintf("  %s%s;\n", cg.cFunctionPointer(fn, cIdent(field.Name)), memberAlign))
			continue
		}
		cg.write(fmt.Sprintf("  %s %s%s;\n", fieldTypes[i], cIdent(field.Name), memberAlign))
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
	if spec.NoPadding {
		// The density claim (docs/spec/40-records.md section 6a), ratified
		// by the C compiler: the struct is exactly the sum of its members.
		members := make([]string, 0, len(recordLit.FieldOrder))
		for _, field := range recordLit.FieldOrder {
			members = append(members, fmt.Sprintf("sizeof(((%s *)0)->%s)", cName, cIdent(field.Name)))
		}
		cg.write(fmt.Sprintf("typedef char oak_layout_dense_%s[ (sizeof(%s) == (%s)) ? 1 : -1 ];\n",
			typeName, cName, strings.Join(members, " + ")))
	}
	for _, placed := range layout.Fields {
		cg.write(fmt.Sprintf("typedef char oak_layout_off_%s_%s[ (offsetof(%s, %s) == %du) ? 1 : -1 ];\n",
			typeName, cIdent(placed.Name), cName, cIdent(placed.Name), placed.Offset))
	}
	cg.write("\n")
}
