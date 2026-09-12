// Package nativegen is the native AArch64 backend for Oak bodies
// (docs/spec/94-assembler.md §9): it lowers a type-checked Oak function to
// an asm.Function — the same checked, verifiable, encodable object an
// `.oakasm` unit yields — so the compiler's own output is held to the seam
// checker's disciplines, proved against the Oak body by the verifier where
// the verifier reaches, and encoded by the Oak assembler into the companion
// object. The C backend stays the portable realization and the differential
// oracle.
//
// First increment — the fixed-width integer subset: parameters, locals,
// and results of u8/u16/u32/u64/i8/i16/i32/i64/Bool (or a unit result);
// literals, arithmetic (wrapping, as 20-types.md §11.1 states; division by
// zero traps), shifts (a count at or beyond the width traps), comparisons,
// `&&`/`||` (short-circuit), `!`/`-`/`^`, the primitive conversions
// `u32(x)`, the Bool conditional `c ? a | b` in value and statement
// position, typed locals and assignment, `while`/`break`, `assert`, and
// calls to program functions with scalar signatures. Anything else leaves
// the function to the C backend, with the reason.
//
// Values live in the frame: every parameter and local has an 8-byte slot;
// expressions evaluate into the scratch registers x9–x15 as a small operand
// stack, spilled around calls (the checker forbids reading a caller-saved
// register after `bl`). A value of a narrow type is kept normalized in its
// register — zero-extended when unsigned, sign-extended when signed — so
// comparisons and divisions read it as C does.
package nativegen

import (
	"fmt"
	"math"
	"strconv"
	"strings"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/semir"
	"github.com/SCKelemen/oak/typechecker"
)

// scalar is a fixed-width integer type of the subset.
type scalar struct {
	name    string
	bits    int
	signed  bool
	isBool  bool
	isFloat bool // f32/f64: held in the s/d view of a vector register
}

var scalars = map[string]scalar{
	"u8": {name: "u8", bits: 8}, "u16": {name: "u16", bits: 16}, "u32": {name: "u32", bits: 32}, "u64": {name: "u64", bits: 64},
	"i8": {name: "i8", bits: 8, signed: true}, "i16": {name: "i16", bits: 16, signed: true}, "i32": {name: "i32", bits: 32, signed: true}, "i64": {name: "i64", bits: 64, signed: true},
	"Bool": {name: "Bool", bits: 8, isBool: true}, "byte": {name: "u8", bits: 8},
	"f32": {name: "f32", bits: 32, isFloat: true}, "f64": {name: "f64", bits: 64, isFloat: true},
}

// scalarOf reads a type expression of the subset.
func scalarOf(expr ast.Expression) (scalar, bool) {
	if expr == nil {
		return scalar{}, false
	}
	s, ok := scalars[expr.String()]
	return s, ok
}

// wide reports a type held in an x register (64-bit); the rest use w.
func (s scalar) wide() bool { return s.bits == 64 }

// span is a span ([*]T, writable) or view ([]T) parameter of fixed-width
// elements: it arrives as a {base, u32 len} register pair and stays in
// those registers (the checker keys its facts on the bound base register).
type span struct {
	elem     scalar
	writable bool
	// elemLayout: the element type when the span holds records (elem unused).
	elemLayout *recordLayout
	baseReg    int // x register holding the base
	lenReg     int // w register holding the length
	// argBase/argLen: the argument registers the pair arrived in. In a
	// function that calls, the pair is parked in callee-saved registers
	// (baseReg/lenReg) by the prologue — the checker follows the copies —
	// so the callee's clobber of x0–x17 never touches it.
	argBase, argLen int
}

// spanTypeOf reads a span or view type of scalar or record elements.
func (g *generator) spanTypeOf(expr ast.Expression) (span, bool) {
	if sp, ok := spanOf(expr); ok {
		return sp, true
	}
	index, ok := expr.(*ast.IndexExpression)
	if !ok || index.Dot {
		return span{}, false
	}
	marker, isIdent := index.Index.(*ast.Identifier)
	if !isIdent || (marker.Value != "*" && marker.Value != "") {
		return span{}, false
	}
	name, isRecord := g.recordTypeName(index.Left)
	if !isRecord {
		return span{}, false
	}
	layout, err := g.layoutOf(name)
	if err != nil {
		return span{}, false
	}
	return span{elemLayout: layout, writable: marker.Value == "*"}, true
}

// sameElements reports two span shapes over the same element type.
func sameElements(a, b span) bool { return a.elem == b.elem && a.elemLayout == b.elemLayout }

// stride is the span's element size in bytes.
func (sp span) stride() int64 {
	if sp.elemLayout != nil {
		return sp.elemLayout.size
	}
	return int64(sp.elem.bits / 8)
}

// spanOf reads a span or view type of the subset.
func spanOf(expr ast.Expression) (span, bool) {
	index, ok := expr.(*ast.IndexExpression)
	if !ok || index.Dot {
		return span{}, false
	}
	marker, isIdent := index.Index.(*ast.Identifier)
	if !isIdent || (marker.Value != "*" && marker.Value != "") {
		return span{}, false
	}
	elem, ok := scalarOf(index.Left)
	if !ok || elem.isBool {
		return span{}, false
	}
	return span{elem: elem, writable: marker.Value == "*"}, true
}

// arrayLocal is an owned array `buf: [N]T` living in the frame: N*sizeof(T)
// bytes at a fixed slot offset. Its elements are reached through a frame
// address (`add xB, sp, #off`) under a constant index guard (`cmp wI, #N;
// b.hs trap`) — the checker admits exactly that shape (asm/check.go,
// frameArrayAccess) — and `view(&buf)` / `span(&buf)` hand a callee the
// {address, N} pair.
type arrayLocal struct {
	offset int64 // slot offset (slotMem-relative), or the offset from reg
	elem   scalar
	length int64
	// elemLayout: the element type when the array holds records (elem unused).
	elemLayout *recordLayout
	// inReg: the array lives at [x<reg>, #offset] (inside a dynamically
	// addressed record element) rather than in the frame; temps are the
	// scratch registers to release once the place is consumed.
	inReg bool
	reg   int
	temps []int
}

// elemSize is the array's element stride in bytes.
func (a *arrayLocal) elemSize() int64 {
	if a.elemLayout != nil {
		return a.elemLayout.size
	}
	return int64(a.elem.bits / 8)
}

// loc is a memory location: sp-relative (a frame slot) or register-based.
type loc struct {
	inReg  bool
	reg    int
	offset int64
}

func (l loc) plus(delta int64) loc { return loc{inReg: l.inReg, reg: l.reg, offset: l.offset + delta} }

// memOf is the memory operand for a location.
func (g *generator) memOf(l loc) asm.Memory {
	if l.inReg {
		return asm.Memory{Base: xr(l.reg), Offset: l.offset}
	}
	return g.slotMem(l.offset)
}

// alignmentOf is the alignment the checker sees for a location: the frame
// offset's, or the offset from the register (element addresses are
// multiples of the element's alignment).
func (g *generator) alignmentOf(l loc) int64 {
	if l.inReg {
		return l.offset
	}
	return g.slotMem(l.offset).Offset
}

// arrayTypeOf reads an owned array type [N]T of scalar or record elements.
func (g *generator) arrayTypeOf(expr ast.Expression) (elem scalar, elemLayout *recordLayout, length int64, err error) {
	if e, n, ok := arrayOf(expr); ok {
		return e, nil, n, nil
	}
	index, isIndex := expr.(*ast.IndexExpression)
	if !isIndex || index.Dot {
		return scalar{}, nil, 0, unsupported("%s is not an array type", expr.String())
	}
	n, isLit := index.Index.(*ast.IntegerLiteral)
	if !isLit || n.Value <= 0 {
		return scalar{}, nil, 0, unsupported("%s is not an array type", expr.String())
	}
	name, isRecord := g.recordTypeName(index.Left)
	if !isRecord {
		return scalar{}, nil, 0, unsupported("%s is not an array type of scalars or records", expr.String())
	}
	layout, err := g.layoutOf(name)
	if err != nil {
		return scalar{}, nil, 0, err
	}
	return scalar{}, layout, n.Value, nil
}

// isArrayType reports an owned array type of any element.
func (g *generator) isArrayType(expr ast.Expression) bool {
	index, isIndex := expr.(*ast.IndexExpression)
	if !isIndex || index.Dot {
		return false
	}
	n, isLit := index.Index.(*ast.IntegerLiteral)
	if !isLit || n.Value <= 0 {
		return false
	}
	if _, ok := scalarOf(index.Left); ok {
		return true
	}
	_, isRecord := g.recordTypeName(index.Left)
	return isRecord
}

// arrayOf reads an owned array type [N]T of scalar elements.
func arrayOf(expr ast.Expression) (elem scalar, length int64, ok bool) {
	index, isIndex := expr.(*ast.IndexExpression)
	if !isIndex || index.Dot {
		return scalar{}, 0, false
	}
	n, isLit := index.Index.(*ast.IntegerLiteral)
	if !isLit || n.Value <= 0 {
		return scalar{}, 0, false
	}
	elem, ok = scalarOf(index.Left)
	if !ok || elem.isBool {
		return scalar{}, 0, false
	}
	return elem, n.Value, true
}

// recordLayout is a declared record type's placement — the natural ordered
// layout `semir.RecordLayoutWithSpec` computes, the same numbers the C
// backend asserts against the C compiler (codegen/records.go) — restricted
// to scalar fields. A record local occupies size bytes of the frame; a field
// is read and written at its own width at offset.
type recordLayout struct {
	name     string
	size     int64
	align    int64
	hasFloat bool // a float field anywhere inside (the vector save area is reserved)
	fields   map[string]recordField
	order    []string
	// A tagged union (ADT) is a synthetic record: the u32 field "tag" at
	// offset 0 and one field per payload-carrying variant, named after the
	// variant, at the payload union's offset (semir.TaggedUnionLayout — the
	// numbers the C backend asserts). variants maps each variant to its
	// tag value and payload field ("" for a bare variant).
	variants map[string]variantInfo
}

type variantInfo struct {
	tag     int64
	payload string
}

func (l *recordLayout) isADT() bool { return l.variants != nil }

// fieldKind: a scalar field, a nested declared record, or an owned array
// of scalars.
type fieldKind int

const (
	fieldScalar fieldKind = iota
	fieldRecord
	fieldArray
)

type recordField struct {
	kind   fieldKind
	typ    scalar // the scalar, or the array's element type
	offset int64
	size   int64         // the C field's size: a Bool field is the 4-byte enum
	layout *recordLayout // fieldRecord: the nested record
	length int64         // fieldArray: the element count
}

// scalarPlace is a scalar field's location (a frame slot, or an offset from
// an element address register).
type scalarPlace struct {
	offset   int64
	typ      scalar
	inReg    bool
	reg      int
	temps    []int
	readOnly bool
}

func (s *scalarPlace) loc() loc { return loc{inReg: s.inReg, reg: s.reg, offset: s.offset} }

// place is what an access chain names in the frame: a record (a local or a
// nested record field), an array (a local or an array field), or a scalar
// field. An expression that is not such a chain resolves to the zero place.
type place struct {
	rec *recordLocal
	arr *arrayLocal
	sc  *scalarPlace
}

// recordParam is a record parameter's arrival: reg is its first register,
// regs how many chunks it spans (1 when indirect: the address of the
// caller's copy). It becomes the record local `local` in the prologue.
type recordParam struct {
	layout   *recordLayout
	reg      int
	regs     int
	indirect bool
	local    *recordLocal
}

// isHFA reports a homogeneous floating-point aggregate (all fields one
// float type, at most four): AAPCS64 passes it in v registers, which v1
// leaves to the C backend.
func (l *recordLayout) isHFA() bool {
	if len(l.order) == 0 || len(l.order) > 4 {
		return false
	}
	first := l.fields[l.order[0]].typ
	if !first.isFloat {
		return false
	}
	for _, name := range l.order {
		if l.fields[name].typ != first {
			return false
		}
	}
	return true
}

// chunks is the number of x registers a record of this size travels in.
func (l *recordLayout) chunks() int { return int((l.size + 7) / 8) }

// Composites is the checker's table of the program's placeable record and
// tagged-union types (asm.Function.Composites): every declaration whose
// layout the backend can place, by name.
func Composites(records map[string]*ast.RecordLiteral, adts map[string]*ast.ADTType) map[string]asm.Composite {
	g := &generator{recordDecls: records, adtDecls: adts, layouts: map[string]*recordLayout{}}
	out := map[string]asm.Composite{}
	for name := range records {
		if layout, err := g.layoutOf(name); err == nil {
			out[name] = asm.Composite{Size: layout.size, HFA: layout.isHFA()}
		}
	}
	for name := range adts {
		if layout, err := g.layoutOf(name); err == nil {
			out[name] = asm.Composite{Size: layout.size}
		}
	}
	return out
}

// recordLocal is an owned record in the frame, or (inReg) a record
// element addressed through a register: [x<reg>, #offset].
type recordLocal struct {
	offset int64 // slot offset (slotMem-relative), or the offset from reg
	layout *recordLayout
	inReg  bool
	reg    int
	temps  []int // scratch registers to release once the place is consumed
	// readOnly: an element of a view ([]T): stores are refused.
	readOnly bool
}

func (r *recordLocal) loc() loc { return loc{inReg: r.inReg, reg: r.reg, offset: r.offset} }

func (a *arrayLocal) loc() loc { return loc{inReg: a.inReg, reg: a.reg, offset: a.offset} }

// releaseTemps frees the scratch registers a dynamically addressed place
// holds (the element address).
func (g *generator) releaseTemps(temps []int) {
	for _, r := range temps {
		g.release(r)
	}
}

// fieldRepresentations: the C backend's sizes and alignments of the scalar
// field types (codegen/records.go fixedFieldRepresentations).
var fieldRepresentations = map[string]semir.RecordFieldRepresentation{
	"u8": {Size: 1, Alignment: 1}, "i8": {Size: 1, Alignment: 1}, "byte": {Size: 1, Alignment: 1},
	"u16": {Size: 2, Alignment: 2}, "i16": {Size: 2, Alignment: 2},
	"u32": {Size: 4, Alignment: 4}, "i32": {Size: 4, Alignment: 4}, "f32": {Size: 4, Alignment: 4},
	"u64": {Size: 8, Alignment: 8}, "i64": {Size: 8, Alignment: 8}, "f64": {Size: 8, Alignment: 8},
	"Bool": {Size: 4, Alignment: 4},
}

// layoutOf places a declared record type, or reports why it is outside the
// subset (a non-scalar field, a packed layout, an under-aligned field).
func (g *generator) layoutOf(name string) (*recordLayout, error) {
	if layout, done := g.layouts[name]; done {
		return layout, nil
	}
	decl, isRecord := g.recordDecls[name]
	if !isRecord {
		if adt, isADT := g.adtDecls[name]; isADT {
			return g.adtLayoutOf(name, adt)
		}
		return nil, unsupported("the type %s is not a declared record", name)
	}
	if decl.Layout != nil && decl.Layout.Packed {
		return nil, unsupported("the packed record %s", name)
	}
	if g.placing[name] {
		return nil, unsupported("the record %s contains itself", name)
	}
	if g.placing == nil {
		g.placing = map[string]bool{}
	}
	g.placing[name] = true
	defer delete(g.placing, name)
	var reps []semir.RecordFieldRepresentation
	layout := &recordLayout{name: name, fields: map[string]recordField{}}
	for _, field := range decl.FieldOrder {
		var rep semir.RecordFieldRepresentation
		var placed recordField
		switch {
		case func() bool { _, ok := scalarOf(field.Value); return ok }():
			typ, _ := scalarOf(field.Value)
			fixed, placeable := fieldRepresentations[field.Value.String()]
			if !placeable {
				return nil, unsupported("the record %s (field %s: %s)", name, field.Name, field.Value.String())
			}
			rep = fixed
			placed = recordField{kind: fieldScalar, typ: typ}
			layout.hasFloat = layout.hasFloat || typ.isFloat
		case func() bool { _, ok := g.recordTypeName(field.Value); return ok }():
			nestedName, _ := g.recordTypeName(field.Value)
			nested, err := g.layoutOf(nestedName)
			if err != nil {
				return nil, err
			}
			rep = semir.RecordFieldRepresentation{Size: uint32(nested.size), Alignment: uint32(nested.align)}
			placed = recordField{kind: fieldRecord, layout: nested}
			layout.hasFloat = layout.hasFloat || nested.hasFloat
		case g.isArrayType(field.Value):
			arrayRep, arrayField, err := g.fieldOf("the record "+name, field.Value)
			if err != nil {
				return nil, err
			}
			rep, placed = arrayRep, arrayField
			layout.hasFloat = layout.hasFloat || placed.mentionsFloat()
		default:
			return nil, unsupported("the record %s (field %s: %s)", name, field.Name, field.Value.String())
		}
		if field.Align != 0 {
			if field.Align < rep.Alignment {
				return nil, unsupported("the record %s (field %s under-aligned)", name, field.Name)
			}
			rep.Alignment = field.Align
		}
		rep.Name = field.Name
		reps = append(reps, rep)
		placed.size = int64(rep.Size)
		layout.fields[field.Name] = placed
		layout.order = append(layout.order, field.Name)
	}
	spec := semir.RecordLayoutSpec{}
	if decl.Layout != nil {
		spec.Align = decl.Layout.Align
	}
	placed, err := semir.RecordLayoutWithSpec(reps, spec)
	if err != nil || len(reps) == 0 {
		return nil, unsupported("the record %s has no placeable layout", name)
	}
	for _, placedField := range placed.Fields {
		field := layout.fields[placedField.Name]
		field.offset = int64(placedField.Offset)
		layout.fields[placedField.Name] = field
	}
	layout.size = int64(placed.Size)
	layout.align = int64(placed.Alignment)
	g.layouts[name] = layout
	return layout, nil
}

// fieldOf places one member type (a scalar, a declared record, an owned
// array of scalars) as a record field representation and its field shape.
func (g *generator) fieldOf(owner string, member ast.Expression) (semir.RecordFieldRepresentation, recordField, error) {
	if typ, isScalar := scalarOf(member); isScalar {
		fixed, placeable := fieldRepresentations[member.String()]
		if !placeable {
			return semir.RecordFieldRepresentation{}, recordField{}, unsupported("%s (member type %s)", owner, member.String())
		}
		return fixed, recordField{kind: fieldScalar, typ: typ}, nil
	}
	if nestedName, isRecord := g.recordTypeName(member); isRecord {
		nested, err := g.layoutOf(nestedName)
		if err != nil {
			return semir.RecordFieldRepresentation{}, recordField{}, err
		}
		return semir.RecordFieldRepresentation{Size: uint32(nested.size), Alignment: uint32(nested.align)}, recordField{kind: fieldRecord, layout: nested}, nil
	}
	if elem, length, isArray := arrayOf(member); isArray {
		fixed, placeable := fieldRepresentations[elem.name]
		if !placeable {
			return semir.RecordFieldRepresentation{}, recordField{}, unsupported("%s (member type %s)", owner, member.String())
		}
		return semir.RecordFieldRepresentation{Size: fixed.Size * uint32(length), Alignment: fixed.Alignment}, recordField{kind: fieldArray, typ: elem, length: length}, nil
	}
	if g.isArrayType(member) {
		// An array of records: N contiguous records at the record's alignment.
		_, elemLayout, length, err := g.arrayTypeOf(member)
		if err != nil {
			return semir.RecordFieldRepresentation{}, recordField{}, err
		}
		return semir.RecordFieldRepresentation{Size: uint32(elemLayout.size) * uint32(length), Alignment: uint32(elemLayout.align)}, recordField{kind: fieldArray, layout: elemLayout, length: length}, nil
	}
	return semir.RecordFieldRepresentation{}, recordField{}, unsupported("%s (member type %s)", owner, member.String())
}

func (f recordField) mentionsFloat() bool {
	if f.layout != nil {
		return f.layout.hasFloat
	}
	return f.typ.isFloat
}

// adtLayoutOf places a tagged union as a synthetic record: the u32 tag,
// then every payload at the union's offset (semir.TaggedUnionLayout).
func (g *generator) adtLayoutOf(name string, adt *ast.ADTType) (*recordLayout, error) {
	if len(adt.TypeParams) > 0 {
		return nil, unsupported("the generic type %s", name)
	}
	if g.placing[name] {
		return nil, unsupported("the type %s contains itself", name)
	}
	if g.placing == nil {
		g.placing = map[string]bool{}
	}
	g.placing[name] = true
	defer delete(g.placing, name)
	layout := &recordLayout{name: name, fields: map[string]recordField{}, variants: map[string]variantInfo{}}
	layout.fields["tag"] = recordField{kind: fieldScalar, typ: scalars["u32"], size: 4}
	layout.order = append(layout.order, "tag")
	var payloads []semir.RecordFieldRepresentation
	pending := map[string]recordField{}
	for i, variant := range adt.Variants {
		info := variantInfo{tag: int64(i)}
		if i < len(adt.TagValues) {
			info.tag = int64(adt.TagValues[i])
		}
		if variant.Payload != nil {
			rep, field, err := g.fieldOf("the type "+name, variant.Payload)
			if err != nil {
				return nil, err
			}
			rep.Name = variant.Name.Value
			payloads = append(payloads, rep)
			field.size = int64(rep.Size)
			pending[variant.Name.Value] = field
			info.payload = variant.Name.Value
			layout.hasFloat = layout.hasFloat || field.mentionsFloat()
		}
		layout.variants[variant.Name.Value] = info
	}
	placed, err := semir.TaggedUnionLayout(payloads)
	if err != nil {
		return nil, unsupported("the type %s has no placeable layout", name)
	}
	if len(payloads) > 0 {
		at := int64(placed.Fields[1].Offset)
		for _, variant := range adt.Variants {
			if field, has := pending[variant.Name.Value]; has {
				field.offset = at
				layout.fields[variant.Name.Value] = field
				layout.order = append(layout.order, variant.Name.Value)
			}
		}
	}
	layout.size = int64(placed.Size)
	layout.align = int64(placed.Alignment)
	g.layouts[name] = layout
	return layout, nil
}

// variantTypeName names the ADT a variant expression builds: its written
// type, the checker's resolution, or the expected type.
func (g *generator) variantTypeName(e *ast.VariantExpression, expected *recordLayout) (string, error) {
	if e.TypeName != nil {
		return e.TypeName.Value, nil
	}
	if g.tc != nil {
		if name, resolved := g.tc.VariantResolution(e); resolved {
			return name, nil
		}
	}
	if expected != nil {
		return expected.name, nil
	}
	return "", unsupported("the variant %s without a resolved type", e.String())
}

// placeOf resolves an access chain to its frame place: a record or array
// local, `r.f` on a record place (a scalar, nested record, or array field),
// recursively. An expression that is no such chain is the zero place.
func (g *generator) placeOf(expr ast.Expression) (place, error) {
	switch e := expr.(type) {
	case *ast.Identifier:
		if rec, isRecord := g.records[e.Value]; isRecord {
			return place{rec: rec}, nil
		}
		if arr, isArray := g.arrays[e.Value]; isArray {
			return place{arr: arr}, nil
		}
	case *ast.IndexExpression:
		if !e.Dot {
			// An element of an array or span of records: `pool[i]`.
			if ident, isIdent := e.Left.(*ast.Identifier); isIdent {
				if sp, isSpan := g.spans[ident.Value]; isSpan && sp.elemLayout != nil {
					return g.spanRecordElement(sp, e.Index)
				}
			}
			base, err := g.placeOf(e.Left)
			if err != nil {
				return place{}, err
			}
			if base.arr == nil || base.arr.elemLayout == nil {
				return place{}, nil
			}
			return g.recordElement(base.arr, e.Index)
		}
		base, err := g.placeOf(e.Left)
		if err != nil {
			return place{}, err
		}
		if base.rec == nil {
			call, isCall := e.Left.(*ast.InvocationExpression)
			if !isCall {
				return place{}, unsupported("a field access on %s (not a record)", e.Left.String())
			}
			// A field of a call's record result: the call lands in a temp.
			rec, err := g.callRecord(call)
			if err != nil {
				return place{}, err
			}
			base = place{rec: rec}
		}
		name, isName := e.Index.(*ast.Identifier)
		if !isName {
			return place{}, unsupported("a field access %s", e.String())
		}
		field, has := base.rec.layout.fields[name.Value]
		if !has {
			return place{}, unsupported("the field %s of %s", name.Value, base.rec.layout.name)
		}
		at := base.rec.loc().plus(field.offset)
		switch field.kind {
		case fieldScalar:
			return place{sc: &scalarPlace{offset: at.offset, typ: field.typ, inReg: at.inReg, reg: at.reg, temps: base.rec.temps, readOnly: base.rec.readOnly}}, nil
		case fieldRecord:
			return place{rec: &recordLocal{offset: at.offset, layout: field.layout, inReg: at.inReg, reg: at.reg, temps: base.rec.temps, readOnly: base.rec.readOnly}}, nil
		default:
			if base.rec.readOnly {
				return place{}, unsupported("the array field %s of an element read through a view", e.String())
			}
			return place{arr: &arrayLocal{offset: at.offset, elem: field.typ, elemLayout: field.layout, length: field.length, inReg: at.inReg, reg: at.reg, temps: base.rec.temps}}, nil
		}
	}
	return place{}, nil
}

// recordElement addresses one element of an array of records: a literal
// index inside the array is a static place; any other index goes through
// the element idiom the checker admits — the array's frame address, the
// constant guard `cmp wI, #N; b.hs trap`, then `add xE, xB, wI, uxtw #s`
// for a power-of-two stride up to 16 bytes or `movz wK, #stride; umaddl
// xE, wI, wK, xB` otherwise — yielding a record place at [xE].
func (g *generator) recordElement(arr *arrayLocal, index ast.Expression) (place, error) {
	stride := arr.elemLayout.size
	if k, isConst := constantValue(index); isConst && k >= 0 && k < arr.length {
		at := arr.loc().plus(k * stride)
		return place{rec: &recordLocal{offset: at.offset, layout: arr.elemLayout, inReg: at.inReg, reg: at.reg, temps: arr.temps}}, nil
	}
	if arr.inReg {
		return place{}, unsupported("a computed index into an array of records inside a computed element")
	}
	idxType, err := g.typeOf(index, nil)
	if err != nil {
		return place{}, err
	}
	if idxType.wide() || idxType.signed || idxType.isBool || idxType.isFloat {
		return place{}, unsupported("an element index of type %s (the array idiom walks by a u32 index)", idxType.name)
	}
	r, err := g.expr(index, &idxType)
	if err != nil {
		return place{}, err
	}
	base, err := g.alloc(scalars["u64"])
	if err != nil {
		return place{}, err
	}
	element, err := g.alloc(scalars["u64"])
	if err != nil {
		return place{}, err
	}
	g.emit("add", xr(base), sp(), imm(g.slotMem(arr.offset).Offset))
	g.usedTrap = true
	g.emit("cmp", wr(r), imm(arr.length))
	g.branch("hs", g.trap)
	if stride > 0 && stride&(stride-1) == 0 && stride <= 16 {
		g.emit("add", xr(element), xr(base), asm.Extended{Reg: wr(r), Kind: "uxtw", Amount: int64(log2Bytes(int(stride)))})
	} else {
		if stride >= 1<<16 {
			return place{}, unsupported("a record stride of %d bytes", stride)
		}
		strideReg, err := g.alloc(scalars["u32"])
		if err != nil {
			return place{}, err
		}
		g.emit("movz", wr(strideReg), imm(stride))
		g.emit("umaddl", xr(element), wr(r), wr(strideReg), xr(base))
		g.release(strideReg)
	}
	g.release(base)
	g.release(r)
	return place{rec: &recordLocal{layout: arr.elemLayout, inReg: true, reg: element, temps: []int{element}}}, nil
}

// recordLayoutOfExpr resolves the record type an expression denotes without
// emitting code (typeOf runs before lowering): a record local, a nested
// record field, a typed literal, or a call returning a record.
func (g *generator) recordLayoutOfExpr(expr ast.Expression) (*recordLayout, error) {
	switch e := expr.(type) {
	case *ast.Identifier:
		if rec, isRecord := g.records[e.Value]; isRecord {
			return rec.layout, nil
		}
	case *ast.IndexExpression:
		if e.Dot {
			base, err := g.recordLayoutOfExpr(e.Left)
			if err != nil {
				return nil, err
			}
			name, isName := e.Index.(*ast.Identifier)
			if !isName {
				return nil, unsupported("a field access %s", e.String())
			}
			field, has := base.fields[name.Value]
			if !has {
				return nil, unsupported("the field %s of %s", name.Value, base.name)
			}
			if field.kind == fieldRecord {
				return field.layout, nil
			}
		} else if layout := g.recordArrayElementLayout(e.Left); layout != nil {
			return layout, nil
		}
	case *ast.RecordLiteral:
		if e.TypeName != nil {
			return g.layoutOf(e.TypeName.Value)
		}
	case *ast.VariantExpression:
		name, err := g.variantTypeName(e, nil)
		if err != nil {
			return nil, err
		}
		return g.layoutOf(name)
	case *ast.InvocationExpression:
		if ident, isIdent := e.Function.(*ast.Identifier); isIdent {
			if callee, known := g.functions[ident.Value]; known && callee.ReturnType != nil {
				if name, isRecord := g.recordTypeName(callee.ReturnType); isRecord {
					return g.layoutOf(name)
				}
			}
		}
	}
	return nil, unsupported("%s is not a record", expr.String())
}

// spanRecordElement addresses one element of a span of records through the
// checker's span element idiom: the index guarded against the length
// register, then `add xE, xB, wI, uxtw #s` or `movz`/`umaddl` by the
// record's stride; the place is read-only through a view.
func (g *generator) spanRecordElement(sp span, index ast.Expression) (place, error) {
	r, err := g.guardedIndex(sp, index)
	if err != nil {
		return place{}, err
	}
	element, err := g.alloc(scalars["u64"])
	if err != nil {
		return place{}, err
	}
	stride := sp.elemLayout.size
	if stride > 0 && stride&(stride-1) == 0 && stride <= 16 {
		g.emit("add", xr(element), xr(sp.baseReg), asm.Extended{Reg: wr(r), Kind: "uxtw", Amount: int64(log2Bytes(int(stride)))})
	} else {
		if stride >= 1<<16 {
			return place{}, unsupported("a record stride of %d bytes", stride)
		}
		strideReg, err := g.alloc(scalars["u32"])
		if err != nil {
			return place{}, err
		}
		g.emit("movz", wr(strideReg), imm(stride))
		g.emit("umaddl", xr(element), wr(r), wr(strideReg), xr(sp.baseReg))
		g.release(strideReg)
	}
	g.release(r)
	return place{rec: &recordLocal{layout: sp.elemLayout, inReg: true, reg: element, temps: []int{element}, readOnly: !sp.writable}}, nil
}

// recordArrayElementLayout is the element type of an array of records the
// expression names (a local, or an array field through any nesting), or
// nil. Resolved without emitting code.
func (g *generator) recordArrayElementLayout(expr ast.Expression) *recordLayout {
	switch e := expr.(type) {
	case *ast.Identifier:
		if arr, isArray := g.arrays[e.Value]; isArray {
			return arr.elemLayout
		}
		if sp, isSpan := g.spans[e.Value]; isSpan {
			return sp.elemLayout
		}
	case *ast.IndexExpression:
		if e.Dot {
			base, err := g.recordLayoutOfExpr(e.Left)
			if err != nil {
				return nil
			}
			if name, isName := e.Index.(*ast.Identifier); isName {
				if field, has := base.fields[name.Value]; has && field.kind == fieldArray {
					return field.layout
				}
			}
		}
	}
	return nil
}

// copyUnit is the widest access (8, 4, 2, 1 bytes) every offset is aligned
// to — the checker requires frame accesses naturally aligned.
func copyUnit(offsets ...int64) int64 {
	unit := int64(8)
	for unit > 1 {
		aligned := true
		for _, offset := range offsets {
			if offset%unit != 0 {
				aligned = false
			}
		}
		if aligned {
			break
		}
		unit /= 2
	}
	return unit
}

// accessPair names the load and store of a byte count through a general
// register (its x view for 8 bytes, w otherwise).
func accessPair(bytes int64) (load, store string) {
	switch bytes {
	case 8, 4:
		return "ldr", "str"
	case 2:
		return "ldrh", "strh"
	}
	return "ldrb", "strb"
}

// copyBytes copies size bytes between two locations through a scratch
// register, in the widest aligned units then a narrowing tail — exactly the
// bytes of the value, never a neighbor's.
func (g *generator) copyBytes(dst, src loc, size int64) error {
	tmp, err := g.alloc(scalars["u64"])
	if err != nil {
		return err
	}
	unit := copyUnit(g.alignmentOf(dst), g.alignmentOf(src))
	off := int64(0)
	for bytes := unit; bytes >= 1; bytes /= 2 {
		for off+bytes <= size {
			load, store := accessPair(bytes)
			r := wr(tmp)
			if bytes == 8 {
				r = xr(tmp)
			}
			g.emit(load, r, g.memOf(src.plus(off)))
			g.emit(store, r, g.memOf(dst.plus(off)))
			off += bytes
		}
	}
	g.release(tmp)
	return nil
}

// slotLoc is a frame-slot location.
func slotLoc(offset int64) loc { return loc{offset: offset} }

// recordTypeName reads a type expression naming a declared record.
func (g *generator) recordTypeName(expr ast.Expression) (string, bool) {
	ident, isIdent := expr.(*ast.Identifier)
	if !isIdent {
		return "", false
	}
	if _, isRecord := g.recordDecls[ident.Value]; isRecord {
		return ident.Value, true
	}
	_, isADT := g.adtDecls[ident.Value]
	return ident.Value, isADT
}

// Unsupported reports why a function is left to the C backend.
type Unsupported struct{ Reason string }

func (u Unsupported) Error() string { return u.Reason }

func unsupported(format string, args ...interface{}) Unsupported {
	return Unsupported{fmt.Sprintf(format, args...)}
}

// generator holds one function's lowering.
type generator struct {
	fn        *ast.FunctionStatement
	tc        *typechecker.TypeChecker
	functions map[string]*ast.FunctionStatement
	result    *scalar

	items  []asm.Item
	slots  map[string]int64       // variable → frame offset (relative to the frame base after the prologue)
	types  map[string]scalar      // variable → type
	spans  map[string]span        // span and view parameters, register-resident
	arrays map[string]*arrayLocal // owned array locals, in the frame
	// Declared record types of the program, their placements, and the
	// record locals in the frame.
	recordDecls map[string]*ast.RecordLiteral
	adtDecls    map[string]*ast.ADTType
	layouts     map[string]*recordLayout
	records     map[string]*recordLocal
	// Record parameters and results under AAPCS64's composite rules: up to
	// 16 bytes as ceil(size/8) x-register chunks, larger by reference to a
	// copy the caller owns (a result beyond 16 bytes is written through the
	// area the caller passes in x8, parked in a callee-saved register when
	// the body calls).
	recordParams   map[string]*recordParam
	placing        map[string]bool // record types being placed (cycle guard)
	resultRecord   *recordLayout
	resultIndirect bool
	resultAreaReg  int // the register holding the result area's address (x8 or its parked copy)
	usedX8         bool
	temps          int
	head           string // the loop header a tail self-call jumps to
	// Variables live in the callee-saved registers x19–x28 in declaration
	// order (saved in the prologue, restored before ret), and in frame
	// slots once those run out; regs maps a variable to its register.
	regs       map[string]int
	usedCallee int
	saveArea   int64 // bytes reserved for the callee-saved pairs (fixed once any variable exists)
	// The vector file for floating point: scratch and callee-saved pools,
	// and the d8–d15 save area (fixed once the function mentions a float).
	freeF       []int
	usedCalleeV int
	saveAreaV   int64
	usedFloat   bool
	scopes      []map[string]slotBinding
	nslots      int64
	spill       map[int]int64 // scratch register → its spill slot offset
	free        []int         // free scratch registers
	live        []int         // allocated scratch registers, allocation order
	labels      int
	loops       []string // break targets
	hasCalls    bool
	line        int
	trap        string // the trap block's label (division by zero, shift overflow, assert)
	usedTrap    bool
	// terminated: an unconditional jump was emitted and no label has
	// followed — instructions there are unreachable and are not emitted (the
	// checker refuses them).
	terminated bool
}

type slotBinding struct {
	offset int64
	typ    scalar
	reg    int          // callee-saved register, or -1 for a slot
	arr    *arrayLocal  // an owned array local (offset/typ/reg unused)
	rec    *recordLocal // an owned record local (offset/typ/reg unused)
	sp     *span        // a local span or view, register-resident
}

const scratchLow, scratchHigh = 9, 15
const calleeLow, calleeHigh = 19, 28

// The vector file: v16–v23 scratch (caller-saved), v8–v15 for float
// variables (callee-saved: their d views are saved and restored).
const vecScratchLow, vecScratchHigh = 16, 23
const vecCalleeLow, vecCalleeHigh = 8, 15

// Compile lowers one Oak function. functions maps every program function by
// name (callees' signatures), records every declared record type by name
// (their field lists); tc is the checker that typed the program.
func Compile(fn *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, records map[string]*ast.RecordLiteral, adts map[string]*ast.ADTType, tc *typechecker.TypeChecker) (*asm.Function, error) {
	if fn.Body == nil || fn.ExternSymbol != "" || fn.Receiver != nil || len(fn.TypeParams) > 0 || fn.AsmBacked {
		return nil, unsupported("not an ordinary function body")
	}
	if len(fn.Parameters) > 8 {
		return nil, unsupported("more than eight parameters")
	}
	g := &generator{fn: fn, tc: tc, functions: functions, slots: map[string]int64{}, types: map[string]scalar{}, spans: map[string]span{}, arrays: map[string]*arrayLocal{}, recordDecls: records, adtDecls: adts, layouts: map[string]*recordLayout{}, records: map[string]*recordLocal{}, recordParams: map[string]*recordParam{}, regs: map[string]int{}, spill: map[int]int64{}, line: fn.Token.Line}
	parkSpans := mentionsCall(fn.Body)
	if hasVariables(fn) || parkSpans {
		g.saveArea = 8 * (calleeHigh - calleeLow + 1)
	}
	for r := scratchHigh; r >= scratchLow; r-- {
		g.free = append(g.free, r)
	}
	for r := vecScratchHigh; r >= vecScratchLow; r-- {
		g.freeF = append(g.freeF, vecBase+r)
	}
	if mentionsFloat(fn) || g.recordsMentionFloat(fn) {
		g.saveAreaV = 8 * (vecCalleeHigh - vecCalleeLow + 1)
	}
	// Parameters take AAPCS64's integer registers in order: a scalar one, a
	// span or view two (base, then the 32-bit length).
	nextReg := 0
	for _, p := range fn.Parameters {
		if p.Variadic {
			return nil, unsupported("variadic parameter %s", p.Name.Value)
		}
		if _, ok := scalarOf(p.Type); ok {
			nextReg++
			continue
		}
		if name, isRecord := g.recordTypeName(p.Type); isRecord {
			layout, err := g.layoutOf(name)
			if err != nil {
				return nil, err
			}
			if layout.isHFA() {
				return nil, unsupported("parameter %s: %s is a homogeneous floating-point aggregate", p.Name.Value, name)
			}
			regs, indirect := 1, layout.size > 16
			if !indirect {
				regs = layout.chunks()
			}
			g.recordParams[p.Name.Value] = &recordParam{layout: layout, reg: nextReg, regs: regs, indirect: indirect}
			nextReg += regs
			continue
		}
		if sp, ok := g.spanTypeOf(p.Type); ok {
			sp.argBase, sp.argLen = nextReg, nextReg+1
			sp.baseReg, sp.lenReg = sp.argBase, sp.argLen
			nextReg += 2
			if parkSpans {
				// Two callee-saved registers, from the pool variables use.
				if g.usedCallee+2 > calleeHigh-calleeLow+1 {
					return nil, unsupported("the span parameters and locals exhaust the callee-saved registers")
				}
				sp.baseReg, sp.lenReg = calleeLow+g.usedCallee, calleeLow+g.usedCallee+1
				g.usedCallee += 2
			}
			g.spans[p.Name.Value] = sp
			continue
		}
		return nil, unsupported("parameter %s of type %s", p.Name.Value, p.Type.String())
	}
	if nextReg > 8 {
		return nil, unsupported("the parameters exhaust the eight argument registers")
	}
	g.hasCalls = mentionsCall(fn.Body)
	if fn.ReturnType != nil {
		if fn.ReturnType.String() != "()" {
			if name, isRecord := g.recordTypeName(fn.ReturnType); isRecord {
				layout, err := g.layoutOf(name)
				if err != nil {
					return nil, err
				}
				if layout.isHFA() {
					return nil, unsupported("result of type %s (a homogeneous floating-point aggregate)", name)
				}
				g.resultRecord = layout
				g.resultIndirect = layout.size > 16
				g.resultAreaReg = 8
				if g.resultIndirect && g.hasCalls {
					// A call clobbers x8: park the result area's address.
					if g.usedCallee+1 > calleeHigh-calleeLow+1 {
						return nil, unsupported("the parameters and locals exhaust the callee-saved registers")
					}
					g.resultAreaReg = calleeLow + g.usedCallee
					g.usedCallee++
				}
			} else {
				s, ok := scalarOf(fn.ReturnType)
				if !ok {
					return nil, unsupported("result of type %s", fn.ReturnType.String())
				}
				g.result = &s
			}
		}
	}
	// Scalar parameters occupy the first slots, in order.
	g.pushScope()
	for _, p := range fn.Parameters {
		if s, ok := scalarOf(p.Type); ok {
			g.declare(p.Name.Value, s)
		}
		if rp, isRecord := g.recordParams[p.Name.Value]; isRecord {
			rp.local = g.declareRecord(p.Name.Value, rp.layout)
		}
	}
	g.head = g.newLabel("head")
	body, err := g.lowerBody(fn.Body)
	if err != nil {
		return nil, err
	}
	// The frame: [x29, x30] when the body calls, then the slots, rounded to
	// 16 bytes; sp moves once at entry and once before ret.
	frame := g.frameSize()
	if frame > 4080 {
		return nil, unsupported("a frame of %d bytes", frame)
	}
	out := &asm.Function{Name: fn.Name.Value, Signature: fn, Line: fn.Token.Line, Fallback: true}
	g.line = fn.Token.Line
	var prologue []asm.Item
	if frame > 0 {
		out.Frame = frame
		prologue = append(prologue, g.ins("sub", sp(), sp(), imm(frame)))
	}
	if g.hasCalls {
		prologue = append(prologue, g.ins("stp", xr(29), xr(30), mem(0)))
	}
	// Save the callee-saved registers the variables occupy, in pairs.
	for i := 0; i < g.usedCallee; i += 2 {
		offset := g.saveBase() + int64(8*i)
		if i+1 < g.usedCallee {
			prologue = append(prologue, g.ins("stp", xr(calleeLow+i), xr(calleeLow+i+1), mem(offset)))
		} else {
			prologue = append(prologue, g.ins("str", xr(calleeLow+i), mem(offset)))
		}
	}
	for i := 0; i < g.usedCalleeV; i += 2 {
		offset := g.saveBaseV() + int64(8*i)
		if i+1 < g.usedCalleeV {
			prologue = append(prologue, g.ins("stp", dr(vecCalleeLow+i), dr(vecCalleeLow+i+1), mem(offset)))
		} else {
			prologue = append(prologue, g.ins("str", dr(vecCalleeLow+i), mem(offset)))
		}
	}
	// Bind and store the parameters (narrow ones normalized: the caller's
	// upper bits are unspecified under AAPCS64); a span's pair stays bound.
	// Floating-point parameters take v0–v7 by their own count.
	regIndex, vecIndex := 0, 0
	if g.resultIndirect && g.resultAreaReg != 8 {
		prologue = append(prologue, g.ins("mov", xr(g.resultAreaReg), xr(8)))
	}
	for _, p := range fn.Parameters {
		if rp, isRecord := g.recordParams[p.Name.Value]; isRecord {
			binding := asm.Binding{Register: xr(rp.reg), Param: p.Name.Value, Line: fn.Token.Line}
			if rp.regs == 2 {
				second := xr(rp.reg + 1)
				binding.Length = &second
			}
			out.Bindings = append(out.Bindings, binding)
			if rp.indirect {
				// The caller's copy, addressed by the register: copy it into
				// the frame (the body may write its own copy).
				prologue = append(prologue, g.copyIn(rp.local, rp.reg)...)
			} else {
				for i := 0; i < rp.regs; i++ {
					prologue = append(prologue, g.ins("str", xr(rp.reg+i), g.slotMem(rp.local.offset+int64(8*i))))
				}
			}
			regIndex += rp.regs
			continue
		}
		if sp, isSpan := g.spans[p.Name.Value]; isSpan {
			length := wr(sp.argLen)
			out.Bindings = append(out.Bindings, asm.Binding{Register: xr(sp.argBase), Length: &length, Param: p.Name.Value, Line: fn.Token.Line})
			if sp.baseReg != sp.argBase {
				// Park the pair in its callee-saved registers (saved above).
				prologue = append(prologue, g.ins("mov", xr(sp.baseReg), xr(sp.argBase)), g.ins("mov", wr(sp.lenReg), wr(sp.argLen)))
			}
			regIndex += 2
			continue
		}
		s, _ := scalarOf(p.Type)
		if s.isFloat {
			i := vecIndex
			vecIndex++
			out.Bindings = append(out.Bindings, asm.Binding{Register: vr(i, s), Param: p.Name.Value, Line: fn.Token.Line})
			prologue = append(prologue, g.storeVar(p.Name.Value, vecBase+i))
			continue
		}
		i := regIndex
		regIndex++
		bound := wr(i)
		if s.wide() {
			bound = xr(i)
		}
		out.Bindings = append(out.Bindings, asm.Binding{Register: bound, Param: p.Name.Value, Line: fn.Token.Line})
		prologue = append(prologue, g.normalizeInto(i, s)...)
		prologue = append(prologue, g.storeVar(p.Name.Value, i))
	}
	// The loop header a tail self-call re-enters: after the parameters are
	// in their slots.
	prologue = append(prologue, asm.Label{Name: g.head, Line: fn.Token.Line})
	out.Items = append(prologue, body...)
	// Clobbers: the scratch registers, the argument registers a call
	// writes beyond the bound parameters, and the link register.
	for r := scratchLow; r <= scratchHigh; r++ {
		out.Clobbers = append(out.Clobbers, xr(r))
	}
	for i := 0; i < g.usedCallee; i++ {
		out.Clobbers = append(out.Clobbers, xr(calleeLow+i))
	}
	if g.usedFloat {
		for r := vecScratchLow; r <= vecScratchHigh; r++ {
			out.Clobbers = append(out.Clobbers, dr(r))
		}
		for i := 0; i < g.usedCalleeV; i++ {
			out.Clobbers = append(out.Clobbers, dr(vecCalleeLow+i))
		}
		if g.hasCalls {
			for r := vecIndex; r <= 7; r++ {
				if !(g.result != nil && g.result.isFloat && r == 0) {
					out.Clobbers = append(out.Clobbers, dr(r))
				}
			}
		}
	}
	if g.hasCalls {
		for r := regIndex; r <= 7; r++ {
			if !(g.result != nil && r == 0) {
				out.Clobbers = append(out.Clobbers, xr(r))
			}
		}
		out.Clobbers = append(out.Clobbers, xr(29), xr(30)) // saved by the prologue's stp, restored by ldp
	}
	if g.usedX8 {
		out.Clobbers = append(out.Clobbers, xr(8))
	}
	// The record types at this function's boundary, for the checker's
	// composite binding rules.
	for _, p := range fn.Parameters {
		if rp, isRecord := g.recordParams[p.Name.Value]; isRecord {
			if out.Composites == nil {
				out.Composites = map[string]asm.Composite{}
			}
			out.Composites[rp.layout.name] = asm.Composite{Size: rp.layout.size}
		}
	}
	if g.resultRecord != nil {
		if out.Composites == nil {
			out.Composites = map[string]asm.Composite{}
		}
		out.Composites[g.resultRecord.name] = asm.Composite{Size: g.resultRecord.size}
	}
	for _, p := range fn.Parameters {
		if sp, isSpan := g.spans[p.Name.Value]; isSpan && sp.elemLayout != nil {
			// A span of records: the checker sizes its elements from the table.
			if out.Composites == nil {
				out.Composites = map[string]asm.Composite{}
			}
			out.Composites[sp.elemLayout.name] = asm.Composite{Size: sp.elemLayout.size}
		}
	}
	return out, nil
}

// copyIn copies a record from the memory a register addresses into a
// record local: whole words, then a 4/2/1-byte tail, through x9.
func (g *generator) copyIn(dst *recordLocal, base int) []asm.Item {
	var items []asm.Item
	size := dst.layout.size
	off := int64(0)
	for ; off+8 <= size; off += 8 {
		items = append(items, g.ins("ldr", xr(scratchLow), asm.Memory{Base: xr(base), Offset: off}), g.ins("str", xr(scratchLow), g.slotMem(dst.offset+off)))
	}
	for _, piece := range []struct {
		bytes       int64
		load, store string
	}{{4, "ldr", "str"}, {2, "ldrh", "strh"}, {1, "ldrb", "strb"}} {
		if off+piece.bytes <= size {
			items = append(items, g.ins(piece.load, wr(scratchLow), asm.Memory{Base: xr(base), Offset: off}), g.ins(piece.store, wr(scratchLow), g.slotMem(dst.offset+off)))
			off += piece.bytes
		}
	}
	return items
}

// copyOut copies a record local into the memory a register addresses (the
// caller's result area), the same way.
func (g *generator) copyOut(base int, src *recordLocal) error {
	tmp, err := g.alloc(scalars["u64"])
	if err != nil {
		return err
	}
	size := src.layout.size
	unit := copyUnit(g.alignmentOf(src.loc()))
	off := int64(0)
	for bytes := unit; bytes >= 1; bytes /= 2 {
		for off+bytes <= size {
			load, store := accessPair(bytes)
			r := wr(tmp)
			if bytes == 8 {
				r = xr(tmp)
			}
			g.emit(load, r, g.memOf(src.loc().plus(off)))
			g.emit(store, r, asm.Memory{Base: xr(base), Offset: off})
			off += bytes
		}
	}
	g.release(tmp)
	return nil
}

// tempRecord declares an anonymous record local (a literal or call result
// in value position, a copy handed to a callee).
func (g *generator) tempRecord(layout *recordLayout) *recordLocal {
	g.temps++
	return g.declareRecord(fmt.Sprintf("$rec%d", g.temps), layout)
}

// recordValue lowers a record-typed expression to a record local: a
// named local or parameter, a typed literal (into a fresh temp), or a call
// returning a record.
func (g *generator) recordValue(expr ast.Expression) (*recordLocal, error) {
	return g.recordValueAs(expr, nil)
}

// recordValueAs is recordValue with the expected type (a variant literal
// without a written type takes it).
func (g *generator) recordValueAs(expr ast.Expression, expected *recordLayout) (*recordLocal, error) {
	switch e := expr.(type) {
	case *ast.VariantExpression:
		name, err := g.variantTypeName(e, expected)
		if err != nil {
			return nil, err
		}
		layout, err := g.layoutOf(name)
		if err != nil {
			return nil, err
		}
		return g.buildVariant(layout, e)
	case *ast.MatchExpression:
		// A record-valued match: every arm lands in one temp.
		layout := expected
		if layout == nil {
			var err error
			if layout, err = g.recordLayoutOfExpr(e.Arms[0].Body); err != nil {
				return nil, err
			}
		}
		out := g.tempRecord(layout)
		err := g.lowerMatch(e, func(body ast.Expression) error {
			src, err := g.recordValueAs(body, layout)
			if err != nil {
				return err
			}
			if src.layout != layout {
				return unsupported("a %s arm where %s is expected", src.layout.name, layout.name)
			}
			err = g.copyBytes(out.loc(), src.loc(), layout.size)
			g.releaseTemps(src.temps)
			return err
		})
		if err != nil {
			return nil, err
		}
		return out, nil
	case *ast.Identifier, *ast.IndexExpression:
		p, err := g.placeOf(e)
		if err != nil {
			return nil, err
		}
		if p.rec == nil {
			return nil, unsupported("%s is not a record", expr.String())
		}
		return p.rec, nil
	case *ast.RecordLiteral:
		if e.TypeName == nil {
			return nil, unsupported("an untyped record literal")
		}
		layout, err := g.layoutOf(e.TypeName.Value)
		if err != nil {
			return nil, err
		}
		return g.fillRecord(layout, e, "")
	case *ast.InvocationExpression:
		return g.callRecord(e)
	}
	return nil, unsupported("a record value %s", expr.String())
}

// buildVariant constructs `.Variant(payload)` in a fresh temp: the tag as a
// 32-bit store, the payload at its field.
func (g *generator) buildVariant(layout *recordLayout, e *ast.VariantExpression) (*recordLocal, error) {
	if !layout.isADT() {
		return nil, unsupported("the variant %s of the record %s", e.Variant.Value, layout.name)
	}
	info, known := layout.variants[e.Variant.Value]
	if !known {
		return nil, unsupported("the variant %s of %s", e.Variant.Value, layout.name)
	}
	if (e.Payload == nil) != (info.payload == "") {
		return nil, unsupported("the variant %s.%s with the wrong payload shape", layout.name, e.Variant.Value)
	}
	// The payload evaluates first (it may call), then the temp is filled.
	var payloadReg = -1
	var payloadSrc *recordLocal
	var field recordField
	if e.Payload != nil {
		field = layout.fields[info.payload]
		switch field.kind {
		case fieldScalar:
			typ := field.typ
			r, err := g.expr(e.Payload, &typ)
			if err != nil {
				return nil, err
			}
			payloadReg = r
		case fieldRecord:
			src, err := g.recordValueAs(e.Payload, field.layout)
			if err != nil {
				return nil, err
			}
			if src.layout != field.layout {
				return nil, unsupported("a %s payload where %s is expected", src.layout.name, field.layout.name)
			}
			payloadSrc = src
		default:
			return nil, unsupported("an array payload for %s.%s", layout.name, e.Variant.Value)
		}
	}
	rec := g.tempRecord(layout)
	tag, err := g.alloc(scalars["u32"])
	if err != nil {
		return nil, err
	}
	g.constant(tag, uint64(info.tag), scalars["u32"])
	g.emit("str", wr(tag), g.slotMem(rec.offset))
	g.release(tag)
	switch {
	case payloadReg >= 0:
		g.fieldStore(&scalarPlace{offset: rec.offset + field.offset, typ: field.typ}, payloadReg)
		g.release(payloadReg)
	case payloadSrc != nil:
		if err := g.copyBytes(slotLoc(rec.offset+field.offset), payloadSrc.loc(), field.size); err != nil {
			return nil, err
		}
		g.releaseTemps(payloadSrc.temps)
	}
	return rec, nil
}

// lowerMatch lowers a general match: over a tagged union (the tag loaded
// once and compared per arm, a payload binding declared as a local from the
// payload field — a record payload copied, as the C backend binds a copy),
// or over a scalar with literal patterns. arm lowers one arm's body in the
// caller's position (statement, value, or result). A wildcard or bare
// binding ends the chain; without one, falling off every arm reaches the
// trap block (the checker proved exhaustiveness, so it never runs).
func (g *generator) lowerMatch(match *ast.MatchExpression, arm func(body ast.Expression) error) error {
	end := g.newLabel("match_end")
	if layout, err := g.recordLayoutOfExpr(match.Scrutinee); err == nil {
		if !layout.isADT() {
			return unsupported("a match over the record %s", layout.name)
		}
		rec, err := g.recordValueAs(match.Scrutinee, layout)
		if err != nil {
			return err
		}
		tag, err := g.alloc(scalars["u32"])
		if err != nil {
			return err
		}
		g.emit("ldr", wr(tag), g.memOf(rec.loc()))
		closed := false
		for _, matchArm := range match.Arms {
			next := g.newLabel("arm")
			g.pushScope()
			if isWildcard(matchArm.Pattern) {
				closed = true
			}
			switch pattern := matchArm.Pattern.(type) {
			case *ast.VariantPattern:
				info, known := layout.variants[pattern.Variant.Value]
				if !known {
					g.popScope()
					return unsupported("the variant %s of %s in a pattern", pattern.Variant.Value, layout.name)
				}
				g.emit("cmp", wr(tag), imm(info.tag))
				g.branch("ne", next)
				if binding, isBinding := pattern.Payload.(*ast.BindingPattern); isBinding && binding.Name != nil && !isWildcard(pattern.Payload) {
					if info.payload == "" {
						g.popScope()
						return unsupported("a binding on the bare variant %s", pattern.Variant.Value)
					}
					if err := g.bindPayload(binding.Name.Value, rec, layout.fields[info.payload]); err != nil {
						g.popScope()
						return err
					}
				} else if pattern.Payload != nil && !isWildcard(pattern.Payload) {
					g.popScope()
					return unsupported("the payload pattern %s", pattern.Payload.String())
				}
			case *ast.WildcardPattern:
			case *ast.BindingPattern:
				if !closed {
					if err := g.bindWhole(pattern.Name.Value, rec); err != nil {
						g.popScope()
						return err
					}
					closed = true
				}
			default:
				g.popScope()
				return unsupported("the pattern %s over %s", matchArm.Pattern.String(), layout.name)
			}
			err := arm(matchArm.Body)
			g.popScope()
			if err != nil {
				return err
			}
			g.emit("b", asm.Symbol{Name: end})
			if closed {
				break
			}
			g.label(next)
		}
		if !closed {
			g.usedTrap = true
			g.emit("b", asm.Symbol{Name: g.trap})
		}
		g.label(end)
		g.release(tag)
		g.releaseTemps(rec.temps)
		return nil
	}
	// A scalar scrutinee with literal patterns.
	typ, err := g.typeOf(match.Scrutinee, nil)
	if err != nil {
		return err
	}
	value, err := g.expr(match.Scrutinee, &typ)
	if err != nil {
		return err
	}
	closed := false
	for _, matchArm := range match.Arms {
		next := g.newLabel("arm")
		switch pattern := matchArm.Pattern.(type) {
		case *ast.LiteralPattern:
			lit, err := g.expr(pattern.Value, &typ)
			if err != nil {
				return err
			}
			g.emit("cmp", reg(value, typ), reg(lit, typ))
			g.release(lit)
			g.branch("ne", next)
		default:
			if !isWildcard(matchArm.Pattern) {
				return unsupported("the pattern %s over %s", matchArm.Pattern.String(), typ.name)
			}
			closed = true
		}
		g.pushScope()
		err := arm(matchArm.Body)
		g.popScope()
		if err != nil {
			return err
		}
		g.emit("b", asm.Symbol{Name: end})
		if closed {
			break
		}
		g.label(next)
	}
	if !closed {
		g.usedTrap = true
		g.emit("b", asm.Symbol{Name: g.trap})
	}
	g.label(end)
	g.release(value)
	return nil
}

// isWildcard reports a pattern that matches anything without binding: `_`
// (spelled as a wildcard, or as a binding named "_").
func isWildcard(pattern ast.Pattern) bool {
	switch p := pattern.(type) {
	case *ast.WildcardPattern:
		return true
	case *ast.BindingPattern:
		return p.Name != nil && p.Name.Value == "_"
	}
	return false
}

// bindPayload declares a match arm's payload binding: a scalar loaded into
// a variable, a record copied into a fresh local.
func (g *generator) bindPayload(name string, rec *recordLocal, field recordField) error {
	switch field.kind {
	case fieldScalar:
		at := rec.loc().plus(field.offset)
		r, err := g.fieldLoad(&scalarPlace{offset: at.offset, typ: field.typ, inReg: at.inReg, reg: at.reg})
		if err != nil {
			return err
		}
		g.declare(name, field.typ)
		g.items = append(g.items, g.storeVar(name, r))
		g.release(r)
		return nil
	case fieldRecord:
		local := g.declareRecord(name, field.layout)
		return g.copyBytes(local.loc(), rec.loc().plus(field.offset), field.size)
	}
	return unsupported("a binding of an array payload")
}

// bindWhole binds a match arm's name to a copy of the whole value.
func (g *generator) bindWhole(name string, rec *recordLocal) error {
	local := g.declareRecord(name, rec.layout)
	return g.copyRecord(local, rec)
}

// fillRecord evaluates a literal's fields (in layout order, before the
// record is bound) into a new record local named name (a temp when empty).
func (g *generator) fillRecord(layout *recordLayout, literal *ast.RecordLiteral, name string) (*recordLocal, error) {
	if len(literal.Fields) != len(layout.order) {
		return nil, unsupported("a partial %s literal", layout.name)
	}
	// Phase one, before the name is bound: scalar values into registers,
	// record and array sources resolved to their places or literals.
	type pending struct {
		reg      int
		src      *recordLocal
		arraySrc *arrayLocal
		elements *ast.ArrayLiteral
	}
	var values []pending
	for _, fieldName := range layout.order {
		expr, given := literal.Fields[fieldName]
		if !given {
			return nil, unsupported("a %s literal without the field %s", layout.name, fieldName)
		}
		field := layout.fields[fieldName]
		switch field.kind {
		case fieldScalar:
			typ := field.typ
			r, err := g.expr(expr, &typ)
			if err != nil {
				return nil, err
			}
			values = append(values, pending{reg: r})
		case fieldRecord:
			src, err := g.recordValueAs(expr, field.layout)
			if err != nil {
				return nil, err
			}
			if src.layout != field.layout {
				return nil, unsupported("a %s where the field %s is a %s", src.layout.name, fieldName, field.layout.name)
			}
			values = append(values, pending{src: src})
		default:
			switch value := expr.(type) {
			case *ast.ArrayLiteral:
				if int64(len(value.Elements)) != field.length {
					return nil, unsupported("an array literal of %d elements for the field %s ([%d]%s)", len(value.Elements), fieldName, field.length, field.typ.name)
				}
				values = append(values, pending{elements: value})
			default:
				p, err := g.placeOf(expr)
				if err != nil {
					return nil, err
				}
				if p.arr == nil || p.arr.elem != field.typ || p.arr.elemLayout != field.layout || p.arr.length != field.length {
					return nil, unsupported("the array field %s initialized from %s", fieldName, expr.String())
				}
				values = append(values, pending{arraySrc: p.arr})
			}
		}
	}
	var rec *recordLocal
	if name == "" {
		rec = g.tempRecord(layout)
	} else {
		rec = g.declareRecord(name, layout)
	}
	for i, fieldName := range layout.order {
		field := layout.fields[fieldName]
		at := rec.offset + field.offset
		switch {
		case field.kind == fieldScalar:
			g.fieldStore(&scalarPlace{offset: at, typ: field.typ}, values[i].reg)
			g.release(values[i].reg)
		case values[i].src != nil:
			if err := g.copyBytes(slotLoc(at), values[i].src.loc(), field.size); err != nil {
				return nil, err
			}
			g.releaseTemps(values[i].src.temps)
		case values[i].arraySrc != nil:
			if err := g.copyBytes(slotLoc(at), values[i].arraySrc.loc(), field.size); err != nil {
				return nil, err
			}
			g.releaseTemps(values[i].arraySrc.temps)
		default:
			if field.layout != nil {
				// An array of records: each element copied in.
				for j, element := range values[i].elements.Elements {
					src, err := g.recordValueAs(element, field.layout)
					if err != nil {
						return nil, err
					}
					if src.layout != field.layout {
						return nil, unsupported("a %s element in the field %s", src.layout.name, fieldName)
					}
					if err := g.copyBytes(slotLoc(at+int64(j)*field.layout.size), src.loc(), field.layout.size); err != nil {
						return nil, err
					}
					g.releaseTemps(src.temps)
				}
				continue
			}
			elemSize := int64(field.typ.bits / 8)
			for j, element := range values[i].elements.Elements {
				typ := field.typ
				r, err := g.expr(element, &typ)
				if err != nil {
					return nil, err
				}
				g.emit(storeOf(typ), reg(r, typ), g.slotMem(at+int64(j)*elemSize))
				g.release(r)
			}
		}
	}
	return rec, nil
}

// callRecord lowers a call returning a record into a fresh temp: up to 16
// bytes arrive as chunks in x0/x1, larger ones are written by the callee
// into the temp through x8.
func (g *generator) callRecord(e *ast.InvocationExpression) (*recordLocal, error) {
	ident, isIdent := e.Function.(*ast.Identifier)
	if !isIdent {
		return nil, unsupported("a call through a value")
	}
	callee, known := g.functions[ident.Value]
	if !known || callee.ReturnType == nil {
		return nil, unsupported("a call to %s", ident.Value)
	}
	name, isRecord := g.recordTypeName(callee.ReturnType)
	if !isRecord {
		return nil, unsupported("a call to %s in record position", ident.Value)
	}
	layout, err := g.layoutOf(name)
	if err != nil {
		return nil, err
	}
	if layout.isHFA() {
		return nil, unsupported("a call to %s returning a homogeneous floating-point aggregate", ident.Value)
	}
	dst := g.tempRecord(layout)
	if _, err := g.callWith(e, dst); err != nil {
		return nil, err
	}
	return dst, nil
}

// resultRecordExpr places a record-typed result: chunks in x0/x1, or a
// copy into the caller's result area.
func (g *generator) resultRecordExpr(expr ast.Expression) error {
	switch e := expr.(type) {
	case *ast.MatchExpression:
		if _, _, isBool := boolConditional(e); !isBool {
			return g.lowerMatch(e, g.resultRecordExpr)
		}
		if whenTrue, whenFalse, ok := boolConditional(e); ok {
			elseLabel, end := g.newLabel("else"), g.newLabel("endif")
			if err := g.condition(e.Scrutinee, elseLabel); err != nil {
				return err
			}
			if err := g.resultRecordExpr(whenTrue); err != nil {
				return err
			}
			g.emit("b", asm.Symbol{Name: end})
			g.label(elseLabel)
			if err := g.resultRecordExpr(whenFalse); err != nil {
				return err
			}
			g.label(end)
			return nil
		}
	case *ast.BlockExpression:
		if e.Block != nil && len(e.Block.Statements) > 0 {
			g.pushScope()
			defer g.popScope()
			stmts := e.Block.Statements
			if err := g.lowerStatements(stmts[:len(stmts)-1], false, ""); err != nil {
				return err
			}
			if es, ok := stmts[len(stmts)-1].(*ast.ExpressionStatement); ok && !es.Discard {
				return g.resultRecordExpr(es.Expression)
			}
			return unsupported("a block whose last statement is not its record result")
		}
	}
	rec, err := g.recordValueAs(expr, g.resultRecord)
	if err != nil {
		return err
	}
	if rec.layout != g.resultRecord {
		return unsupported("a %s result where %s is declared", rec.layout.name, g.resultRecord.name)
	}
	if g.resultIndirect {
		err := g.copyOut(g.resultAreaReg, rec)
		g.releaseTemps(rec.temps)
		return err
	}
	if rec.inReg || g.slotMem(rec.offset).Offset%8 != 0 {
		aligned := g.tempRecord(g.resultRecord)
		if err := g.copyRecord(aligned, rec); err != nil {
			return err
		}
		g.releaseTemps(rec.temps)
		rec = aligned
	}
	for i := 0; i < g.resultRecord.chunks(); i++ {
		g.emit("ldr", xr(i), g.slotMem(rec.offset+int64(8*i)))
	}
	return nil
}

// frameSize is the frame in bytes: the [x29, x30] pair when the body
// calls, the slots, rounded up to 16.
func (g *generator) frameSize() int64 {
	return (g.saveBase() + g.saveArea + g.saveAreaV + 8*g.nslots + 15) / 16 * 16
}

// saveBaseV is the frame offset of the d8–d15 save area: past the
// general callee-saved area.
func (g *generator) saveBaseV() int64 { return g.saveBase() + g.saveArea }

// saveBase is the frame offset of the callee-saved save area: past the
// [x29, x30] pair when the body calls.
func (g *generator) saveBase() int64 {
	if g.hasCalls {
		return 16
	}
	return 0
}

// hasVariables reports scalar parameters or local declarations: what the
// callee-saved registers are reserved for.
func hasVariables(fn *ast.FunctionStatement) bool {
	for _, p := range fn.Parameters {
		if _, ok := scalarOf(p.Type); ok {
			return true
		}
	}
	found := false
	walk(fn.Body, func(n ast.Node) {
		switch e := n.(type) {
		case *ast.VariableDeclaration:
			found = true
		case *ast.MatchExpression:
			// A payload binding in a match arm is a variable too.
			for _, arm := range e.Arms {
				if pattern, isVariant := arm.Pattern.(*ast.VariantPattern); isVariant && pattern.Payload != nil {
					if _, isBinding := pattern.Payload.(*ast.BindingPattern); isBinding {
						found = true
					}
				}
			}
		}
	})
	return found
}

// storeVar moves a value held in register r into a variable's home.
func (g *generator) storeVar(name string, r int) asm.Instruction {
	typ := g.types[name]
	if v, inReg := g.regs[name]; inReg && v >= 0 {
		return g.ins(moveOf(typ), reg(v, typ), reg(r, typ))
	}
	return g.ins("str", reg(r, typ), g.slotMem(g.slots[name]))
}

// loadVar brings a variable's value into register r.
func (g *generator) loadVar(name string, r int) asm.Instruction {
	typ := g.types[name]
	if v, inReg := g.regs[name]; inReg && v >= 0 {
		return g.ins(moveOf(typ), reg(r, typ), reg(v, typ))
	}
	return g.ins("ldr", reg(r, typ), g.slotMem(g.slots[name]))
}

// moveOf is the register move of a type's file.
func moveOf(s scalar) string {
	if s.isFloat {
		return "fmov"
	}
	return "mov"
}

// ---- items ------------------------------------------------------------

func xr(n int) asm.Register {
	if n == 31 {
		return asm.Register{Text: "xzr", Class: asm.ClassX, Num: 31, Lane: -1}
	}
	return asm.Register{Text: "x" + strconv.Itoa(n), Class: asm.ClassX, Num: n, Lane: -1}
}

func wr(n int) asm.Register {
	if n == 31 {
		return asm.Register{Text: "wzr", Class: asm.ClassW, Num: 31, Lane: -1}
	}
	return asm.Register{Text: "w" + strconv.Itoa(n), Class: asm.ClassW, Num: n, Lane: -1}
}

func sp() asm.Register { return asm.Register{Text: "sp", Class: asm.ClassSP, Num: -1, Lane: -1} }

func imm(v int64) asm.Immediate { return asm.Immediate{Value: v} }

func mem(offset int64) asm.Memory { return asm.Memory{Base: sp(), Offset: offset} }

func (g *generator) ins(mnemonic string, operands ...asm.Operand) asm.Instruction {
	return asm.Instruction{Mnemonic: mnemonic, Operands: operands, Line: g.line}
}

func (g *generator) emit(mnemonic string, operands ...asm.Operand) {
	if g.terminated {
		return
	}
	g.items = append(g.items, g.ins(mnemonic, operands...))
	if mnemonic == "b" || mnemonic == "ret" || mnemonic == "brk" {
		g.terminated = true
	}
}

func (g *generator) branch(cond, label string) {
	if g.terminated {
		return
	}
	g.items = append(g.items, asm.Instruction{Mnemonic: "b.", Cond: cond, Operands: []asm.Operand{asm.Symbol{Name: label}}, Line: g.line})
}

func (g *generator) label(name string) {
	g.items = append(g.items, asm.Label{Name: name, Line: g.line})
	g.terminated = false
}

func (g *generator) newLabel(hint string) string {
	g.labels++
	return fmt.Sprintf("%s_%d", hint, g.labels)
}

// reg spells scratch register r at the type's width.
func reg(r int, s scalar) asm.Register {
	if s.isFloat {
		return vr(r-vecBase, s)
	}
	if s.wide() {
		return xr(r)
	}
	return wr(r)
}

// vecBase offsets the vector register file in the generator's register
// numbering: register vecBase+n is vN (its s or d view by the type).
const vecBase = 100

// vr spells vector register n in the type's scalar view.
func vr(n int, s scalar) asm.Register {
	view := "s"
	if s.wide() {
		view = "d"
	}
	return asm.Register{Text: view + strconv.Itoa(n), Class: asm.ClassV, Num: n, Vec: view, Lane: -1}
}

// dr spells vector register n's d view (the callee-saved width, spills).
func dr(n int) asm.Register {
	return asm.Register{Text: "d" + strconv.Itoa(n), Class: asm.ClassV, Num: n, Vec: "d", Lane: -1}
}

// ---- scratch registers and slots --------------------------------------

func (g *generator) alloc(typ scalar) (int, error) {
	pool := &g.free
	if typ.isFloat {
		pool = &g.freeF
		g.usedFloat = true
	}
	if len(*pool) == 0 {
		return 0, unsupported("an expression deeper than the scratch registers")
	}
	r := (*pool)[len(*pool)-1]
	*pool = (*pool)[:len(*pool)-1]
	g.live = append(g.live, r)
	return r, nil
}

func (g *generator) release(r int) {
	for i, live := range g.live {
		if live == r {
			g.live = append(g.live[:i], g.live[i+1:]...)
			break
		}
	}
	if r >= vecBase {
		g.freeF = append(g.freeF, r)
		return
	}
	g.free = append(g.free, r)
}

func (g *generator) pushScope() { g.scopes = append(g.scopes, map[string]slotBinding{}) }

func (g *generator) popScope() {
	top := g.scopes[len(g.scopes)-1]
	g.scopes = g.scopes[:len(g.scopes)-1]
	for name := range top {
		delete(g.slots, name)
		delete(g.types, name)
		delete(g.regs, name)
		delete(g.arrays, name)
		delete(g.records, name)
		if top[name].sp != nil {
			delete(g.spans, name)
		}
		// A shadowed outer binding comes back into view.
		for i := len(g.scopes) - 1; i >= 0; i-- {
			if b, ok := g.scopes[i][name]; ok {
				if b.arr != nil {
					g.arrays[name] = b.arr
				} else if b.rec != nil {
					g.records[name] = b.rec
				} else if b.sp != nil {
					g.spans[name] = *b.sp
				} else {
					g.slots[name], g.types[name], g.regs[name] = b.offset, b.typ, b.reg
				}
				break
			}
		}
	}
}

// declareArray gives an owned array local its frame storage: whole 8-byte
// slots, so every element access stays aligned and spills never overlap.
func (g *generator) declareArray(name string, elem scalar, length int64) *arrayLocal {
	arr := g.allocArray(elem, length)
	g.bindArray(name, arr)
	return arr
}

// allocArray reserves an array's frame storage without binding a name.
func (g *generator) allocArray(elem scalar, length int64) *arrayLocal {
	bytes := length * int64(elem.bits/8)
	arr := &arrayLocal{offset: 8 * g.nslots, elem: elem, length: length}
	g.nslots += (bytes + 7) / 8
	return arr
}

// bindArray brings an array's storage into scope under a name.
func (g *generator) bindArray(name string, arr *arrayLocal) {
	delete(g.slots, name)
	delete(g.types, name)
	delete(g.regs, name)
	g.arrays[name] = arr
	g.scopes[len(g.scopes)-1][name] = slotBinding{reg: -1, arr: arr}
}

// lowerArrayDeclaration lowers `buf: [N]T` (zero-filled, as the C backend
// leaves no storage uninitialized) or `buf: [N]T = [e0, …]` (each element
// stored at its slot).
func (g *generator) lowerArrayDeclaration(s *ast.VariableDeclaration, elem scalar, length int64) error {
	if elem.isFloat {
		g.usedFloat = true
	}
	if s.Value == nil {
		arr := g.declareArray(s.Name.Value, elem, length)
		zero, err := g.alloc(scalars["u64"])
		if err != nil {
			return err
		}
		g.emit("mov", xr(zero), imm(0))
		bytes := length * int64(elem.bits/8)
		words := (bytes + 7) / 8
		for w := int64(0); w < words; w += 2 {
			if w+1 < words {
				g.emit("stp", xr(zero), xr(zero), g.slotMem(arr.offset+8*w))
			} else {
				g.emit("str", xr(zero), g.slotMem(arr.offset+8*w))
			}
		}
		g.release(zero)
		return nil
	}
	literal, isLiteral := s.Value.(*ast.ArrayLiteral)
	if !isLiteral {
		return unsupported("an array local initialized from %s", s.Value.String())
	}
	if int64(len(literal.Elements)) != length {
		return unsupported("an array literal of %d elements for [%d]%s", len(literal.Elements), length, elem.name)
	}
	// The elements evaluate one at a time into storage reserved before the
	// name is bound (an initializer never sees the array it fills).
	arr := g.allocArray(elem, length)
	for i, element := range literal.Elements {
		r, err := g.expr(element, &elem)
		if err != nil {
			return err
		}
		g.emit(storeOf(elem), reg(r, elem), g.slotMem(arr.offset+int64(i)*int64(elem.bits/8)))
		g.release(r)
	}
	g.bindArray(s.Name.Value, arr)
	return nil
}

// declareRecord gives an owned record local its frame storage in whole
// 8-byte slots.
func (g *generator) declareRecord(name string, layout *recordLayout) *recordLocal {
	rec := &recordLocal{offset: 8 * g.nslots, layout: layout}
	g.nslots += (layout.size + 7) / 8
	delete(g.slots, name)
	delete(g.types, name)
	delete(g.regs, name)
	g.records[name] = rec
	g.scopes[len(g.scopes)-1][name] = slotBinding{reg: -1, rec: rec}
	return rec
}

// lowerSpanDeclaration lowers `w: []T = subslice(v, s, n)` / `w: [*]T = …`
// / `w: []T = v`: the local span takes a callee-saved register pair (so it
// survives calls and the checker's fact stays on it) and joins the spans
// the element paths know.
func (g *generator) lowerSpanDeclaration(s *ast.VariableDeclaration, target span) error {
	if s.Value == nil {
		return unsupported("the span local %s without an initializer", s.Name.Value)
	}
	if g.usedCallee+2 > calleeHigh-calleeLow+1 {
		return unsupported("the span local %s: the callee-saved registers are exhausted", s.Name.Value)
	}
	baseReg, lenReg := calleeLow+g.usedCallee, calleeLow+g.usedCallee+1
	g.usedCallee += 2
	value, owned, err := g.spanValue(s.Value, &target, baseReg, lenReg)
	if err != nil {
		return err
	}
	if owned {
		// Another named span's pair: copy it.
		g.emit("mov", xr(baseReg), xr(value.baseReg))
		g.emit("mov", wr(lenReg), wr(value.lenReg))
	}
	local := span{elem: target.elem, elemLayout: target.elemLayout, writable: target.writable, baseReg: baseReg, lenReg: lenReg, argBase: -1, argLen: -1}
	delete(g.slots, s.Name.Value)
	delete(g.types, s.Name.Value)
	delete(g.regs, s.Name.Value)
	g.spans[s.Name.Value] = local
	g.scopes[len(g.scopes)-1][s.Name.Value] = slotBinding{reg: -1, sp: &local}
	return nil
}

// spanValue lowers a span-typed expression: a named span (a parameter or
// local; returned as is, owned=true: its registers are never released),
// `view(&buf)`/`span(&buf)` over an array place, or `subslice(v, start,
// n)` (owned=false). When baseReg/lenReg are given (>= 0) a computed pair
// is produced there; otherwise in fresh scratch registers the caller
// releases. target, when non-nil, is the expected shape.
func (g *generator) spanValue(expr ast.Expression, target *span, baseReg, lenReg int) (span, bool, error) {
	if ident, isIdent := expr.(*ast.Identifier); isIdent {
		sp, isSpan := g.spans[ident.Value]
		if !isSpan {
			return span{}, false, unsupported("%s is not a span", ident.Value)
		}
		if target != nil && (!sameElements(sp, *target) || (target.writable && !sp.writable)) {
			return span{}, false, unsupported("%s does not fit the span type", ident.Value)
		}
		return sp, true, nil
	}
	call, isCall := expr.(*ast.InvocationExpression)
	if !isCall {
		return span{}, false, unsupported("a span value %s", expr.String())
	}
	fn, isIdent := call.Function.(*ast.Identifier)
	if !isIdent {
		return span{}, false, unsupported("a call through a value")
	}
	if baseReg < 0 {
		var err error
		if baseReg, err = g.alloc(scalars["u64"]); err != nil {
			return span{}, false, err
		}
		if lenReg, err = g.alloc(scalars["u32"]); err != nil {
			return span{}, false, err
		}
	}
	out := span{baseReg: baseReg, lenReg: lenReg, argBase: -1, argLen: -1}
	switch {
	case (fn.Value == "view" || fn.Value == "span") && len(call.Arguments) == 1:
		shape := span{writable: fn.Value == "span"}
		if target != nil {
			shape.elem = target.elem
			if target.writable && !shape.writable {
				return span{}, false, unsupported("a view where a span is expected")
			}
		}
		borrow, isBorrow := call.Arguments[0].(*ast.PrefixExpression)
		if !isBorrow || borrow.Operator != "&" {
			return span{}, false, unsupported("%s of %s (only &buf over an owned array)", fn.Value, call.Arguments[0].String())
		}
		arr := g.arrayOperand(borrow.Right)
		if arr == nil {
			return span{}, false, unsupported("%s of %s (only an owned array)", fn.Value, borrow.Right.String())
		}
		if target != nil && (arr.elem != target.elem || arr.elemLayout != target.elemLayout) {
			return span{}, false, unsupported("%s over %s where the span type's elements are expected", fn.Value, borrow.Right.String())
		}
		if arr.inReg {
			return span{}, false, unsupported("%s of an array inside a computed element", fn.Value)
		}
		out.elem, out.elemLayout, out.writable = arr.elem, arr.elemLayout, shape.writable
		g.emit("add", xr(baseReg), sp(), imm(g.slotMem(arr.offset).Offset))
		g.constant(lenReg, uint64(arr.length), scalars["u32"])
		return out, false, nil
	case fn.Value == "subslice" && len(call.Arguments) == 3:
		src, srcOwned, err := g.spanValue(call.Arguments[0], nil, -1, -1)
		if err != nil {
			return span{}, false, err
		}
		if target != nil && (!sameElements(src, *target) || (target.writable && !src.writable)) {
			return span{}, false, unsupported("subslice of %s does not fit the span type", call.Arguments[0].String())
		}
		if stride := src.stride(); stride&(stride-1) != 0 || stride > 16 {
			return span{}, false, unsupported("subslice over %d-byte elements (the derived-span idiom scales by a power of two up to 16)", stride)
		}
		u32 := scalars["u32"]
		for _, bound := range call.Arguments[1:] {
			typ, err := g.typeOf(bound, &u32)
			if err != nil {
				return span{}, false, err
			}
			if typ != u32 {
				return span{}, false, unsupported("a subslice bound of type %s (the native subset takes u32)", typ.name)
			}
		}
		start, err := g.expr(call.Arguments[1], &u32)
		if err != nil {
			return span{}, false, err
		}
		count, err := g.expr(call.Arguments[2], &u32)
		if err != nil {
			return span{}, false, err
		}
		rest, err := g.alloc(u32)
		if err != nil {
			return span{}, false, err
		}
		// The C helper's check: start > len || n > len - start traps.
		g.usedTrap = true
		g.emit("cmp", wr(start), wr(src.lenReg))
		g.branch("hi", g.trap)
		g.emit("sub", wr(rest), wr(src.lenReg), wr(start))
		g.emit("cmp", wr(count), wr(rest))
		g.branch("hi", g.trap)
		g.emit("add", xr(baseReg), xr(src.baseReg), asm.Extended{Reg: wr(start), Kind: "uxtw", Amount: int64(log2Bytes(int(src.stride())))})
		g.emit("mov", wr(lenReg), wr(count))
		g.release(rest)
		g.release(count)
		g.release(start)
		if !srcOwned {
			g.release(src.baseReg)
			g.release(src.lenReg)
		}
		out.elem, out.elemLayout, out.writable = src.elem, src.elemLayout, src.writable
		return out, false, nil
	}
	return span{}, false, unsupported("a span value %s", expr.String())
}

// lowerRecordDeclaration lowers `p: Point = Point { x: e, … }` (every field
// stored at its offset) or `p: Point = q` (a slot-wise copy). A record
// without an initializer is left to the C backend, which leaves it
// uninitialized — no semantics are invented here.
func (g *generator) lowerRecordDeclaration(s *ast.VariableDeclaration, typeName string) error {
	layout, err := g.layoutOf(typeName)
	if err != nil {
		return err
	}
	if s.Value == nil {
		return unsupported("the record local %s without an initializer", s.Name.Value)
	}
	if literal, isLiteral := s.Value.(*ast.RecordLiteral); isLiteral {
		if literal.TypeName != nil && literal.TypeName.Value != typeName {
			return unsupported("a %s literal for the %s local %s", literal.TypeName.Value, typeName, s.Name.Value)
		}
		_, err := g.fillRecord(layout, literal, s.Name.Value)
		return err
	}
	// A copy of another record value: a local, a parameter, a call's
	// result, a variant literal.
	src, err := g.recordValueAs(s.Value, layout)
	if err != nil {
		return err
	}
	if src.layout != layout {
		return unsupported("the %s local %s initialized from a %s", typeName, s.Name.Value, src.layout.name)
	}
	rec := g.declareRecord(s.Name.Value, layout)
	err = g.copyRecord(rec, src)
	g.releaseTemps(src.temps)
	return err
}

// copyRecord copies a record slot-wise (the padding travels too, as the C
// struct assignment copies it).
func (g *generator) copyRecord(dst, src *recordLocal) error {
	return g.copyBytes(dst.loc(), src.loc(), dst.layout.size)
}

// fieldLoad reads a scalar field into a fresh register at its type: a Bool
// field is the 4-byte C enum holding 0 or 1, so its load is a 32-bit `ldr`.
func (g *generator) fieldLoad(sc *scalarPlace) (int, error) {
	r, err := g.alloc(sc.typ)
	if err != nil {
		return 0, err
	}
	load := loadOf(sc.typ)
	if sc.typ.isBool {
		load = "ldr"
	}
	g.emit(load, reg(r, sc.typ), g.memOf(sc.loc()))
	return r, nil
}

// fieldStore writes a normalized value of the field's type.
func (g *generator) fieldStore(sc *scalarPlace, r int) {
	store := storeOf(sc.typ)
	if sc.typ.isBool {
		store = "str"
	}
	g.emit(store, reg(r, sc.typ), g.memOf(sc.loc()))
}

// fieldOperand resolves `p.f` (through any nesting) to a scalar field.
func (g *generator) fieldOperand(e *ast.IndexExpression) (*scalarPlace, error) {
	p, err := g.placeOf(e)
	if err != nil {
		return nil, err
	}
	if p.sc == nil {
		return nil, unsupported("%s is not a scalar field", e.String())
	}
	return p.sc, nil
}

// recordsMentionFloat reports a record local whose type has a float field:
// the vector file's save area is then reserved up front like any float use.
func (g *generator) recordsMentionFloat(fn *ast.FunctionStatement) bool {
	found := false
	walk(fn.Body, func(n ast.Node) {
		decl, isDecl := n.(*ast.VariableDeclaration)
		if !isDecl || decl.Type == nil {
			return
		}
		if name, isRecord := g.recordTypeName(decl.Type); isRecord {
			if layout, err := g.layoutOf(name); err == nil && layout.hasFloat {
				found = true
			}
			return
		}
		if g.isArrayType(decl.Type) {
			if _, elemLayout, _, err := g.arrayTypeOf(decl.Type); err == nil && elemLayout != nil && elemLayout.hasFloat {
				found = true
			}
		}
	})
	return found
}

// lowerRecordArrayDeclaration lowers `pool: [N]Rec` (zero-filled, as the C
// backend's `{0}`) or `pool: [N]Rec = [r0, …]` (each element copied in).
func (g *generator) lowerRecordArrayDeclaration(s *ast.VariableDeclaration, elemLayout *recordLayout, length int64) error {
	if elemLayout.hasFloat {
		g.usedFloat = true
	}
	arr := &arrayLocal{offset: 8 * g.nslots, elemLayout: elemLayout, length: length}
	g.nslots += (length*elemLayout.size + 7) / 8
	if s.Value == nil {
		zero, err := g.alloc(scalars["u64"])
		if err != nil {
			return err
		}
		g.emit("mov", xr(zero), imm(0))
		words := (length*elemLayout.size + 7) / 8
		for w := int64(0); w < words; w += 2 {
			if w+1 < words {
				g.emit("stp", xr(zero), xr(zero), g.slotMem(arr.offset+8*w))
			} else {
				g.emit("str", xr(zero), g.slotMem(arr.offset+8*w))
			}
		}
		g.release(zero)
		g.bindArray(s.Name.Value, arr)
		return nil
	}
	literal, isLiteral := s.Value.(*ast.ArrayLiteral)
	if !isLiteral {
		return unsupported("an array of records initialized from %s", s.Value.String())
	}
	if int64(len(literal.Elements)) != length {
		return unsupported("an array literal of %d elements for [%d]%s", len(literal.Elements), length, elemLayout.name)
	}
	for i, element := range literal.Elements {
		src, err := g.recordValueAs(element, elemLayout)
		if err != nil {
			return err
		}
		if src.layout != elemLayout {
			return unsupported("a %s element in [%d]%s", src.layout.name, length, elemLayout.name)
		}
		if err := g.copyBytes(slotLoc(arr.offset+int64(i)*elemLayout.size), src.loc(), elemLayout.size); err != nil {
			return err
		}
		g.releaseTemps(src.temps)
	}
	g.bindArray(s.Name.Value, arr)
	return nil
}

// storeOf is the whole-element store of a type.
func storeOf(s scalar) string {
	switch {
	case s.isFloat || s.bits >= 32:
		return "str"
	case s.bits == 16:
		return "strh"
	default:
		return "strb"
	}
}

// loadOf is the whole-element load of a type, zero- or sign-extending as the
// element type reads in C.
func loadOf(s scalar) string {
	switch {
	case s.isFloat || s.bits >= 32:
		return "ldr"
	case s.bits == 16 && s.signed:
		return "ldrsh"
	case s.bits == 16:
		return "ldrh"
	case s.signed:
		return "ldrsb"
	default:
		return "ldrb"
	}
}

// declare gives a variable a fresh slot in the current scope.
func (g *generator) declare(name string, s scalar) int64 {
	offset := int64(-1)
	r := -1
	if s.isFloat {
		g.usedFloat = true
		if g.usedCalleeV < vecCalleeHigh-vecCalleeLow+1 {
			r = vecBase + vecCalleeLow + g.usedCalleeV
			g.usedCalleeV++
		} else {
			offset = 8 * g.nslots
			g.nslots++
		}
	} else if g.usedCallee < calleeHigh-calleeLow+1 {
		r = calleeLow + g.usedCallee
		g.usedCallee++
	} else {
		offset = 8 * g.nslots
		g.nslots++
	}
	g.slots[name], g.types[name], g.regs[name] = offset, s, r
	g.scopes[len(g.scopes)-1][name] = slotBinding{offset: offset, typ: s, reg: r}
	return offset
}

// slotMem is the frame address of a slot: past the [x29, x30] pair and the
// callee-saved save area.
func (g *generator) slotMem(offset int64) asm.Memory {
	return mem(g.saveBase() + g.saveArea + g.saveAreaV + offset)
}

// ---- types --------------------------------------------------------------

// typeOf infers an expression's type in the subset; hint is the type the
// context expects (a literal takes it).
func (g *generator) typeOf(expr ast.Expression, hint *scalar) (scalar, error) {
	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		if hint != nil && !hint.isFloat {
			return *hint, nil
		}
		return scalars["i32"], nil
	case *ast.FloatLiteral:
		if hint != nil && hint.isFloat {
			return *hint, nil
		}
		if name, known := g.tc.ArithmeticType(e.Token); known && typechecker.IsFloatName(name) {
			return scalars[name], nil
		}
		return scalars["f64"], nil
	case *ast.Boolean:
		return scalars["Bool"], nil
	case *ast.Identifier:
		if s, ok := g.types[e.Value]; ok {
			return s, nil
		}
		return scalar{}, unsupported("identifier %s", e.Value)
	case *ast.InfixExpression:
		switch e.Operator {
		case "==", "!=", "<", "<=", ">", ">=", "&&", "||":
			return scalars["Bool"], nil
		case "<<", ">>":
			if width, known := g.tc.ShiftWidth(e.Token); known {
				return scalars["u"+strconv.Itoa(width)], nil
			}
			return g.typeOf(e.Left, hint)
		}
		if name, known := g.tc.ArithmeticType(e.Token); known {
			if s, ok := scalars[name]; ok {
				return s, nil
			}
			return scalar{}, unsupported("arithmetic on %s", name)
		}
		// A literal-only expression carries no record: the context types it.
		left, err := g.typeOf(e.Left, hint)
		if err == nil {
			return left, nil
		}
		return g.typeOf(e.Right, hint)
	case *ast.PrefixExpression:
		if e.Operator == "!" {
			return scalars["Bool"], nil
		}
		if name, known := g.tc.ArithmeticType(e.Token); known {
			if s, ok := scalars[name]; ok {
				return s, nil
			}
		}
		return g.typeOf(e.Right, hint)
	case *ast.IndexExpression:
		if e.Dot {
			base, err := g.recordLayoutOfExpr(e.Left)
			if err != nil {
				return scalar{}, err
			}
			name, isName := e.Index.(*ast.Identifier)
			if !isName {
				return scalar{}, unsupported("a field access %s", e.String())
			}
			field, has := base.fields[name.Value]
			if !has || field.kind != fieldScalar {
				return scalar{}, unsupported("%s is not a scalar field", e.String())
			}
			return field.typ, nil
		}
		if arr := g.arrayOperand(e.Left); arr != nil {
			return arr.elem, nil
		}
		sp, err := g.spanOperand(e.Left)
		if err != nil {
			return scalar{}, err
		}
		return sp.elem, nil
	case *ast.InvocationExpression:
		ident, isIdent := e.Function.(*ast.Identifier)
		if !isIdent {
			return scalar{}, unsupported("a call through a value")
		}
		if ident.Value == "len" && len(e.Arguments) == 1 {
			if g.arrayOperand(e.Arguments[0]) != nil {
				return scalars["u32"], nil
			}
			if _, err := g.spanOperand(e.Arguments[0]); err != nil {
				return scalar{}, err
			}
			return scalars["u32"], nil
		}
		if s, isConv := scalars[ident.Value]; isConv && len(e.Arguments) == 1 && ident.Value != "byte" {
			return s, nil
		}
		if target, op, source, isConv := typechecker.ConversionParts(ident.Value); isConv && len(e.Arguments) == 1 {
			t, okT := scalars[target]
			src, okS := scalars[source]
			if !okT || !okS {
				return scalar{}, unsupported("a conversion between %s and %s", source, target)
			}
			switch {
			case op == "trunc" || op == "bits":
			case op == "round" && t.isFloat:
			case op == "saturating" && src.isFloat && !t.isFloat:
			default:
				return scalar{}, unsupported("a %s conversion", op)
			}
			return t, nil
		}
		if typechecker.FloatIntrinsicName(ident.Value) {
			if _, shadowed := g.functions[ident.Value]; !shadowed {
				name, known := g.tc.ArithmeticType(e.Token)
				if !known || !typechecker.IsFloatName(name) {
					return scalar{}, unsupported("the intrinsic %s without a recorded width", ident.Value)
				}
				if _, ok := floatIntrinsicOps[ident.Value]; !ok {
					return scalar{}, unsupported("the intrinsic %s", ident.Value)
				}
				return scalars[name], nil
			}
		}
		if callee, ok := g.functions[ident.Value]; ok {
			if callee.ReturnType == nil || callee.ReturnType.String() == "()" {
				return scalar{}, unsupported("a call to %s (no result) in value position", ident.Value)
			}
			if s, ok := scalarOf(callee.ReturnType); ok {
				return s, nil
			}
			return scalar{}, unsupported("a call to %s returning %s", ident.Value, callee.ReturnType.String())
		}
		return scalar{}, unsupported("a call to %s", ident.Value)
	case *ast.MatchExpression:
		whenTrue, _, ok := boolConditional(e)
		if !ok {
			if len(e.Arms) == 0 {
				return scalar{}, unsupported("a match without arms")
			}
			return g.typeOf(e.Arms[0].Body, hint)
		}
		return g.typeOf(whenTrue, hint)
	case *ast.BlockExpression:
		if r := e.Result(); r != nil {
			return g.typeOf(r, hint)
		}
		return scalar{}, unsupported("a block without a result")
	}
	return scalar{}, unsupported("%T", expr)
}

// ---- the body -------------------------------------------------------------

// lowerBody lowers the function body; the result (if any) ends in w0/x0
// and control reaches ret with the frame released.
func (g *generator) lowerBody(body ast.Expression) ([]asm.Item, error) {
	retLabel := g.newLabel("ret")
	trapLabel := g.newLabel("trap")
	g.trap = trapLabel
	switch b := body.(type) {
	case *ast.BlockExpression:
		if b.Block == nil {
			return nil, unsupported("an empty body")
		}
		if err := g.lowerStatements(b.Block.Statements, true, retLabel); err != nil {
			return nil, err
		}
	default:
		if g.resultRecord != nil {
			if err := g.resultRecordExpr(body); err != nil {
				return nil, err
			}
			break
		}
		if g.result == nil {
			return nil, unsupported("an expression body in a function without a result")
		}
		if err := g.resultExpr(body); err != nil {
			return nil, err
		}
	}
	g.label(retLabel)
	g.epilogue()
	if g.usedTrap {
		g.label(trapLabel)
		g.emit("brk", imm(1))
	}
	return g.items, nil
}

func (g *generator) epilogue() {
	frame := g.frameSize()
	for i := 0; i < g.usedCalleeV; i += 2 {
		offset := g.saveBaseV() + int64(8*i)
		if i+1 < g.usedCalleeV {
			g.emit("ldp", dr(vecCalleeLow+i), dr(vecCalleeLow+i+1), mem(offset))
		} else {
			g.emit("ldr", dr(vecCalleeLow+i), mem(offset))
		}
	}
	for i := 0; i < g.usedCallee; i += 2 {
		offset := g.saveBase() + int64(8*i)
		if i+1 < g.usedCallee {
			g.emit("ldp", xr(calleeLow+i), xr(calleeLow+i+1), mem(offset))
		} else {
			g.emit("ldr", xr(calleeLow+i), mem(offset))
		}
	}
	if g.hasCalls {
		g.emit("ldp", xr(29), xr(30), mem(0))
	}
	if frame > 0 {
		g.emit("add", sp(), sp(), imm(frame))
	}
	g.emit("ret")
}

// moveResult places a value in the result register.
func (g *generator) moveResult(r int, s scalar) {
	if s.isFloat {
		g.emit("fmov", reg(vecBase, s), reg(r, s))
		return
	}
	g.emit("mov", reg(0, s), reg(r, s))
}

// lowerStatements lowers a block; in a function body the last expression
// statement is the result.
func (g *generator) lowerStatements(stmts []ast.Statement, functionBody bool, retLabel string) error {
	for i, stmt := range stmts {
		last := functionBody && i == len(stmts)-1
		g.line = statementLine(stmt)
		switch s := stmt.(type) {
		case *ast.VariableDeclaration:
			if elem, length, isArray := arrayOf(s.Type); isArray {
				if err := g.lowerArrayDeclaration(s, elem, length); err != nil {
					return err
				}
				continue
			}
			if s.Type != nil && g.isArrayType(s.Type) {
				_, elemLayout, length, err := g.arrayTypeOf(s.Type)
				if err != nil {
					return err
				}
				if err := g.lowerRecordArrayDeclaration(s, elemLayout, length); err != nil {
					return err
				}
				continue
			}
			if typeName, isRecord := g.recordTypeName(s.Type); isRecord {
				if err := g.lowerRecordDeclaration(s, typeName); err != nil {
					return err
				}
				continue
			}
			if target, isSpan := g.spanTypeOf(s.Type); isSpan {
				if err := g.lowerSpanDeclaration(s, target); err != nil {
					return err
				}
				continue
			}
			if s.Value == nil {
				return unsupported("a local without an initializer")
			}
			var typ scalar
			if s.Type != nil {
				t, ok := scalarOf(s.Type)
				if !ok {
					return unsupported("a local of type %s", s.Type.String())
				}
				typ = t
			} else {
				t, err := g.typeOf(s.Value, nil)
				if err != nil {
					return err
				}
				typ = t
			}
			r, err := g.expr(s.Value, &typ)
			if err != nil {
				return err
			}
			g.declare(s.Name.Value, typ)
			g.items = append(g.items, g.storeVar(s.Name.Value, r))
			g.release(r)
		case *ast.AssignmentStatement:
			if dst, isRecord := g.records[s.Name.Value]; isRecord {
				// `q = p` / `q = f(p)` / `q = .Some(x)`: a whole-record copy.
				from, err := g.recordValueAs(s.Value, dst.layout)
				if err != nil {
					return err
				}
				if from.layout != dst.layout {
					return unsupported("an assignment of a %s to the %s %s", from.layout.name, dst.layout.name, s.Name.Value)
				}
				if err := g.copyRecord(dst, from); err != nil {
					return err
				}
				g.releaseTemps(from.temps)
				continue
			}
			typ, ok := g.types[s.Name.Value]
			if !ok {
				return unsupported("an assignment to %s", s.Name.Value)
			}
			r, err := g.expr(s.Value, &typ)
			if err != nil {
				return err
			}
			g.items = append(g.items, g.storeVar(s.Name.Value, r))
			g.release(r)
		case *ast.IndexAssignmentStatement:
			if err := g.elementStore(s); err != nil {
				return err
			}
		case *ast.WhileStatement:
			if err := g.lowerWhile(s); err != nil {
				return err
			}
		case *ast.IfStatement:
			if err := g.lowerIf(s); err != nil {
				return err
			}
		case *ast.BreakStatement:
			if len(g.loops) == 0 {
				return unsupported("break outside a loop")
			}
			g.emit("b", asm.Symbol{Name: g.loops[len(g.loops)-1]})
		case *ast.BlockStatement:
			g.pushScope()
			err := g.lowerStatements(s.Statements, false, "")
			g.popScope()
			if err != nil {
				return err
			}
		case *ast.ExpressionStatement:
			if last && !s.Discard {
				if g.resultRecord != nil {
					if err := g.resultRecordExpr(s.Expression); err != nil {
						return err
					}
					continue
				}
				if g.result == nil {
					// A unit function whose last statement is an expression.
					if err := g.effect(s.Expression); err != nil {
						return err
					}
					continue
				}
				if err := g.resultExpr(s.Expression); err != nil {
					return err
				}
				continue
			}
			if match, isMatch := s.Expression.(*ast.MatchExpression); isMatch {
				if err := g.lowerConditionalStatement(match); err != nil {
					return err
				}
				continue
			}
			if err := g.effect(s.Expression); err != nil {
				return err
			}
		default:
			return unsupported("%T", stmt)
		}
	}
	if functionBody && (g.result != nil || g.resultRecord != nil) {
		if len(stmts) == 0 {
			return unsupported("an empty body with a result")
		}
		if es, ok := stmts[len(stmts)-1].(*ast.ExpressionStatement); !ok || es.Discard {
			return unsupported("a body whose last statement is not its result")
		}
	}
	return nil
}

// effect evaluates an expression for its effects: a call, or assert.
func (g *generator) effect(expr ast.Expression) error {
	call, isCall := expr.(*ast.InvocationExpression)
	if !isCall {
		return unsupported("an expression statement that is not a call")
	}
	ident, isIdent := call.Function.(*ast.Identifier)
	if !isIdent {
		return unsupported("a call through a value")
	}
	if ident.Value == "assert" && len(call.Arguments) == 1 {
		b := scalars["Bool"]
		r, err := g.expr(call.Arguments[0], &b)
		if err != nil {
			return err
		}
		g.usedTrap = true
		g.emit("cbz", wr(r), asm.Symbol{Name: g.trap})
		g.release(r)
		return nil
	}
	r, err := g.call(call)
	if err != nil {
		return err
	}
	if r >= 0 {
		g.release(r)
	}
	return nil
}

func (g *generator) lowerWhile(loop *ast.WhileStatement) error {
	head, end := g.newLabel("loop"), g.newLabel("done")
	g.label(head)
	if err := g.condition(loop.Condition, end); err != nil {
		return err
	}
	g.loops = append(g.loops, end)
	g.pushScope()
	err := g.lowerStatements(loop.Body.Statements, false, "")
	g.popScope()
	g.loops = g.loops[:len(g.loops)-1]
	if err != nil {
		return err
	}
	g.emit("b", asm.Symbol{Name: head})
	g.label(end)
	return nil
}

func (g *generator) lowerIf(s *ast.IfStatement) error {
	elseLabel, end := g.newLabel("else"), g.newLabel("endif")
	if err := g.condition(s.Condition, elseLabel); err != nil {
		return err
	}
	if s.Consequence != nil {
		g.pushScope()
		err := g.lowerStatements(s.Consequence.Statements, false, "")
		g.popScope()
		if err != nil {
			return err
		}
	}
	g.emit("b", asm.Symbol{Name: end})
	g.label(elseLabel)
	switch alt := s.Alternative.(type) {
	case nil:
	case *ast.IfStatement:
		if err := g.lowerIf(alt); err != nil {
			return err
		}
	case *ast.BlockStatement:
		g.pushScope()
		err := g.lowerStatements(alt.Statements, false, "")
		g.popScope()
		if err != nil {
			return err
		}
	default:
		return unsupported("an else of %T", alt)
	}
	g.label(end)
	return nil
}

// lowerConditionalStatement: `c ? { ... } | { ... }` in statement position.
func (g *generator) lowerConditionalStatement(match *ast.MatchExpression) error {
	whenTrue, whenFalse, ok := boolConditional(match)
	if !ok {
		return g.lowerMatch(match, g.lowerArm)
	}
	elseLabel, end := g.newLabel("else"), g.newLabel("endif")
	if err := g.condition(match.Scrutinee, elseLabel); err != nil {
		return err
	}
	if err := g.lowerArm(whenTrue); err != nil {
		return err
	}
	g.emit("b", asm.Symbol{Name: end})
	g.label(elseLabel)
	if err := g.lowerArm(whenFalse); err != nil {
		return err
	}
	g.label(end)
	return nil
}

func (g *generator) lowerArm(arm ast.Expression) error {
	block, isBlock := arm.(*ast.BlockExpression)
	if !isBlock {
		// An arm that is a call or assert in statement position.
		return g.effect(arm)
	}
	if block.Block == nil {
		return nil
	}
	g.pushScope()
	defer g.popScope()
	return g.lowerStatements(block.Block.Statements, false, "")
}

// condition evaluates a Bool expression and branches to target when false.
func (g *generator) condition(expr ast.Expression, target string) error {
	return g.conditionBranch(expr, target, true)
}

var inverseCondition = map[string]string{"eq": "ne", "ne": "eq", "lo": "hs", "hs": "lo", "ls": "hi", "hi": "ls", "lt": "ge", "ge": "lt", "le": "gt", "gt": "le"}

// conditionBranch evaluates a Bool expression and branches to target when
// it is false (jumpIfFalse) or true. A comparison of simple operands —
// variables in registers, a span length, a small constant — emits directly
// as `cmp` then `b.cond`, the shape the checker's guards and the
// verifier's loop recognizer read.
func (g *generator) conditionBranch(expr ast.Expression, target string, jumpIfFalse bool) error {
	if infix, ok := expr.(*ast.InfixExpression); ok {
		if codes, isComparison := conditionCodes[infix.Operator]; isComparison {
			if operand, err := g.operandType(infix); err == nil && !operand.isFloat {
				left, leftOK := g.simpleOperand(infix.Left, operand, false)
				right, rightOK := g.simpleOperand(infix.Right, operand, true)
				if leftOK && rightOK {
					code := codes[0]
					if operand.signed {
						code = codes[1]
					}
					if jumpIfFalse {
						code = inverseCondition[code]
					}
					g.emit("cmp", left, right)
					g.branch(code, target)
					return nil
				}
			}
		}
	}
	b := scalars["Bool"]
	r, err := g.expr(expr, &b)
	if err != nil {
		return err
	}
	if jumpIfFalse {
		g.emit("cbz", wr(r), asm.Symbol{Name: target})
	} else {
		g.emit("cbnz", wr(r), asm.Symbol{Name: target})
	}
	g.release(r)
	return nil
}

// simpleOperand spells an operand `cmp` takes directly: a variable in its
// register, a span's length register, or (on the right) a constant below
// 4096, possibly under a widening constructor.
func (g *generator) simpleOperand(expr ast.Expression, typ scalar, allowImm bool) (asm.Operand, bool) {
	switch e := expr.(type) {
	case *ast.Identifier:
		if v, inReg := g.regs[e.Value]; inReg && v >= 0 && !typ.isFloat {
			if t, ok := g.types[e.Value]; ok && !t.isFloat && t.wide() == typ.wide() {
				return reg(v, typ), true
			}
		}
	case *ast.InvocationExpression:
		if ident, ok := e.Function.(*ast.Identifier); ok && len(e.Arguments) == 1 {
			if ident.Value == "len" && !typ.wide() {
				if sp, err := g.spanOperand(e.Arguments[0]); err == nil {
					return wr(sp.lenReg), true
				}
			}
			if _, isConv := scalars[ident.Value]; isConv && allowImm {
				if v, ok := constantValue(e.Arguments[0]); ok && v >= 0 && v < 4096 {
					return imm(v), true
				}
			}
		}
	case *ast.IntegerLiteral:
		if allowImm && e.Value >= 0 && e.Value < 4096 {
			return imm(e.Value), true
		}
	}
	return nil, false
}

// ---- expressions ------------------------------------------------------------

// expr evaluates an expression into a fresh scratch register, normalized at
// its own type; hint types literals.
func (g *generator) expr(expr ast.Expression, hint *scalar) (int, error) {
	typ, err := g.typeOf(expr, hint)
	if err != nil {
		return 0, err
	}
	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		r, err := g.alloc(typ)
		if err != nil {
			return 0, err
		}
		g.constant(r, uint64(e.Value), typ)
		return r, nil
	case *ast.FloatLiteral:
		value, ok := typechecker.FloatLiteralValue(e.Text, typ.name)
		if !ok {
			return 0, unsupported("the float literal %s at %s", e.Text, typ.name)
		}
		r, err := g.alloc(typ)
		if err != nil {
			return 0, err
		}
		if err := g.floatConstant(r, value, typ); err != nil {
			return 0, err
		}
		return r, nil
	case *ast.Boolean:
		r, err := g.alloc(typ)
		if err != nil {
			return 0, err
		}
		v := uint64(0)
		if e.Value {
			v = 1
		}
		g.constant(r, v, typ)
		return r, nil
	case *ast.Identifier:
		r, err := g.alloc(typ)
		if err != nil {
			return 0, err
		}
		g.items = append(g.items, g.loadVar(e.Value, r))
		return r, nil
	case *ast.InfixExpression:
		return g.infix(e, typ)
	case *ast.PrefixExpression:
		return g.prefix(e, typ)
	case *ast.IndexExpression:
		return g.element(e)
	case *ast.InvocationExpression:
		ident := e.Function.(*ast.Identifier)
		if ident.Value == "len" && len(e.Arguments) == 1 {
			r, err := g.alloc(scalars["u32"])
			if err != nil {
				return 0, err
			}
			if arr := g.arrayOperand(e.Arguments[0]); arr != nil {
				g.constant(r, uint64(arr.length), scalars["u32"])
				return r, nil
			}
			sp, err := g.spanOperand(e.Arguments[0])
			if err != nil {
				return 0, err
			}
			g.emit("mov", wr(r), wr(sp.lenReg))
			return r, nil
		}
		if target, isConv := scalars[ident.Value]; isConv && len(e.Arguments) == 1 && ident.Value != "byte" {
			return g.convert(e.Arguments[0], target, "")
		}
		if targetName, op, _, isConv := typechecker.ConversionParts(ident.Value); isConv && len(e.Arguments) == 1 {
			// The {target}_{op}_{source} family typeOf admitted.
			return g.convert(e.Arguments[0], scalars[targetName], op)
		}
		if typechecker.FloatIntrinsicName(ident.Value) {
			if _, shadowed := g.functions[ident.Value]; !shadowed {
				return g.intrinsic(e, typ)
			}
		}
		return g.call(e)
	case *ast.MatchExpression:
		whenTrue, whenFalse, isBool := boolConditional(e)
		if !isBool {
			out, err := g.alloc(typ)
			if err != nil {
				return 0, err
			}
			err = g.lowerMatch(e, func(body ast.Expression) error {
				r, err := g.expr(body, &typ)
				if err != nil {
					return err
				}
				g.emit(moveOf(typ), reg(out, typ), reg(r, typ))
				g.release(r)
				return nil
			})
			if err != nil {
				return 0, err
			}
			return out, nil
		}
		elseLabel, end := g.newLabel("else"), g.newLabel("endif")
		if err := g.condition(e.Scrutinee, elseLabel); err != nil {
			return 0, err
		}
		out, err := g.alloc(typ)
		if err != nil {
			return 0, err
		}
		t, err := g.expr(whenTrue, &typ)
		if err != nil {
			return 0, err
		}
		g.emit(moveOf(typ), reg(out, typ), reg(t, typ))
		g.release(t)
		g.emit("b", asm.Symbol{Name: end})
		g.label(elseLabel)
		f, err := g.expr(whenFalse, &typ)
		if err != nil {
			return 0, err
		}
		g.emit(moveOf(typ), reg(out, typ), reg(f, typ))
		g.release(f)
		g.label(end)
		return out, nil
	case *ast.BlockExpression:
		if e.Block == nil || len(e.Block.Statements) == 0 {
			return 0, unsupported("an empty block in value position")
		}
		g.pushScope()
		defer g.popScope()
		stmts := e.Block.Statements
		if err := g.lowerStatements(stmts[:len(stmts)-1], false, ""); err != nil {
			return 0, err
		}
		es, ok := stmts[len(stmts)-1].(*ast.ExpressionStatement)
		if !ok {
			return 0, unsupported("a block whose last statement is not an expression")
		}
		return g.expr(es.Expression, &typ)
	}
	return 0, unsupported("%T", expr)
}

// constant materializes a value at a type (movz/movk pieces).
// floatConstant materializes a float: its IEEE bit pattern through an
// integer scratch register and fmov (exact for every value).
func (g *generator) floatConstant(r int, value float64, s scalar) error {
	bits := scalars["u64"]
	pattern := math.Float64bits(value)
	if !s.wide() {
		bits = scalars["u32"]
		pattern = uint64(math.Float32bits(float32(value)))
	}
	t, err := g.alloc(bits)
	if err != nil {
		return err
	}
	g.constant(t, pattern, bits)
	g.emit("fmov", reg(r, s), reg(t, bits))
	g.release(t)
	return nil
}

func (g *generator) constant(r int, v uint64, s scalar) {
	if !s.wide() {
		v &= 0xffffffff
		// Narrow signed values keep their sign extension within the word.
		if s.signed && s.bits < 32 {
			v = uint64(int64(int32(v)<<uint(32-s.bits)>>uint(32-s.bits))) & 0xffffffff
		}
	}
	dst := reg(r, s)
	if v == 0 {
		g.emit("mov", dst, reg(31, s))
		return
	}
	first := true
	for shift := 0; shift < 64; shift += 16 {
		if !s.wide() && shift >= 32 {
			break
		}
		piece := (v >> uint(shift)) & 0xffff
		if piece == 0 {
			continue
		}
		if first {
			g.emit("movz", dst, asm.Immediate{Value: int64(piece), Shift: int64(shift)})
			first = false
		} else {
			g.emit("movk", dst, asm.Immediate{Value: int64(piece), Shift: int64(shift)})
		}
	}
}

// normalize re-establishes a narrow type's representation after an
// operation on the whole register.
func (g *generator) normalize(r int, s scalar) {
	for _, it := range g.normalizeInto(r, s) {
		g.items = append(g.items, it)
	}
}

func (g *generator) normalizeInto(r int, s scalar) []asm.Item {
	switch {
	case s.isFloat, s.bits >= 32:
		return nil
	case s.signed && s.bits == 8:
		return []asm.Item{g.ins("sxtb", wr(r), wr(r))}
	case s.signed:
		return []asm.Item{g.ins("sxth", wr(r), wr(r))}
	case s.bits == 8:
		return []asm.Item{g.ins("and", wr(r), wr(r), imm(0xff))}
	default:
		return []asm.Item{g.ins("and", wr(r), wr(r), imm(0xffff))}
	}
}

var conditionCodes = map[string][2]string{
	"==": {"eq", "eq"}, "!=": {"ne", "ne"},
	"<": {"lo", "lt"}, "<=": {"ls", "le"}, ">": {"hi", "gt"}, ">=": {"hs", "ge"},
}

// floatConditionCodes read fcmp's flags as C does: an unordered pair is
// unequal and neither less nor greater (mi, ls, gt, ge are all false when
// V is set; ne is true).
var floatConditionCodes = map[string]string{"==": "eq", "!=": "ne", "<": "mi", "<=": "ls", ">": "gt", ">=": "ge"}

// floatIntrinsicOps are the correctly rounded intrinsics that are one
// instruction each; fma is fmadd (nothing else is ever contracted).
var floatIntrinsicOps = map[string]string{
	"sqrt": "fsqrt", "abs": "fabs", "floor": "frintm", "ceil": "frintp", "trunc": "frintz", "round": "frinta", "round_even": "frintn",
	"min": "fmin", "max": "fmax", "min_num": "fminnm", "max_num": "fmaxnm", "fma": "fmadd",
}

func (g *generator) infix(e *ast.InfixExpression, typ scalar) (int, error) {
	switch e.Operator {
	case "&&", "||":
		out, err := g.alloc(scalars["Bool"])
		if err != nil {
			return 0, err
		}
		end := g.newLabel("short")
		b := scalars["Bool"]
		l, err := g.expr(e.Left, &b)
		if err != nil {
			return 0, err
		}
		g.emit("mov", wr(out), wr(l))
		g.release(l)
		if e.Operator == "&&" {
			g.emit("cbz", wr(out), asm.Symbol{Name: end})
		} else {
			g.emit("cbnz", wr(out), asm.Symbol{Name: end})
		}
		rr, err := g.expr(e.Right, &b)
		if err != nil {
			return 0, err
		}
		g.emit("mov", wr(out), wr(rr))
		g.release(rr)
		g.label(end)
		return out, nil
	case "==", "!=", "<", "<=", ">", ">=":
		operand, err := g.operandType(e)
		if err != nil {
			return 0, err
		}
		l, err := g.expr(e.Left, &operand)
		if err != nil {
			return 0, err
		}
		r, err := g.expr(e.Right, &operand)
		if err != nil {
			return 0, err
		}
		if operand.isFloat {
			// IEEE comparison: unordered operands compare false except for !=.
			g.emit("fcmp", reg(l, operand), reg(r, operand))
			g.release(l)
			g.release(r)
			out, err := g.alloc(scalars["Bool"])
			if err != nil {
				return 0, err
			}
			g.emit("cset", wr(out), asm.Condition{Code: floatConditionCodes[e.Operator]})
			return out, nil
		}
		g.emit("cmp", reg(l, operand), reg(r, operand))
		g.release(r)
		code := conditionCodes[e.Operator][0]
		if operand.signed {
			code = conditionCodes[e.Operator][1]
		}
		g.emit("cset", wr(l), asm.Condition{Code: code})
		return l, nil
	}
	l, err := g.expr(e.Left, &typ)
	if err != nil {
		return 0, err
	}
	if typ.isFloat {
		r, err := g.expr(e.Right, &typ)
		if err != nil {
			return 0, err
		}
		op, ok := map[string]string{"+": "fadd", "-": "fsub", "*": "fmul", "/": "fdiv"}[e.Operator]
		if !ok {
			return 0, unsupported("operator %s on %s", e.Operator, typ.name)
		}
		g.emit(op, reg(l, typ), reg(l, typ), reg(r, typ))
		g.release(r)
		return l, nil
	}
	switch e.Operator {
	case "<<", ">>":
		if typ.signed {
			return 0, unsupported("a shift of a signed operand")
		}
		count, isConst := constantValue(e.Right)
		if isConst {
			if count < 0 || count >= int64(typ.bits) {
				return 0, unsupported("a constant shift count of %d", count)
			}
			op := "lsl"
			if e.Operator == ">>" {
				op = "lsr"
			}
			g.emit(op, reg(l, typ), reg(l, typ), imm(count))
			g.normalize(l, typ)
			return l, nil
		}
		r, err := g.expr(e.Right, &typ)
		if err != nil {
			return 0, err
		}
		// A count at or beyond the width traps (10-syntax.md §3b).
		g.usedTrap = true
		g.emit("cmp", reg(r, typ), imm(int64(typ.bits)))
		g.branch("hs", g.trap)
		op := "lsl"
		if e.Operator == ">>" {
			op = "lsr"
		}
		g.emit(op, reg(l, typ), reg(l, typ), reg(r, typ))
		g.release(r)
		g.normalize(l, typ)
		return l, nil
	}
	r, err := g.expr(e.Right, &typ)
	if err != nil {
		return 0, err
	}
	switch e.Operator {
	case "+":
		g.emit("add", reg(l, typ), reg(l, typ), reg(r, typ))
	case "-":
		g.emit("sub", reg(l, typ), reg(l, typ), reg(r, typ))
	case "*":
		g.emit("mul", reg(l, typ), reg(l, typ), reg(r, typ))
	case "&":
		g.emit("and", reg(l, typ), reg(l, typ), reg(r, typ))
	case "|":
		g.emit("orr", reg(l, typ), reg(l, typ), reg(r, typ))
	case "^":
		g.emit("eor", reg(l, typ), reg(l, typ), reg(r, typ))
	case "/", "%":
		// Division by zero traps; MIN / -1 and MIN % -1 wrap as the C
		// helpers state (sdiv and msub give exactly that).
		g.usedTrap = true
		g.emit("cbz", reg(r, typ), asm.Symbol{Name: g.trap})
		div := "udiv"
		if typ.signed {
			div = "sdiv"
		}
		if e.Operator == "/" {
			g.emit(div, reg(l, typ), reg(l, typ), reg(r, typ))
		} else {
			q, err := g.alloc(typ)
			if err != nil {
				return 0, err
			}
			g.emit(div, reg(q, typ), reg(l, typ), reg(r, typ))
			g.emit("msub", reg(l, typ), reg(q, typ), reg(r, typ), reg(l, typ))
			g.release(q)
		}
	default:
		return 0, unsupported("operator %s", e.Operator)
	}
	g.release(r)
	g.normalize(l, typ)
	return l, nil
}

// operandType is the common type of a comparison's operands.
func (g *generator) operandType(e *ast.InfixExpression) (scalar, error) {
	if s, err := g.typeOf(e.Left, nil); err == nil && !isLiteral(e.Left) {
		return s, nil
	}
	if s, err := g.typeOf(e.Right, nil); err == nil && !isLiteral(e.Right) {
		return s, nil
	}
	return g.typeOf(e.Left, nil)
}

func isLiteral(expr ast.Expression) bool {
	switch expr.(type) {
	case *ast.IntegerLiteral, *ast.Boolean:
		return true
	}
	return false
}

func constantValue(expr ast.Expression) (int64, bool) {
	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		return e.Value, true
	case *ast.InvocationExpression:
		if ident, ok := e.Function.(*ast.Identifier); ok && len(e.Arguments) == 1 {
			if _, isConv := scalars[ident.Value]; isConv {
				return constantValue(e.Arguments[0])
			}
		}
	}
	return 0, false
}

// isConversion reports the conversion spellings the subset lowers inline
// (not calls): `u32(x)`, `u16_trunc_u64(x)`, `i32_bits_u32(x)`,
// `f64_round_i32(x)`, `i32_saturating_f64(x)`.
func isConversion(name string) bool {
	if _, isCtor := scalars[name]; isCtor && name != "byte" {
		return true
	}
	_, op, _, ok := typechecker.ConversionParts(name)
	return ok && (op == "trunc" || op == "bits" || op == "round" || op == "saturating")
}

// mentionsFloat reports a function touching floating point: a float
// parameter, result, or span element, a float literal, or a float name in
// a local's type or a conversion.
func mentionsFloat(fn *ast.FunctionStatement) bool {
	isFloatType := func(expr ast.Expression) bool {
		if s, ok := scalarOf(expr); ok && s.isFloat {
			return true
		}
		if sp, ok := spanOf(expr); ok && sp.elem.isFloat {
			return true
		}
		return false
	}
	for _, p := range fn.Parameters {
		if isFloatType(p.Type) {
			return true
		}
	}
	if fn.ReturnType != nil && isFloatType(fn.ReturnType) {
		return true
	}
	found := false
	walk(fn.Body, func(n ast.Node) {
		switch e := n.(type) {
		case *ast.FloatLiteral:
			found = true
		case *ast.VariableDeclaration:
			if e.Type != nil && isFloatType(e.Type) {
				found = true
			}
		case *ast.InvocationExpression:
			if ident, ok := e.Function.(*ast.Identifier); ok && (strings.Contains(ident.Value, "f32") || strings.Contains(ident.Value, "f64") || typechecker.FloatIntrinsicName(ident.Value)) {
				found = true
			}
		}
	})
	return found
}

func (g *generator) prefix(e *ast.PrefixExpression, typ scalar) (int, error) {
	switch e.Operator {
	case "!":
		b := scalars["Bool"]
		r, err := g.expr(e.Right, &b)
		if err != nil {
			return 0, err
		}
		g.emit("eor", wr(r), wr(r), imm(1))
		return r, nil
	case "-":
		r, err := g.expr(e.Right, &typ)
		if err != nil {
			return 0, err
		}
		if typ.isFloat {
			g.emit("fneg", reg(r, typ), reg(r, typ))
			return r, nil
		}
		g.emit("neg", reg(r, typ), reg(r, typ))
		g.normalize(r, typ)
		return r, nil
	case "^":
		r, err := g.expr(e.Right, &typ)
		if err != nil {
			return 0, err
		}
		g.emit("mvn", reg(r, typ), reg(r, typ))
		g.normalize(r, typ)
		return r, nil
	}
	return 0, unsupported("prefix operator %s", e.Operator)
}

// convert lowers `T(x)`: the operand's bits at the new width — a widening
// of a signed operand sign-extends, everything else truncates or zero-fills.
func (g *generator) convert(operand ast.Expression, target scalar, op string) (int, error) {
	source, err := g.typeOf(operand, &target)
	if err != nil {
		return 0, err
	}
	r, err := g.expr(operand, &source)
	if err != nil {
		return 0, err
	}
	if source.isFloat || target.isFloat {
		return g.convertFloat(r, source, target, op)
	}
	switch {
	case source.wide() && target.wide():
	case !source.wide() && target.wide():
		if source.signed {
			g.emit("sxtw", xr(r), wr(r))
		} else {
			g.emit("mov", wr(r), wr(r)) // the upper half is already zero: a w write clears it
		}
	case source.wide() && !target.wide():
		g.emit("mov", wr(r), wr(r))
		g.normalize(r, target)
	default:
		g.normalize(r, target)
	}
	return r, nil
}

// convertFloat lowers the conversions with a float on either side
// (docs/spec/20-types.md §11.3.4): widening and `round` between floats
// through fcvt, integer to float through scvtf/ucvtf, `bits` through fmov,
// `saturating` float to integer through fcvtzs/fcvtzu (which saturate and
// send NaN to 0, the helper's semantics), and `trunc` float to integer with
// the C backend's range check first — NaN or a value outside the target's
// open interval traps.
func (g *generator) convertFloat(r int, source, target scalar, op string) (int, error) {
	switch {
	case source.isFloat && target.isFloat:
		if source.bits == target.bits {
			return r, nil
		}
		g.emit("fcvt", reg(r, target), reg(r, source))
		return r, nil
	case !source.isFloat && target.isFloat:
		f, err := g.alloc(target)
		if err != nil {
			return 0, err
		}
		if op == "bits" {
			g.emit("fmov", reg(f, target), reg(r, source))
		} else if source.signed {
			g.emit("scvtf", reg(f, target), reg(r, source))
		} else {
			g.emit("ucvtf", reg(f, target), reg(r, source))
		}
		g.release(r)
		return f, nil
	}
	// Float to integer.
	out, err := g.alloc(target)
	if err != nil {
		return 0, err
	}
	switch op {
	case "bits":
		g.emit("fmov", reg(out, target), reg(r, source))
	case "saturating":
		// fcvtzs/fcvtzu saturate at the register's range and send NaN to 0;
		// a narrower target is clamped to its own range afterwards.
		if target.signed {
			g.emit("fcvtzs", reg(out, target), reg(r, source))
		} else {
			g.emit("fcvtzu", reg(out, target), reg(r, source))
		}
		if target.bits < 32 {
			if err := g.clampNarrow(out, target); err != nil {
				return 0, err
			}
		}
		g.normalize(out, target)
	case "trunc":
		low, lowInclusive, high := floatIntegerBounds(target)
		bound, err := g.alloc(source)
		if err != nil {
			return 0, err
		}
		g.usedTrap = true
		if err := g.floatConstant(bound, low, source); err != nil {
			return 0, err
		}
		g.emit("fcmp", reg(r, source), reg(bound, source))
		if lowInclusive {
			g.branch("lt", g.trap) // x < low, or unordered
		} else {
			g.branch("le", g.trap) // x <= low, or unordered
		}
		if err := g.floatConstant(bound, high, source); err != nil {
			return 0, err
		}
		g.emit("fcmp", reg(r, source), reg(bound, source))
		g.branch("ge", g.trap) // x >= high (NaN already trapped)
		g.release(bound)
		if target.signed {
			g.emit("fcvtzs", reg(out, target), reg(r, source))
		} else {
			g.emit("fcvtzu", reg(out, target), reg(r, source))
		}
		g.normalize(out, target)
	default:
		return 0, unsupported("a %s conversion from %s to %s", op, source.name, target.name)
	}
	g.release(r)
	return out, nil
}

// clampNarrow clamps a 32-bit value in register r into a narrow integer
// type's range (cmp then csel), the saturation fcvtz* cannot do for u8/u16
// and i8/i16.
func (g *generator) clampNarrow(r int, target scalar) error {
	word := scalars["u32"]
	if target.signed {
		word = scalars["i32"]
	}
	t, err := g.alloc(word)
	if err != nil {
		return err
	}
	var max, min int64
	if target.signed {
		max, min = int64(1)<<uint(target.bits-1)-1, -(int64(1) << uint(target.bits-1))
	} else {
		max = int64(1)<<uint(target.bits) - 1
	}
	g.constant(t, uint64(max), word)
	g.emit("cmp", wr(r), wr(t))
	if target.signed {
		g.emit("csel", wr(r), wr(t), wr(r), asm.Condition{Code: "gt"})
		g.constant(t, uint64(min), word)
		g.emit("cmp", wr(r), wr(t))
		g.emit("csel", wr(r), wr(t), wr(r), asm.Condition{Code: "lt"})
	} else {
		g.emit("csel", wr(r), wr(t), wr(r), asm.Condition{Code: "hi"})
	}
	g.release(t)
	return nil
}

// floatIntegerBounds is the C backend's admitted open interval for a
// float-to-integer trunc: (low, high), with low inclusive only for i64.
func floatIntegerBounds(target scalar) (low float64, lowInclusive bool, high float64) {
	switch {
	case target.signed && target.bits == 64:
		return -9223372036854775808.0, true, 9223372036854775808.0
	case target.signed:
		return float64(-(int64(1) << uint(target.bits-1))) - 1, false, float64(int64(1) << uint(target.bits-1))
	case target.bits == 64:
		return -1.0, false, 18446744073709551616.0
	default:
		return -1.0, false, float64(uint64(1) << uint(target.bits))
	}
}

// intrinsic lowers a correctly rounded float intrinsic: every operand at
// the call's recorded width (narrower operands widen exactly first).
func (g *generator) intrinsic(e *ast.InvocationExpression, typ scalar) (int, error) {
	ident := e.Function.(*ast.Identifier)
	op := floatIntrinsicOps[ident.Value]
	var regs []int
	for _, arg := range e.Arguments {
		argType, err := g.typeOf(arg, &typ)
		if err != nil {
			return 0, err
		}
		r, err := g.expr(arg, &argType)
		if err != nil {
			return 0, err
		}
		if !argType.isFloat {
			return 0, unsupported("a non-float operand of %s", ident.Value)
		}
		if argType.bits != typ.bits {
			g.emit("fcvt", reg(r, typ), reg(r, argType))
		}
		regs = append(regs, r)
	}
	switch len(regs) {
	case 1:
		g.emit(op, reg(regs[0], typ), reg(regs[0], typ))
		return regs[0], nil
	case 2:
		g.emit(op, reg(regs[0], typ), reg(regs[0], typ), reg(regs[1], typ))
		g.release(regs[1])
		return regs[0], nil
	case 3:
		// fma(a, b, c) = a*b + c: fmadd d, a, b, c.
		g.emit(op, reg(regs[0], typ), reg(regs[0], typ), reg(regs[1], typ), reg(regs[2], typ))
		g.release(regs[1])
		g.release(regs[2])
		return regs[0], nil
	}
	return 0, unsupported("the intrinsic %s with %d operands", ident.Value, len(regs))
}

// call evaluates a call: arguments into x0–x7, live scratch spilled around
// the bl, the result (if any) into a fresh scratch register (-1 for unit).
func (g *generator) call(e *ast.InvocationExpression) (int, error) {
	return g.callWith(e, nil)
}

// callWith lowers a call; recordResult, when the callee returns a record,
// is the temp that receives it (chunks stored from x0/x1, or written by
// the callee through x8).
func (g *generator) callWith(e *ast.InvocationExpression, recordResult *recordLocal) (int, error) {
	ident := e.Function.(*ast.Identifier)
	callee, ok := g.functions[ident.Value]
	if !ok {
		return 0, unsupported("a call to %s", ident.Value)
	}
	if len(e.Arguments) != len(callee.Parameters) || len(e.Arguments) > 8 {
		return 0, unsupported("a call to %s with %d arguments", ident.Value, len(e.Arguments))
	}
	var resultType *scalar
	if callee.ReturnType != nil && callee.ReturnType.String() != "()" {
		if _, isRecord := g.recordTypeName(callee.ReturnType); isRecord {
			if recordResult == nil {
				return 0, unsupported("a call to %s (returning a record) in scalar position", ident.Value)
			}
		} else {
			s, ok := scalarOf(callee.ReturnType)
			if !ok {
				return 0, unsupported("a call to %s returning %s", ident.Value, callee.ReturnType.String())
			}
			resultType = &s
		}
	}
	// Arguments evaluate into scratch registers first (an argument may
	// itself call), then move to the argument registers: a scalar one, a
	// span or view (`view(&buf)` / `span(&buf)` over an owned array local)
	// its {frame address, u32 length} pair.
	type argument struct {
		regs  []int
		types []scalar
		fixed bool // the registers are a parked span's, not scratch: never released
	}
	var args []argument
	for i, arg := range e.Arguments {
		p := callee.Parameters[i]
		if p.Variadic {
			return 0, unsupported("a call to %s (parameter %s is variadic)", ident.Value, p.Name.Value)
		}
		if s, ok := scalarOf(p.Type); ok {
			r, err := g.expr(arg, &s)
			if err != nil {
				return 0, err
			}
			args = append(args, argument{regs: []int{r}, types: []scalar{s}})
			continue
		}
		if name, isRecord := g.recordTypeName(p.Type); isRecord {
			layout, err := g.layoutOf(name)
			if err != nil {
				return 0, err
			}
			if layout.isHFA() {
				return 0, unsupported("a call to %s passing a homogeneous floating-point aggregate", ident.Value)
			}
			rec, err := g.recordValueAs(arg, layout)
			if err != nil {
				return 0, err
			}
			if rec.layout != layout {
				return 0, unsupported("a call to %s: a %s where %s is expected", ident.Value, rec.layout.name, name)
			}
			if layout.size > 16 {
				// By reference to a copy the callee owns.
				copied := g.tempRecord(layout)
				if err := g.copyRecord(copied, rec); err != nil {
					return 0, err
				}
				g.releaseTemps(rec.temps)
				base, err := g.alloc(scalars["u64"])
				if err != nil {
					return 0, err
				}
				g.emit("add", xr(base), sp(), imm(g.slotMem(copied.offset).Offset))
				args = append(args, argument{regs: []int{base}, types: []scalar{scalars["u64"]}})
				continue
			}
			if rec.inReg || g.slotMem(rec.offset).Offset%8 != 0 {
				// A nested record at an unaligned offset, or an array element
				// addressed through a register: its chunks load from an
				// aligned frame copy (whose slots cover the last chunk).
				aligned := g.tempRecord(layout)
				if err := g.copyRecord(aligned, rec); err != nil {
					return 0, err
				}
				g.releaseTemps(rec.temps)
				rec = aligned
			}
			var chunks []int
			var kinds []scalar
			for i := 0; i < layout.chunks(); i++ {
				r, err := g.alloc(scalars["u64"])
				if err != nil {
					return 0, err
				}
				g.emit("ldr", xr(r), g.slotMem(rec.offset+int64(8*i)))
				chunks = append(chunks, r)
				kinds = append(kinds, scalars["u64"])
			}
			args = append(args, argument{regs: chunks, types: kinds})
			continue
		}
		target, isSpan := g.spanTypeOf(p.Type)
		if !isSpan {
			return 0, unsupported("a call to %s (parameter %s: %s)", ident.Value, p.Name.Value, p.Type.String())
		}
		// A span argument: a named span's pair (a parameter or local, never
		// released), or a fresh pair from view/span(&buf) or subslice.
		value, named, err := g.spanValue(arg, &target, -1, -1)
		if err != nil {
			return 0, unsupported("a call to %s: %v", ident.Value, err)
		}
		args = append(args, argument{regs: []int{value.baseReg, value.lenReg}, types: []scalar{scalars["u64"], scalars["u32"]}, fixed: named})
	}
	general, vector := 0, 0
	for _, arg := range args {
		for j, r := range arg.regs {
			typ := arg.types[j]
			if typ.isFloat {
				g.emit("fmov", reg(vecBase+vector, typ), reg(r, typ))
				vector++
			} else {
				g.emit("mov", reg(general, typ), reg(r, typ))
				general++
			}
			if !arg.fixed {
				g.release(r)
			}
		}
	}
	if general > 8 || vector > 8 {
		return 0, unsupported("a call to %s: the arguments exhaust the argument registers", ident.Value)
	}
	if recordResult != nil && recordResult.layout.size > 16 {
		// The callee writes its result into the temp through x8.
		g.usedX8 = true
		g.emit("add", xr(8), sp(), imm(g.slotMem(recordResult.offset).Offset))
	}
	// Spill the live scratch registers: the callee owns x9–x15 and v16–v23.
	var spilled []int
	for _, r := range g.live {
		if _, ok := g.spill[r]; !ok {
			g.spill[r] = 8 * g.nslots
			g.nslots++
		}
		g.emit("str", spillReg(r), g.slotMem(g.spill[r]))
		spilled = append(spilled, r)
	}
	g.emit("bl", asm.Symbol{Name: ident.Value})
	for _, r := range spilled {
		g.emit("ldr", spillReg(r), g.slotMem(g.spill[r]))
	}
	if recordResult != nil {
		if recordResult.layout.size <= 16 {
			for i := 0; i < recordResult.layout.chunks(); i++ {
				g.emit("str", xr(i), g.slotMem(recordResult.offset+int64(8*i)))
			}
		}
		return -1, nil
	}
	if resultType == nil {
		return -1, nil
	}
	out, err := g.alloc(*resultType)
	if err != nil {
		return 0, err
	}
	if resultType.isFloat {
		g.emit("fmov", reg(out, *resultType), reg(vecBase, *resultType))
	} else {
		g.emit("mov", reg(out, *resultType), reg(0, *resultType))
	}
	return out, nil
}

// arrayArgument reads a span or view argument: `span(&buf)` for a [*]T
// parameter, `view(&buf)` for a []T one, over an owned array local of the
// parameter's element type.
func (g *generator) arrayArgument(arg ast.Expression, target span) (*arrayLocal, error) {
	call, isCall := arg.(*ast.InvocationExpression)
	if !isCall || len(call.Arguments) != 1 {
		return nil, unsupported("a span argument that is not view(&buf) or span(&buf)")
	}
	ident, isIdent := call.Function.(*ast.Identifier)
	if !isIdent || (ident.Value != "view" && ident.Value != "span") {
		return nil, unsupported("a span argument that is not view(&buf) or span(&buf)")
	}
	if target.writable && ident.Value != "span" {
		return nil, unsupported("a view where a span is expected")
	}
	borrow, isBorrow := call.Arguments[0].(*ast.PrefixExpression)
	if !isBorrow || borrow.Operator != "&" {
		return nil, unsupported("%s of %s (only &buf over an owned array local)", ident.Value, call.Arguments[0].String())
	}
	arr := g.arrayOperand(borrow.Right)
	if arr == nil {
		return nil, unsupported("%s of %s (only an owned array local)", ident.Value, borrow.Right.String())
	}
	if arr.elem != target.elem {
		return nil, unsupported("%s over [%d]%s where %s elements are expected", ident.Value, arr.length, arr.elem.name, target.elem.name)
	}
	return arr, nil
}

// spillReg is the whole-register view a scratch register spills as.
func spillReg(r int) asm.Register {
	if r >= vecBase {
		return dr(r - vecBase)
	}
	return xr(r)
}

// ---- helpers ------------------------------------------------------------------

// boolConditional recognizes `cond ? a | b`: two arms on the Bool literals,
// or one literal and a trailing wildcard.
func boolConditional(match *ast.MatchExpression) (whenTrue, whenFalse ast.Expression, ok bool) {
	if match.Scrutinee == nil || len(match.Arms) != 2 {
		return nil, nil, false
	}
	for i, arm := range match.Arms {
		switch pattern := arm.Pattern.(type) {
		case *ast.LiteralPattern:
			lit, isBool := pattern.Value.(*ast.Boolean)
			if !isBool {
				return nil, nil, false
			}
			if lit.Value {
				whenTrue = arm.Body
			} else {
				whenFalse = arm.Body
			}
		case *ast.WildcardPattern:
			if i != 1 {
				return nil, nil, false
			}
			if whenTrue == nil {
				whenTrue = arm.Body
			} else {
				whenFalse = arm.Body
			}
		default:
			return nil, nil, false
		}
	}
	return whenTrue, whenFalse, whenTrue != nil && whenFalse != nil
}

// mentionsCall reports a body with a call to a program function or assert
// (a conversion `u32(x)` is not a call).
func mentionsCall(body ast.Node) bool {
	found := false
	walk(body, func(n ast.Node) {
		if call, ok := n.(*ast.InvocationExpression); ok {
			if ident, ok := call.Function.(*ast.Identifier); ok {
				if isConversion(ident.Value) || ident.Value == "assert" || ident.Value == "len" || ident.Value == "view" || ident.Value == "span" || ident.Value == "subslice" || typechecker.FloatIntrinsicName(ident.Value) {
					return
				}
			}
			found = true
		}
	})
	return found
}

// walk visits the nodes of the subset's shapes.
func walk(n ast.Node, visit func(ast.Node)) {
	if n == nil {
		return
	}
	visit(n)
	switch e := n.(type) {
	case *ast.BlockStatement:
		for _, s := range e.Statements {
			walk(s, visit)
		}
	case *ast.BlockExpression:
		if e.Block != nil {
			walk(e.Block, visit)
		}
	case *ast.ExpressionStatement:
		walk(e.Expression, visit)
	case *ast.VariableDeclaration:
		if e.Value != nil {
			walk(e.Value, visit)
		}
	case *ast.AssignmentStatement:
		walk(e.Value, visit)
	case *ast.IndexAssignmentStatement:
		walk(e.Target, visit)
		walk(e.Value, visit)
	case *ast.IndexExpression:
		walk(e.Left, visit)
		walk(e.Index, visit)
	case *ast.WhileStatement:
		walk(e.Condition, visit)
		walk(e.Body, visit)
	case *ast.IfStatement:
		walk(e.Condition, visit)
		if e.Consequence != nil {
			walk(e.Consequence, visit)
		}
		if e.Alternative != nil {
			walk(e.Alternative, visit)
		}
	case *ast.InfixExpression:
		walk(e.Left, visit)
		walk(e.Right, visit)
	case *ast.PrefixExpression:
		walk(e.Right, visit)
	case *ast.InvocationExpression:
		for _, a := range e.Arguments {
			walk(a, visit)
		}
	case *ast.ArrayLiteral:
		for _, a := range e.Elements {
			walk(a, visit)
		}
	case *ast.RecordLiteral:
		for _, field := range e.FieldOrder {
			if value, given := e.Fields[field.Name]; given {
				walk(value, visit)
			}
		}
	case *ast.VariantExpression:
		if e.Payload != nil {
			walk(e.Payload, visit)
		}
	case *ast.MatchExpression:
		walk(e.Scrutinee, visit)
		for _, arm := range e.Arms {
			walk(arm.Body, visit)
		}
	}
}

func statementLine(stmt ast.Statement) int {
	switch s := stmt.(type) {
	case *ast.VariableDeclaration:
		return s.Token.Line
	case *ast.AssignmentStatement:
		return s.Token.Line
	case *ast.WhileStatement:
		return s.Token.Line
	case *ast.IfStatement:
		return s.Token.Line
	case *ast.ExpressionStatement:
		return s.Token.Line
	case *ast.BreakStatement:
		return s.Token.Line
	case *ast.IndexAssignmentStatement:
		return s.Token.Line
	}
	return 0
}

// ---- spans ------------------------------------------------------------------------

// spanOperand resolves the span or view a `len(v)` / `v[i]` names.
func (g *generator) spanOperand(expr ast.Expression) (span, error) {
	ident, isIdent := expr.(*ast.Identifier)
	if !isIdent {
		return span{}, unsupported("an index into %s (not a span parameter)", expr.String())
	}
	sp, ok := g.spans[ident.Value]
	if !ok {
		return span{}, unsupported("an index into %s (not a span parameter)", ident.Value)
	}
	return sp, nil
}

// guardedIndex evaluates an element index into a 32-bit scratch register
// and emits the checker's guard: `cmp wI, wL; b.hs <trap>` right before the
// access, so an index at or past the length traps and the fall-through
// path carries the fact that wI < len.
func (g *generator) guardedIndex(sp span, index ast.Expression) (int, error) {
	idxType, err := g.typeOf(index, nil)
	if err != nil {
		return 0, err
	}
	if idxType.wide() || idxType.signed || idxType.isBool {
		return 0, unsupported("an element index of type %s (the span idiom walks by a u32 index)", idxType.name)
	}
	r, err := g.expr(index, &idxType)
	if err != nil {
		return 0, err
	}
	g.usedTrap = true
	g.emit("cmp", wr(r), wr(sp.lenReg))
	g.branch("hs", g.trap)
	return r, nil
}

func log2Bytes(bytes int) int {
	n := 0
	for 1<<uint(n) < bytes {
		n++
	}
	return n
}

// arrayOperand names an owned array local, or nil.
func (g *generator) arrayOperand(expr ast.Expression) *arrayLocal {
	p, err := g.placeOf(expr)
	if err != nil {
		return nil
	}
	return p.arr
}

// arrayAddress lowers `buf[i]` to a memory operand: a literal index inside
// the array addresses its slot directly through sp; any other index goes
// through the frame address of the array under the constant guard
// `cmp wI, #N; b.hs trap` — the checker's frame-array idiom. The returned
// registers are released by the caller (the index may be spent as the
// load's destination, so it is returned separately).
func (g *generator) arrayAddress(arr *arrayLocal, index ast.Expression) (address asm.Memory, indexReg, baseReg int, err error) {
	size := int64(arr.elem.bits / 8)
	if k, isConst := constantValue(index); isConst && k >= 0 && k < arr.length {
		return g.memOf(arr.loc().plus(k * size)), -1, -1, nil
	}
	idxType, err := g.typeOf(index, nil)
	if err != nil {
		return asm.Memory{}, 0, 0, err
	}
	if idxType.wide() || idxType.signed || idxType.isBool || idxType.isFloat {
		return asm.Memory{}, 0, 0, unsupported("an element index of type %s (the array idiom walks by a u32 index)", idxType.name)
	}
	r, err := g.expr(index, &idxType)
	if err != nil {
		return asm.Memory{}, 0, 0, err
	}
	base, err := g.alloc(scalars["u64"])
	if err != nil {
		return asm.Memory{}, 0, 0, err
	}
	if arr.inReg {
		// An array field inside a computed element: its address is the
		// element's plus the field offset (the checker narrows the region).
		g.emit("add", xr(base), xr(arr.reg), imm(arr.offset))
	} else {
		g.emit("add", xr(base), sp(), imm(g.slotMem(arr.offset).Offset))
	}
	g.usedTrap = true
	g.emit("cmp", wr(r), imm(arr.length))
	g.branch("hs", g.trap)
	idx := wr(r)
	return asm.Memory{Base: xr(base), Index: &idx, Shift: log2Bytes(int(size)), Extend: "uxtw"}, r, base, nil
}

// arrayElement lowers a load from an owned array local.
func (g *generator) arrayElement(arr *arrayLocal, index ast.Expression) (int, error) {
	address, idx, base, err := g.arrayAddress(arr, index)
	if err != nil {
		return 0, err
	}
	out := idx
	if idx < 0 || arr.elem.isFloat {
		out, err = g.alloc(arr.elem)
		if err != nil {
			return 0, err
		}
	}
	g.emit(loadOf(arr.elem), reg(out, arr.elem), address)
	if base >= 0 {
		g.release(base)
	}
	if idx >= 0 && out != idx {
		g.release(idx)
	}
	g.releaseTemps(arr.temps)
	return out, nil
}

// storeToPlace stores into a resolved place: a scalar field at its width,
// a record (a nested field or an array element) by its exact size.
func (g *generator) storeToPlace(target place, s *ast.IndexAssignmentStatement) error {
	switch {
	case target.sc != nil:
		if target.sc.readOnly {
			return unsupported("a store into %s through a read-only view", s.Target.String())
		}
		value, err := g.expr(s.Value, &target.sc.typ)
		if err != nil {
			return err
		}
		g.fieldStore(target.sc, value)
		g.release(value)
		g.releaseTemps(target.sc.temps)
		return nil
	case target.rec != nil:
		if target.rec.readOnly {
			return unsupported("a store into %s through a read-only view", s.Target.String())
		}
		src, err := g.recordValueAs(s.Value, target.rec.layout)
		if err != nil {
			return err
		}
		if src.layout != target.rec.layout {
			return unsupported("a %s stored into %s (a %s)", src.layout.name, s.Target.String(), target.rec.layout.name)
		}
		err = g.copyBytes(target.rec.loc(), src.loc(), target.rec.layout.size)
		g.releaseTemps(src.temps)
		g.releaseTemps(target.rec.temps)
		return err
	}
	return unsupported("a store to the array %s", s.Target.String())
}

// element lowers `v[i]`: a guarded, whole-element load through the bound
// base, zero- or sign-extending as the element type reads in C.
func (g *generator) element(e *ast.IndexExpression) (int, error) {
	if e.Dot {
		sc, err := g.fieldOperand(e)
		if err != nil {
			return 0, err
		}
		r, err := g.fieldLoad(sc)
		if err != nil {
			return 0, err
		}
		g.releaseTemps(sc.temps)
		return r, nil
	}
	if arr := g.arrayOperand(e.Left); arr != nil {
		return g.arrayElement(arr, e.Index)
	}
	sp, err := g.spanOperand(e.Left)
	if err != nil {
		return 0, err
	}
	r, err := g.guardedIndex(sp, e.Index)
	if err != nil {
		return 0, err
	}
	index := wr(r)
	address := asm.Memory{Base: xr(sp.baseReg), Index: &index, Shift: log2Bytes(sp.elem.bits / 8), Extend: "uxtw"}
	if sp.elem.isFloat {
		f, err := g.alloc(sp.elem)
		if err != nil {
			return 0, err
		}
		g.emit("ldr", reg(f, sp.elem), address)
		g.release(r)
		return f, nil
	}
	var load string
	switch {
	case sp.elem.bits >= 32:
		load = "ldr"
	case sp.elem.bits == 16 && sp.elem.signed:
		load = "ldrsh"
	case sp.elem.bits == 16:
		load = "ldrh"
	case sp.elem.signed:
		load = "ldrsb"
	default:
		load = "ldrb"
	}
	// The element lands in the index register: the index is spent.
	g.emit(load, reg(r, sp.elem), address)
	return r, nil
}

// elementStore lowers `v[i] = e` through a writable span.
func (g *generator) elementStore(s *ast.IndexAssignmentStatement) error {
	if s.Target.Dot {
		target, err := g.placeOf(s.Target)
		if err != nil {
			return err
		}
		return g.storeToPlace(target, s)
	}
	if layout := g.recordArrayElementLayout(s.Target.Left); layout != nil {
		// `pool[i] = r`: a record element replaced.
		target, err := g.placeOf(s.Target)
		if err != nil {
			return err
		}
		return g.storeToPlace(target, s)
	}
	if arr := g.arrayOperand(s.Target.Left); arr != nil {
		value, err := g.expr(s.Value, &arr.elem)
		if err != nil {
			return err
		}
		address, idx, base, err := g.arrayAddress(arr, s.Target.Index)
		if err != nil {
			return err
		}
		g.emit(storeOf(arr.elem), reg(value, arr.elem), address)
		for _, r := range []int{value, idx, base} {
			if r >= 0 {
				g.release(r)
			}
		}
		g.releaseTemps(arr.temps)
		return nil
	}
	sp, err := g.spanOperand(s.Target.Left)
	if err != nil {
		return err
	}
	if !sp.writable {
		return unsupported("a store through the view %s", s.Target.Left.String())
	}
	value, err := g.expr(s.Value, &sp.elem)
	if err != nil {
		return err
	}
	r, err := g.guardedIndex(sp, s.Target.Index)
	if err != nil {
		return err
	}
	index := wr(r)
	address := asm.Memory{Base: xr(sp.baseReg), Index: &index, Shift: log2Bytes(sp.elem.bits / 8), Extend: "uxtw"}
	store := "str"
	switch sp.elem.bits {
	case 16:
		store = "strh"
	case 8:
		store = "strb"
	}
	g.emit(store, reg(value, sp.elem), address)
	g.release(r)
	g.release(value)
	return nil
}

// ---- results and tail calls ----------------------------------------------------

// resultExpr places an expression in result position: a tail self-call
// becomes the next iteration (the arguments into the parameter slots, then
// a jump to the header); a Bool conditional keeps its arms in result
// position; anything else evaluates into the result register.
func (g *generator) resultExpr(expr ast.Expression) error {
	switch e := expr.(type) {
	case *ast.InvocationExpression:
		if ident, ok := e.Function.(*ast.Identifier); ok && ident.Value == g.fn.Name.Value && len(g.spans) == 0 {
			return g.tailCall(e)
		}
	case *ast.MatchExpression:
		if _, _, isBool := boolConditional(e); !isBool {
			return g.lowerMatch(e, g.resultExpr)
		}
		if whenTrue, whenFalse, ok := boolConditional(e); ok {
			// With one arm a tail self-call, the loop shape the verifier
			// recognizes: the exit branch leaves for the value arm, the tail
			// arm falls through to the back edge.
			if g.isTailCall(whenFalse) != g.isTailCall(whenTrue) {
				tail, value, jumpIfFalse := whenTrue, whenFalse, true
				if g.isTailCall(whenFalse) {
					tail, value, jumpIfFalse = whenFalse, whenTrue, false
				}
				exit := g.newLabel("exit")
				if err := g.conditionBranch(e.Scrutinee, exit, jumpIfFalse); err != nil {
					return err
				}
				if err := g.resultExpr(tail); err != nil {
					return err
				}
				g.label(exit)
				return g.resultExpr(value)
			}
			elseLabel, end := g.newLabel("else"), g.newLabel("endif")
			if err := g.condition(e.Scrutinee, elseLabel); err != nil {
				return err
			}
			if err := g.resultExpr(whenTrue); err != nil {
				return err
			}
			g.emit("b", asm.Symbol{Name: end})
			g.label(elseLabel)
			if err := g.resultExpr(whenFalse); err != nil {
				return err
			}
			g.label(end)
			return nil
		}
	case *ast.BlockExpression:
		if e.Block != nil && len(e.Block.Statements) > 0 {
			g.pushScope()
			defer g.popScope()
			stmts := e.Block.Statements
			if err := g.lowerStatements(stmts[:len(stmts)-1], false, ""); err != nil {
				return err
			}
			if es, ok := stmts[len(stmts)-1].(*ast.ExpressionStatement); ok && !es.Discard {
				return g.resultExpr(es.Expression)
			}
		}
	}
	r, err := g.expr(expr, g.result)
	if err != nil {
		return err
	}
	g.moveResult(r, *g.result)
	g.release(r)
	return nil
}

// tailCall lowers a self-call in result position as a loop: every argument
// is evaluated before any parameter slot changes.
func (g *generator) tailCall(e *ast.InvocationExpression) error {
	if len(e.Arguments) != len(g.fn.Parameters) {
		return unsupported("a self-call with %d arguments", len(e.Arguments))
	}
	var values []int
	for i, arg := range e.Arguments {
		typ, _ := scalarOf(g.fn.Parameters[i].Type)
		r, err := g.expr(arg, &typ)
		if err != nil {
			return err
		}
		values = append(values, r)
	}
	for i, r := range values {
		g.items = append(g.items, g.storeVar(g.fn.Parameters[i].Name.Value, r))
		g.release(r)
	}
	g.emit("b", asm.Symbol{Name: g.head})
	return nil
}

// isTailCall recognizes a self-call the loop lowering handles.
func (g *generator) isTailCall(expr ast.Expression) bool {
	call, ok := expr.(*ast.InvocationExpression)
	if !ok || len(g.spans) != 0 {
		return false
	}
	ident, ok := call.Function.(*ast.Identifier)
	return ok && ident.Value == g.fn.Name.Value
}

// Describe spells a lowered function as `.oakasm` text (diagnostics, tests).
func Describe(fn *asm.Function) string {
	var b strings.Builder
	fmt.Fprintf(&b, "%s = {\n", fn.Name)
	for _, bind := range fn.Bindings {
		if bind.Length != nil {
			fmt.Fprintf(&b, "  bind %s, %s = %s\n", bind.Register.Text, bind.Length.Text, bind.Param)
			continue
		}
		fmt.Fprintf(&b, "  bind %s = %s\n", bind.Register.Text, bind.Param)
	}
	if len(fn.Clobbers) > 0 {
		names := make([]string, len(fn.Clobbers))
		for i, c := range fn.Clobbers {
			names[i] = c.Text
		}
		fmt.Fprintf(&b, "  clobber %s\n", strings.Join(names, ", "))
	}
	if fn.Frame > 0 {
		fmt.Fprintf(&b, "  frame %d\n", fn.Frame)
	}
	for _, item := range fn.Items {
		switch it := item.(type) {
		case asm.Label:
			fmt.Fprintf(&b, "%s:\n", it.Name)
		case asm.Instruction:
			fmt.Fprintf(&b, "  %s\n", it.String())
		}
	}
	b.WriteString("}\n")
	return b.String()
}
