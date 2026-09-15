// Package nativegen is the native backend for Oak bodies
// (docs/spec/94-assembler.md §9): it lowers a type-checked Oak function to
// an asm.Function — the same checked, verifiable, encodable object an
// `.oakasm` unit yields — so the compiler's own output is held to the seam
// checker's disciplines, proved against the Oak body by the verifier where
// the verifier reaches, and encoded by the Oak assembler into the companion
// object. The C backend stays the portable realization and the differential
// oracle. This file is the AArch64 lane (CompileFor with asm.ArchArm64, or
// Compile); rv64.go is the RV64 lane, the fixed-width integer subset under
// the LP64 psABI.
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
	"math/bits"
	"sort"
	"strconv"
	"strings"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/semir"
	"github.com/SCKelemen/oak/token"
	"github.com/SCKelemen/oak/typechecker"
)

// scalar is a fixed-width integer type of the subset.
type scalar struct {
	name    string
	bits    int
	signed  bool
	isBool  bool
	isFloat bool // f32/f64: held in the s/d view of a vector register
	// isVec marks the fixed 128-bit vectors (nativegen/simd.go): held whole
	// in a vector register, lanes of laneBits each.
	isVec    bool
	lanes    int
	laneBits int
	// laneFloat marks the floating-point vectors simd.F32x4/F64x2
	// (docs/spec/93-simd.md section 1.2a): lanes are f32/f64 values.
	laneFloat bool
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
	if v, isVec := vecTypeOf(expr); isVec {
		return v, true
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
	// atomic marks a span of cells (`[*]Atomic[T]`, docs/spec/65-machine-memory.md
	// section 1): its elements are reached only by the atomic builtins
	// (nativegen/atomics.go), never by a plain load or store.
	atomic bool
	// elemLayout: the element type when the span holds records (elem unused).
	elemLayout *recordLayout
	baseReg    int // x register holding the base
	lenReg     int // w register holding the length
	// argBase/argLen: the argument registers the pair arrived in. In a
	// function that calls, the pair is parked in callee-saved registers
	// (baseReg/lenReg) by the prologue — the checker follows the copies —
	// so the callee's clobber of x0–x17 never touches it.
	argBase, argLen int
	// frameLen: the constant length of a span bound over an owned frame
	// array (`span(&buf)` / `view(&buf)`), 0 for any other span. Its base
	// is a frame address to the checker, whose frame idioms (a frame array
	// access, the element region of a frame array of records) take a
	// constant index guard `cmp wI, #N` — the length register would leave
	// every element of the span unaddressable in the binding function.
	frameLen int64
	// norm: on the rv64 lane, the register holding the length zero-extended
	// (`slli n, aL, 32; srli n, n, 32`, the checker's normalization idiom):
	// the LP64 pair leaves padding above the u32 length, so every bounds
	// guard compares against this copy (nativegen/rv64.go).
	norm int
	// array: for a local view or span over an owned array of the frame
	// (`whole: []u32 = view(&buf)`), the array itself. Its elements are
	// reached through the array's own idiom — the frame address and the
	// constant guard — since the pair's base register carries a frame
	// address the checker forgets at the first call, not a span fact.
	array *arrayLocal
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
	if carrier, isCell := atomicCarrier(index.Left); isCell {
		return span{elem: carrier, writable: marker.Value == "*", atomic: true}, true
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
	// readOnly: an array field of a view's element: stores are refused.
	readOnly bool
	// paramRef: an in-place by-reference array parameter (recordParam.inPlace).
	paramRef bool
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

// reachable is memOf for a size-byte access whose offset from a register
// base may exceed the load/store immediate (4095 scaled units): a field
// past a large array inside a span element (the OS pilot's N2). The base
// is rebased through a fresh register by addOffset and the small remainder
// stays in the operand; temp is that register (or -1), released by the
// caller after the access. The checker narrows the element region through
// the adds (asm/check.go, deriveElement).
func (g *generator) reachable(l loc, size int64) (asm.Memory, int, error) {
	if !l.inReg || size <= 0 || (l.offset >= 0 && l.offset%size == 0 && l.offset/size <= 4095) {
		return g.memOf(l), -1, nil
	}
	temp, err := g.alloc(scalars["u64"])
	if err != nil {
		return asm.Memory{}, -1, err
	}
	high := l.offset &^ 0xfff
	if err := g.addOffset(temp, l.reg, high); err != nil {
		return asm.Memory{}, -1, err
	}
	return asm.Memory{Base: xr(temp), Offset: l.offset - high}, temp, nil
}

// addOffset emits `add xD, xS, #off` for any offset below 2^24: the low
// twelve bits as one add, the rest as `#imm, lsl #12`.
func (g *generator) addOffset(dst, src int, off int64) error {
	if off < 0 || off >= 1<<24 {
		return unsupported("an offset of %d bytes inside an element", off)
	}
	high, low := off>>12, off&0xfff
	current := src
	if high != 0 {
		g.emit("add", xr(dst), xr(current), asm.Immediate{Value: high, Shift: 12})
		current = dst
	}
	if low != 0 || current == src {
		g.emit("add", xr(dst), xr(current), imm(low))
	}
	return nil
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
	// atomic marks an Atomic[T] cell placed as its carrier T.
	atomic bool
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
	// inPlace: a by-reference parameter the body only reads, kept as the
	// caller's memory addressed by the callee-saved register park (the
	// checker's read-only region, copied there by `mov`), never copied into
	// the frame; a callee taking it by reference receives the same address.
	inPlace bool
	park    int
}

// isHFA reports a homogeneous floating-point aggregate (all fields one
// float type, at most four): AAPCS64 passes it in v registers, which v1
// leaves to the C backend.
func (l *recordLayout) isHFA() bool {
	if len(l.order) == 0 {
		return false
	}
	first := l.fields[l.order[0]].typ
	if !first.isFloat {
		return false
	}
	// An array field's elements are members in their own right (AAPCS64
	// §5.9.5.3 counts the fundamental data types of the composite), so
	// `[4]f32` is an HFA and `[8]f32` a 32-byte composite by reference.
	members := int64(0)
	for _, name := range l.order {
		field := l.fields[name]
		if field.kind == fieldRecord || field.typ != first {
			return false
		}
		members++
		if field.kind == fieldArray {
			members += field.length - 1
		}
	}
	return members <= 4
}

// arrayLayout is an owned array of scalars `[N]T` seen as a value: the
// one-field composite the C backend's wrapper struct is (a `T v[N]` member,
// so the AAPCS64 rules for records apply unchanged — chunks up to 16
// bytes, by reference beyond), docs/spec/94-assembler.md §9, forty-seventh
// increment. The layout is shared per (T, N), so layouts compare by
// identity as record layouts do; its name is the type's spelling.
func (g *generator) arrayLayout(elem scalar, length int64) *recordLayout {
	key := fmt.Sprintf("(%s[%d])", elem.name, length)
	if layout, done := g.layouts[key]; done {
		return layout
	}
	rep := fieldRepresentations[elem.name]
	size := int64(rep.Size) * length
	layout := &recordLayout{name: key, size: size, align: int64(rep.Alignment), hasFloat: elem.isFloat, fields: map[string]recordField{"": {kind: fieldArray, typ: elem, length: length, size: size}}, order: []string{""}}
	g.layouts[key] = layout
	return layout
}

// arrayLayoutOf is arrayLayout for a written array type of placeable
// scalars (vectors and Bool stay outside: their arrays never cross the
// boundary as values).
func (g *generator) arrayLayoutOf(expr ast.Expression) (*recordLayout, bool) {
	elem, length, ok := arrayOf(expr)
	if !ok {
		return nil, false
	}
	if _, placeable := fieldRepresentations[elem.name]; !placeable {
		return nil, false
	}
	return g.arrayLayout(elem, length), true
}

// valueLayoutOf is the layout of a type that travels as a composite value:
// a declared record or union (layoutOf), or an owned array of scalars.
func (g *generator) valueLayoutOf(typ ast.Expression) (layout *recordLayout, isValue bool, err error) {
	if name, isRecord := g.recordTypeName(typ); isRecord {
		layout, err = g.layoutOf(name)
		return layout, true, err
	}
	if layout, isArray := g.arrayLayoutOf(typ); isArray {
		return layout, true, nil
	}
	return nil, false, nil
}

// arrayElem is the element type and count of an array layout.
func (l *recordLayout) arrayElem() (scalar, int64, bool) {
	field, isArray := l.fields[""]
	if !isArray || len(l.order) != 1 || field.kind != fieldArray {
		return scalar{}, 0, false
	}
	return field.typ, field.length, true
}

// isArray reports an array layout.
func (l *recordLayout) isArray() bool {
	_, _, isArray := l.arrayElem()
	return isArray
}

// arrayAsRecord views an owned array of scalars as the record value its
// layout describes: the same storage, the same temps.
func (g *generator) arrayAsRecord(arr *arrayLocal) (*recordLocal, bool) {
	if arr.elemLayout != nil {
		return nil, false
	}
	if _, placeable := fieldRepresentations[arr.elem.name]; !placeable {
		return nil, false
	}
	return &recordLocal{offset: arr.offset, layout: g.arrayLayout(arr.elem, arr.length), inReg: arr.inReg, reg: arr.reg, temps: arr.temps, readOnly: arr.readOnly, paramRef: arr.paramRef}, true
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
			out[name] = layout.composite()
		}
	}
	for name := range adts {
		if layout, err := g.layoutOf(name); err == nil {
			out[name] = layout.composite()
		}
	}
	return out
}

// composite is the layout as the checker and verifier see it.
func (l *recordLayout) composite() asm.Composite {
	out := asm.Composite{Size: l.size, HFA: l.isHFA()}
	for _, name := range l.order {
		field := l.fields[name]
		placed := asm.CompositeField{Name: name, Offset: field.offset, Size: field.size}
		switch field.kind {
		case fieldScalar:
			placed.Scalar = field.typ.name
		case fieldRecord:
			placed.Type = field.layout.name
		default:
			placed.Length = field.length
			if field.layout != nil {
				placed.ElemType = field.layout.name
			} else {
				placed.Elem = field.typ.name
			}
		}
		out.Fields = append(out.Fields, placed)
	}
	if l.variants != nil {
		out.Variants = map[string]int64{}
		for name, v := range l.variants {
			out.Variants[name] = v.tag
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
	// paramRef: an in-place by-reference parameter (recordParam.inPlace):
	// the caller's memory, passed on by its address.
	paramRef bool
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
		case func() bool { _, ok := atomicCarrier(field.Value); return ok }():
			// An atomic cell is placed as its carrier (docs/spec/65-machine-memory.md
			// section 1); only the atomic builtins reach it.
			typ, _ := atomicCarrier(field.Value)
			rep = fieldRepresentations[typ.name]
			placed = recordField{kind: fieldScalar, typ: typ, atomic: true}
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
		if gl, isTable := g.tables[e.Value]; isTable {
			// A constant table: its address in a scratch register (adrl),
			// a read-only array at offset 0 from it.
			r, err := g.alloc(scalars["u64"])
			if err != nil {
				return place{}, err
			}
			g.emit("adrl", xr(r), asm.Symbol{Name: gl.Symbol})
			return place{arr: &arrayLocal{elem: scalars[gl.Elem], length: gl.Length, inReg: true, reg: r, temps: []int{r}, readOnly: true}}, nil
		}
		if decl, isAggregate := g.aggregates[e.Value]; isAggregate && !g.shadowed(e.Value) {
			return g.globalAggregatePlace(e.Value, decl)
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
			return place{arr: &arrayLocal{offset: at.offset, elem: field.typ, elemLayout: field.layout, length: field.length, inReg: at.inReg, reg: at.reg, temps: base.rec.temps, readOnly: base.rec.readOnly}}, nil
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
	r, err := g.indexValue(index)
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
	if arr.inReg {
		// An array of records inside a register-based place (a global
		// aggregate, a span element): its base is the place's register
		// plus the field offset; the checker narrows the region through
		// the add and derives the element region under the guard.
		if err := g.addOffset(base, arr.reg, arr.offset); err != nil {
			return place{}, err
		}
	} else {
		g.emit("add", xr(base), sp(), imm(g.slotMem(arr.offset).Offset))
	}
	if err := g.constantGuard(r, arr.length); err != nil {
		return place{}, err
	}
	if stride > 0 && stride&(stride-1) == 0 && stride <= 16 {
		g.emit("add", xr(element), xr(base), asm.Extended{Reg: wr(r), Kind: "uxtw", Amount: int64(log2Bytes(int(stride)))})
	} else {
		if stride >= 1<<32 {
			return place{}, unsupported("a record stride of %d bytes", stride)
		}
		// The stride as a 32-bit constant — movz, and movk for the high
		// halfword of a large record (the OS pilot's N2: a 409 600-byte
		// regime) — then one umaddl.
		strideReg, err := g.alloc(scalars["u32"])
		if err != nil {
			return place{}, err
		}
		g.constant(strideReg, uint64(stride), scalars["u32"])
		g.emit("umaddl", xr(element), wr(r), wr(strideReg), xr(base))
		g.release(strideReg)
	}
	g.release(base)
	g.release(r)
	if arr.inReg {
		g.releaseTemps(arr.temps)
	}
	return place{rec: &recordLocal{layout: arr.elemLayout, inReg: true, reg: element, temps: []int{element}, readOnly: arr.readOnly}}, nil
}

// globalAggregatePlace is a top-level record or array at its symbol's
// address (adrp/add, docs/spec/94-assembler.md §9): a record place, or an
// array place, in a fresh register — fields and guarded elements through
// it as through a span element's.
func (g *generator) globalAggregatePlace(name string, decl *ast.VariableDeclaration) (place, error) {
	if typeName, isRecord := g.recordTypeName(decl.Type); isRecord {
		layout, err := g.layoutOf(typeName)
		if err != nil {
			return place{}, err
		}
		global := asm.Global{Type: typeName, Aggregate: true, Size: layout.size}
		addr, err := g.globalAddress(name, global)
		if err != nil {
			return place{}, err
		}
		return place{rec: &recordLocal{layout: layout, inReg: true, reg: addr, temps: []int{addr}}}, nil
	}
	elem, elemLayout, length, err := g.arrayTypeOf(decl.Type)
	if err != nil {
		return place{}, err
	}
	size := length * int64(elem.bits/8)
	if elemLayout != nil {
		size = length * elemLayout.size
	}
	global := asm.Global{Type: decl.Type.String(), Aggregate: true, Size: size}
	addr, err := g.globalAddress(name, global)
	if err != nil {
		return place{}, err
	}
	return place{arr: &arrayLocal{elem: elem, elemLayout: elemLayout, length: length, inReg: true, reg: addr, temps: []int{addr}}}, nil
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
		if decl, isAggregate := g.aggregates[e.Value]; isAggregate && !g.shadowed(e.Value) {
			if typeName, isRecord := g.recordTypeName(decl.Type); isRecord {
				return g.layoutOf(typeName)
			}
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
		if stride >= 1<<32 {
			return place{}, unsupported("a record stride of %d bytes", stride)
		}
		strideReg, err := g.alloc(scalars["u32"])
		if err != nil {
			return place{}, err
		}
		g.constant(strideReg, uint64(stride), scalars["u32"])
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
		if decl, isAggregate := g.aggregates[e.Value]; isAggregate && !g.shadowed(e.Value) {
			if _, elemLayout, _, err := g.arrayTypeOf(decl.Type); err == nil {
				return elemLayout
			}
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

// recordTypeName reads a type expression naming a declared record or
// tagged union: a name, or an instantiation (Option[u32]) by its mangled
// name, which the compiler specialized into a monomorphic declaration.
func (g *generator) recordTypeName(expr ast.Expression) (string, bool) {
	name, ok := asm.TypeApplicationName(expr)
	if !ok {
		return "", false
	}
	if _, isRecord := g.recordDecls[name]; isRecord {
		return name, true
	}
	_, isADT := g.adtDecls[name]
	return name, isADT
}

// Unsupported reports why a function is left to the C backend.
type Unsupported struct{ Reason string }

func (u Unsupported) Error() string { return u.Reason }

func unsupported(format string, args ...interface{}) Unsupported {
	return Unsupported{fmt.Sprintf(format, args...)}
}

// generator holds one function's lowering.
type generator struct {
	// rvLane marks the rv64 lane's embedding: the AArch64-only lowerings
	// (the atomics) leave the function to the C backend there.
	rvLane bool
	fn     *ast.FunctionStatement
	// scalarArrays: the array locals lowered as their elements
	// (nativegen/scalar_arrays.go).
	scalarArrays map[string]*scalarArray
	// fusedWords counts the word assemblies lowered as one load
	// (nativegen/word_fusion.go).
	fusedWords int
	tc         *typechecker.TypeChecker
	functions  map[string]*ast.FunctionStatement
	result     *scalar

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
	// Registers and slots of variables whose scope has closed, reused by
	// later declarations (an inlined block's locals die with the block):
	// callee-saved general registers, callee-saved vector registers (as
	// vecBase+n), eight-byte slots, sixteen-byte slots.
	freeCallee  []int
	freeCalleeV []int
	freeSlots8  []int64
	freeSlots16 []int64
	saveArea    int64 // bytes reserved for the callee-saved pairs (fixed once any variable exists)
	// The vector file for floating point: scratch and callee-saved pools,
	// and the d8–d15 save area (fixed once the function mentions a float).
	freeF       []int
	freeV       []int // the rv64 lane's vector scratch registers (rvVBase + n)
	usedVector  bool  // the rv64 lane used the vector extension
	usedCalleeV int
	saveAreaV   int64
	usedFloat   bool
	scopes      []map[string]slotBinding
	nslots      int64
	spill       map[int]int64 // scratch register → its spill slot offset
	free        []int         // free scratch registers
	ipScratch   int           // x16/x17 taken as overflow scratch (overflowScratch)
	// In a leaf (no call) the argument registers are homes: a scalar
	// parameter stays where it arrived, and the argument registers no
	// parameter occupies hold locals before any callee-saved register is
	// taken (leafHomes, in order; argHomes names each parameter's). Nothing
	// need be saved for them, and the prologue moves nothing.
	leafHomes []int
	argHomes  map[string]int
	homesUsed map[int]bool // every argument register handed out as a home
	// loopHomes: per loop header label, the registers of the variables in
	// scope when the loop began — the loop-invariant pass never moves or
	// removes a write into one (the value is the variable's, read where
	// the block cannot see: after the loop, at the header, in another arm).
	loopHomes map[string]map[int]bool
	// openLoops: the header labels of the loops being lowered, innermost
	// last — a home handed out inside a loop's body joins the loop's set
	// (a span declared in an arm of the body has no reader the pass can
	// see once its guards are elided, yet its length register carries
	// the checker's facts).
	openLoops []string
	// callerHomes: in a function that calls, the caller-saved registers a
	// variable may live in once the callee-saved ones are taken — x16, x17
	// and the argument registers no parameter occupies — each saved before
	// a call and restored after it (callerSpill), one store and one load per
	// call instead of one memory access per read or write from a frame slot.
	callerHomes []int
	peakScratch int // the most integer scratch registers live at once
	// Arguments beyond the register contract (asm/abi.go): packedStack the
	// convention, stackParams each such parameter's place (entry-relative
	// offset), stackArgs the incoming area's size, outgoing the bytes this
	// function's own calls need below its saved registers.
	packedStack bool
	stackParams map[string]asm.ArgPlace
	stackArgs   int64
	outgoing    int64
	pressure    bool // a scalar variable took a caller-saved home or a slot
	// lv: the liveness pre-pass (liveness.go) deciding which homes a call
	// saves and which variables cross a call; nil on the rv64 lane.
	lv   *callLiveness
	live []int // allocated scratch registers, allocation order
	// defined marks the live scratch registers an emitted instruction has
	// written: a call spills exactly those (a register allocated for an
	// enclosing expression's result and not yet written holds nothing, and
	// the checker refuses a spill that reads it).
	defined map[int]bool
	// tables are the program's constant tables (Lane.Tables), read
	// through their data symbols' addresses.
	tables map[string]GlobalArray
	// constants are the program's folded constant globals
	// (asm.Function.Constants): an identifier naming one, not shadowed by
	// a local, materializes as an immediate at its declared type.
	constants map[string]asm.Constant
	// globals are the program's addressable top-level scalars (Lane.Globals);
	// usedGlobals the ones this body addressed (asm.Function.Globals).
	globals     map[string]asm.Global
	usedGlobals map[string]asm.Global
	// aggregates are the program's addressable top-level records and
	// arrays (Lane.Aggregates), placed at their symbol's address.
	aggregates map[string]*ast.VariableDeclaration
	labels     int
	loops      []string // break targets
	hasCalls   bool
	line       int
	trap       string // the trap block's label (division by zero, shift overflow, assert)
	usedTrap   bool
	// loopFacts: what the enclosing while conditions prove about a span
	// and an index variable inside their bodies (nativegen/simd.go
	// vecGuardedIndex): `len(v) >= N && i <= len(v) - N` proves
	// i + N <= len(v) until i is assigned.
	loopFacts []loopFact
	// terminated: an unconditional jump was emitted and no label has
	// followed — instructions there are unreachable and are not emitted (the
	// checker refuses them).
	terminated bool
	// system: the body uses an instruction function that needs the
	// checker's system capability (mrs/msr, eret, the DAIF writes);
	// never: the function's result type is never (it leaves by eret).
	system bool
	never  bool
	// elide: an element access the typechecker proved in range
	// (IndexProven) is lowered without its guard, leaving the checker to
	// admit it from the facts already on the path (the loop's own exit
	// test) or to refuse — on refusal the compiler lowers again with
	// guards (compiler/native_bodies.go). Safety stays the checker's.
	elide bool
	// guardLines: accesses on these source lines keep their guards even
	// when proven (Lane.GuardLines, the compiler's per-line fallback).
	guardLines map[int]bool
	// reuseFlags (Lane.ReuseFlags): flagsTo records, per label, the compare
	// whose conditional branch reaches it — its operands' spelling — or ""
	// once another kind of transfer does; liveFlags is that compare while
	// nothing has been emitted since the label; reused counts the
	// compares left out.
	reuseFlags bool
	flagsTo    map[string]string
	liveFlags  string
	reused     int
	// licmReserve: callee-saved registers held for the loop-invariant pass,
	// handed back to declarations that would otherwise refuse the body
	// (reclaimReserve).
	licmReserve []int
	// selected: conditional chains lowered as compare-and-select (nativegen/select.go).
	selected int
	// elided counts the guards left out under elide (reported).
	elided int
	// strength lowers constant multiplications, divisions, and remainders
	// to shifts, masks, and untested divisions (Lane.Strength); reduced
	// counts them (reported, and the compiler's cue to fall back).
	strength bool
	reduced  int
	// vectorHomes (Lane.VectorHomes): callerHomesV is the pool of vector
	// registers a calling function hands its vector locals, homesUsedV the
	// ones handed out, vecHomes their count (reported).
	vectorHomes  bool
	vecPoolBuilt bool
	callerHomesV []int
	homesUsedV   map[int]bool
	vecHomes     int
	// leafHomesV (Lane.VectorHomes, leaves): the vector argument registers
	// no parameter occupies, v1–v7, as homes for a leaf's vector locals
	// once the callee-saved and scratch homes are taken; leafVecHomes
	// counts them (reported).
	leafHomesV    []int
	leafPoolBuilt bool
	leafVecHomes  int
}

type slotBinding struct {
	offset int64
	typ    scalar
	reg    int          // callee-saved register, or -1 for a slot
	arr    *arrayLocal  // an owned array local (offset/typ/reg unused)
	rec    *recordLocal // an owned record local (offset/typ/reg unused)
	sp     *span        // a local span or view, register-resident
	freed  bool         // register or slot already returned after the last use
	// sa: a scalar-replaced array (nativegen/scalar_arrays.go).
	sa *scalarArray
}

const scratchLow, scratchHigh = 9, 15
const calleeLow, calleeHigh = 19, 28

// The vector file: v16–v23 scratch (caller-saved), v8–v15 for float
// variables (callee-saved: their d views are saved and restored).
const vecScratchLow, vecScratchHigh = 16, 31

// vecTempReserve is how many caller-saved vector registers stay scratch
// when a function without calls takes the rest for its vector locals.
const vecTempReserve = 4
const vecCalleeLow, vecCalleeHigh = 8, 15

// Lane names the assembler lane a body is lowered on and the target facts
// the lowering depends on beyond the architecture.
type Lane struct {
	// NoReductions leaves the plain integer reductions as written
	// (nativegen/reduction.go): the compiler's second lowering when the
	// unrolled form did not prove.
	NoReductions bool
	// HoistInvariants runs the loop-invariant code motion pass
	// (nativegen/licm.go) on the AArch64 lane; the compiler clears it and
	// lowers again when the checker refuses the hoisted form.
	HoistInvariants bool
	// Arch is asm.ArchArm64 (the default) or asm.ArchRV64.
	Arch string
	// SoftFloat marks a RISC-V target without the F/D calling convention
	// (freestanding/riscv64 compiles soft-float, lp64): a body touching
	// floating point stays with the C backend there, as an F/D unit is
	// refused (docs/spec/94-assembler.md §9).
	SoftFloat bool
	// ElideProven lowers element accesses the typechecker proved in range
	// without their guards on the AArch64 lane; the checker admits or
	// refuses the body, and the compiler falls back to guards on refusal.
	ElideProven bool
	// ReuseFlags lets a conditional chain's else arm reuse the compare its
	// guard already made — `k == t ? … | k < t ? …` compares once — where
	// the else label's only predecessor is that compare's branch; the
	// checker admits flags across the label or the compiler lowers the
	// body again without the reuse (docs/spec/94-assembler.md §9
	// "Condition selection").
	ReuseFlags bool
	// GuardLines names source lines whose element accesses keep their
	// guards under ElideProven: the compiler adds the line of an access
	// the checker could not admit and lowers again, so the accesses the
	// checker does admit stay elided (compiler/native_bodies.go).
	GuardLines map[int]bool
	// Strength lowers a multiplication, division, or remainder by a
	// constant to the cheaper instruction on the AArch64 lane — a power
	// of two as a shift or a mask, a nonzero divisor without its zero
	// test (docs/spec/90-backend.md §16, docs/spec/94-assembler.md §9).
	// The verifier proves the body or the compiler lowers it again
	// without the reduction.
	Strength bool
	// VectorHomes keeps the vector locals of a function that calls in the
	// caller-saved vector registers v16–v31, saved around a call only when
	// live after it, instead of sixteen-byte frame slots reloaded at every
	// use (docs/spec/94-assembler.md §9.ad); the checker and the verifier
	// decide, and the compiler falls back to slots on refusal.
	VectorHomes bool
	// Globals are the program's mutable top-level scalars a body may
	// address (docs/spec/94-assembler.md §9, the OS pilot's N3), by Oak
	// name with their storage width; the generator records the ones a body
	// uses in asm.Function.Globals. Nil leaves every global unsupported.
	Globals map[string]asm.Global
	// Aggregates are the program's mutable top-level records and arrays
	// (the OS pilot's N9): addressed as a record or array place at the
	// symbol's address, fields and guarded elements through it.
	Aggregates map[string]*ast.VariableDeclaration
	// Tables are the program's constant tables by Oak name (GlobalArrayOf):
	// a body reads one through its data symbol's address.
	Tables map[string]GlobalArray
	// Vector marks a RISC-V processor with the vector extension (`-cpu
	// ...+v`): the rv64 lane lowers the fixed simd vectors there
	// (nativegen/rv64_simd.go) and leaves them to the C backend otherwise.
	Vector bool
	// PackedStackArgs selects Apple's arm64 convention for arguments beyond
	// the registers (natural size and alignment on the stack) over the
	// standard 8-byte slots (asm/abi.go).
	PackedStackArgs bool
}

// GlobalStorage is the addressed storage of a top-level scalar of the
// named type: its C storage width (a Bool is the C backend's 4-byte
// `Bool`), or false for a type the native subset does not address.
func GlobalStorage(typeName string) (asm.Global, bool) {
	typ, ok := scalars[typeName]
	if !ok || typ.isVec {
		return asm.Global{}, false
	}
	return asm.Global{Type: typ.name, Bits: globalStorageBits(typ)}, true
}

func globalStorageBits(typ scalar) int {
	if typ.isBool {
		return 32
	}
	return typ.bits
}

// GlobalArray is a constant top-level array the program reads — a table:
// its data symbol in the object (asm.DataSymbol), its element type by
// name, and its length. A body addresses it with `adrl` (AArch64) or `la`
// (RV64) and reads guarded elements through the address, read-only
// (docs/spec/94-assembler.md §9, constant tables).
type GlobalArray struct {
	Symbol string
	Elem   string
	Length int64
}

// ElemSize is the width of one element in bytes (the table's alignment).
func (gl GlobalArray) ElemSize() int64 {
	if elem, ok := scalars[gl.Elem]; ok {
		return int64(elem.bits / 8)
	}
	return 1
}

// GlobalArrayOf reads a top-level declaration as a constant table: an
// owned array `[N]T` of fixed-width integers with a literal initializer
// (every element a literal or a conversion of one; none for all zeros),
// returning the table and its little-endian bytes. The symbol is
// `data_<name>` before the backend's C symbol prefix (the object names it
// as it names the functions). Anything else — a
// float element, a computed element, a partial literal — is not one, and
// stays with the C backend. Whether the program writes the array is the
// caller's question (the compiler refuses a mutated table).
func GlobalArrayOf(decl *ast.VariableDeclaration) (GlobalArray, []byte, bool) {
	if decl == nil || decl.Name == nil || decl.Type == nil {
		return GlobalArray{}, nil, false
	}
	elem, length, isArray := arrayOf(decl.Type)
	if !isArray || elem.isFloat || elem.isVec || elem.bits < 8 || elem.bits > 64 {
		return GlobalArray{}, nil, false
	}
	width := int64(elem.bits / 8)
	bytes := make([]byte, length*width)
	if decl.Value != nil {
		literal, isLiteral := decl.Value.(*ast.ArrayLiteral)
		if !isLiteral {
			return GlobalArray{}, nil, false
		}
		if len(literal.Elements) != 0 && int64(len(literal.Elements)) != length {
			return GlobalArray{}, nil, false
		}
		for i, element := range literal.Elements {
			operand, negative := element, false
			if prefix, isPrefix := element.(*ast.PrefixExpression); isPrefix && prefix.Operator == "-" {
				operand, negative = prefix.Right, true
			}
			value, isConst := constantValue(operand)
			if !isConst {
				return GlobalArray{}, nil, false
			}
			if negative {
				if !elem.signed {
					return GlobalArray{}, nil, false
				}
				value = -value
			}
			bits := uint64(value)
			for b := int64(0); b < width; b++ {
				bytes[int64(i)*width+b] = byte(bits >> (8 * uint(b)))
			}
		}
	}
	return GlobalArray{Symbol: "data_" + decl.Name.Value, Elem: elem.name, Length: length}, bytes, true
}

// tableSizes is the checkers' and the verifier's table of the data
// symbols a body may address: each with its size, element width, and
// signedness.
func tableSizes(tables map[string]GlobalArray) map[string]asm.Table {
	out := map[string]asm.Table{}
	for _, gl := range tables {
		if elem, ok := scalars[gl.Elem]; ok {
			out[gl.Symbol] = asm.Table{Size: gl.Length * int64(elem.bits/8), Elem: int64(elem.bits / 8), Signed: elem.signed}
		}
	}
	return out
}

// CompileFor lowers one Oak function on a lane (docs/spec/94-assembler.md
// §9). A lane without a native backend leaves the function to the C
// backend with the reason.
func CompileFor(lane Lane, fn *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, records map[string]*ast.RecordLiteral, adts map[string]*ast.ADTType, constants map[string]asm.Constant, tc *typechecker.TypeChecker) (*asm.Function, error) {
	switch lane.Arch {
	case "", asm.ArchArm64:
		return compileArm64(fn, functions, records, adts, constants, lane.Globals, lane.Aggregates, tc, lane.ElideProven, lane.GuardLines, lane.Strength, lane.VectorHomes, lane.ReuseFlags, lane.Tables, lane.PackedStackArgs, !lane.NoReductions, lane.HoistInvariants)
	case asm.ArchRV64:
		return compileRV64(fn, functions, records, adts, constants, tc, lane.SoftFloat, lane.Tables, lane.Globals, lane.Vector, !lane.NoReductions, lane.ElideProven, lane.GuardLines)
	}
	return nil, unsupported("no native backend for the %s lane", lane.Arch)
}

// Compile lowers one Oak function on the AArch64 lane. functions maps every
// program function by name (callees' signatures), records every declared
// record type by name (their field lists), constants the program's folded
// constant globals (docs/spec/90-backend.md §8a); tc is the checker that
// typed the program.
func Compile(fn *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, records map[string]*ast.RecordLiteral, adts map[string]*ast.ADTType, constants map[string]asm.Constant, tc *typechecker.TypeChecker) (*asm.Function, error) {
	return compileArm64(fn, functions, records, adts, constants, nil, nil, tc, false, nil, false, false, false, nil, false, true, false)
}

// ElidedGuards reports how many element guards a lowering left out under
// Lane.ElideProven (for the compiler's diagnostics).
func ElidedGuards(fn *asm.Function) int { return elidedGuards[fn] }

var elidedGuards = map[*asm.Function]int{}

// Reduced reports how many constant multiplications, divisions, and
// remainders a lowering strength-reduced under Lane.Strength.
func Reduced(fn *asm.Function) int { return reducedOps[fn] }

// ReusedCompares reports how many compares a lowering left out under
// Lane.ReuseFlags (an else arm reading its guard's flags).
func ReusedCompares(fn *asm.Function) int { return reusedCompares[fn] }

var reusedCompares = map[*asm.Function]int{}

// Hoisted reports how many loops the loop-invariant pass changed under
// Lane.HoistInvariants (the compiler's fallback lowers again without it
// when the checker refuses the hoisted form).
func Hoisted(fn *asm.Function) int { return hoistedLoops[fn] }

var hoistedLoops = map[*asm.Function]int{}

var reducedOps = map[*asm.Function]int{}

// VectorHomes reports how many vector locals a lowering kept in registers
// across calls under Lane.VectorHomes.
func VectorHomes(fn *asm.Function) int { return vectorHomesOf[fn] }

var vectorHomesOf = map[*asm.Function]int{}

// LeafVectorHomes reports how many vector locals of a leaf a lowering
// homed in the argument registers v1–v7 under Lane.VectorHomes.
func LeafVectorHomes(fn *asm.Function) int { return leafVectorHomesOf[fn] }

var leafVectorHomesOf = map[*asm.Function]int{}

// pressured marks a lowering in which some scalar variable had to take a
// caller-saved home or a frame slot: the second pass is worth its cost.
var pressured = map[*asm.Function]bool{}

func compileArm64(fn *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, records map[string]*ast.RecordLiteral, adts map[string]*ast.ADTType, constants map[string]asm.Constant, globals map[string]asm.Global, aggregates map[string]*ast.VariableDeclaration, tc *typechecker.TypeChecker, elide bool, guardLines map[int]bool, strength bool, vhomes bool, reuse bool, tables map[string]GlobalArray, packed bool, unroll bool, hoist bool) (*asm.Function, error) {
	if fn.Body == nil || fn.ExternSymbol != "" || fn.Receiver != nil || len(fn.TypeParams) > 0 || fn.AsmBacked {
		return nil, unsupported("not an ordinary function body")
	}
	// The vector helpers the body calls are expanded first (nativegen/inline.go);
	// the lowering sees the expanded body, the verifier the original. An
	// expansion the lowering refuses falls back to the body as written.
	// The plain integer reductions are then unrolled (nativegen/reduction.go);
	// the verifier sees that rewritten body (asm.Function.Body), the rewrite
	// being its own theorem. A lowering the rewrite makes unsupported falls
	// back to the body before it.
	inlined := inlineBody(fn, functions)
	// Single-use span locals fold into the call that uses them
	// (nativegen/span_forward.go): the body needs no callee-saved pair for
	// them. A lowering the rewrite makes unsupported falls back to the
	// body before it.
	if forwarded, changed := forwardSingleUseSpans(cloneNode(inlined).(ast.Expression)); changed {
		expanded := *fn
		expanded.Body = forwarded
		if out, err := compileArm64Body(&expanded, functions, records, adts, constants, globals, aggregates, tc, elide, guardLines, strength, vhomes, reuse, tables, packed, hoist); err == nil {
			return out, nil
		} else if _, outside := err.(Unsupported); !outside {
			return nil, err
		}
	}
	if unrolled, changed := unrollReductions(fn, inlined); changed && unroll {
		expanded := *fn
		expanded.Body = unrolled
		if out, err := compileArm64Body(&expanded, functions, records, adts, constants, globals, aggregates, tc, elide, guardLines, strength, vhomes, reuse, tables, packed, hoist); err == nil {
			out.Body = unrolled
			return out, nil
		} else if _, outside := err.(Unsupported); !outside {
			return nil, err
		}
	}
	if inlined != fn.Body {
		expanded := *fn
		expanded.Body = inlined
		if out, err := compileArm64Body(&expanded, functions, records, adts, constants, globals, aggregates, tc, elide, guardLines, strength, vhomes, reuse, tables, packed, hoist); err == nil {
			return out, nil
		} else if _, outside := err.(Unsupported); !outside {
			return nil, err
		}
	}
	return compileArm64Body(fn, functions, records, adts, constants, globals, aggregates, tc, elide, guardLines, strength, vhomes, reuse, tables, packed, hoist)
}

// compileArm64Body lowers one function body as given — twice: the first
// pass measures the most scratch registers any expression of the body
// holds at once, the second hands the scratch registers that pass never
// reached (from x15 down) to the variables as caller-saved homes, so a
// body whose expressions need three temporaries keeps four more variables
// in registers instead of frame slots. A second pass the lowering refuses
// (it should not: a variable in a register needs no temporary a slot did)
// leaves the first pass's code.
func compileArm64Body(fn *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, records map[string]*ast.RecordLiteral, adts map[string]*ast.ADTType, constants map[string]asm.Constant, globals map[string]asm.Global, aggregates map[string]*ast.VariableDeclaration, tc *typechecker.TypeChecker, elide bool, guardLines map[int]bool, strength bool, vhomes bool, reuse bool, tables map[string]GlobalArray, packed bool, hoist bool) (*asm.Function, error) {
	first, peak, wanted, err := compileArm64Pass(fn, functions, records, adts, constants, globals, aggregates, tc, elide, guardLines, strength, vhomes, reuse, tables, packed, hoist, 0, 0)
	if err != nil {
		return nil, err
	}
	spare := scratchHigh - scratchLow + 1 - peak
	if spare <= 0 || !pressured[first] {
		spare = 0 // nothing to gain: every variable already has a register
	}
	// The loop-invariant pass reports the values it could not hoist for
	// want of a register (nativegen/licm.go): a second lowering reserves
	// that many callee-saved registers for them, four at most.
	reserve := min(wanted, 4)
	if spare == 0 && reserve == 0 {
		return first, nil
	}
	second, _, _, err := compileArm64Pass(fn, functions, records, adts, constants, globals, aggregates, tc, elide, guardLines, strength, vhomes, reuse, tables, packed, hoist, spare, reserve)
	if err != nil {
		return first, nil
	}
	return second, nil
}

// compileArm64Pass is one lowering of a body; spare is how many scratch
// registers, from x15 down, serve as variable homes instead of
// temporaries. It reports the peak number of integer scratch registers
// live at once.
func compileArm64Pass(fn *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, records map[string]*ast.RecordLiteral, adts map[string]*ast.ADTType, constants map[string]asm.Constant, globals map[string]asm.Global, aggregates map[string]*ast.VariableDeclaration, tc *typechecker.TypeChecker, elide bool, guardLines map[int]bool, strength bool, vhomes bool, reuse bool, tables map[string]GlobalArray, packed bool, hoist bool, spare int, reserve int) (*asm.Function, int, int, error) {
	g := &generator{fn: fn, tc: tc, functions: functions, slots: map[string]int64{}, types: map[string]scalar{}, spans: map[string]span{}, arrays: map[string]*arrayLocal{}, recordDecls: records, adtDecls: adts, layouts: map[string]*recordLayout{}, records: map[string]*recordLocal{}, recordParams: map[string]*recordParam{}, regs: map[string]int{}, spill: map[int]int64{}, defined: map[int]bool{}, constants: constants, globals: globals, aggregates: aggregates, usedGlobals: map[string]asm.Global{}, tables: tables, line: fn.Token.Line, elide: elide, guardLines: guardLines, strength: strength, vectorHomes: vhomes, homesUsedV: map[int]bool{}, reuseFlags: reuse, flagsTo: map[string]string{}, packedStack: packed, stackParams: map[string]asm.ArgPlace{}}
	// A span pair parked in callee-saved registers survives a call, and a
	// result: the result leaves in x0 (and x1), where a span parameter's
	// pair is bound, and the checker's span facts flow in text order — a
	// result placed in one arm would end the span before a later arm
	// walks it.
	g.hasCalls = mentionsCall(fn.Body)
	g.argHomes = map[string]int{}
	g.homesUsed = map[int]bool{}
	g.loopHomes = map[string]map[int]bool{}
	if g.hasCalls {
		g.outgoing = g.outgoingArea(fn.Body)
	}
	if g.hasCalls {
		g.lv = analyzeLiveness(fn)
	}
	parkSpans := g.hasCalls || returnsValue(fn)
	if hasVariables(fn) || parkSpans {
		g.saveArea = 8 * (calleeHigh - calleeLow + 1)
	}
	for r := scratchHigh; r >= scratchLow; r-- {
		g.free = append(g.free, r)
	}
	// The spare scratch registers (the first pass never held that many
	// temporaries at once) become variable homes: caller-saved, so saved
	// around calls like the other homes.
	var scratchHomes []int
	for i := 0; i < spare && len(g.free) > 1; i++ {
		scratchHomes = append(scratchHomes, g.free[0])
		g.free = g.free[1:]
	}
	for r := vecScratchHigh; r >= vecScratchLow; r-- {
		g.freeF = append(g.freeF, vecBase+r)
	}
	if mentionsFloat(fn) || g.recordsMentionFloat(fn) {
		g.saveAreaV = 8 * (vecCalleeHigh - vecCalleeLow + 1)
	}
	// Parameters take AAPCS64's integer registers in order — a scalar one, a
	// span or view two (base, then the 32-bit length), a record its chunks
	// or one for a reference — and past the registers the caller's outgoing
	// area (asm.LayoutArguments), read in the prologue.
	type paramClass struct {
		p      *ast.FunctionParameter
		s      scalar
		layout *recordLayout
		sp     span
		kind   int // 0 scalar, 1 record, 2 span
	}
	var intParams []paramClass
	var classes []asm.ArgClass
	vectorParams := 0
	for _, p := range fn.Parameters {
		if p.Variadic {
			return nil, 0, 0, unsupported("variadic parameter %s", p.Name.Value)
		}
		if s, ok := scalarOf(p.Type); ok {
			if s.isFloat || s.isVec {
				// Floats and fixed vectors arrive in v0–v7 (AAPCS64); a ninth
				// would go on the stack, which the register contract does
				// not spell — the function stays with the C backend.
				vectorParams++
				if vectorParams > 8 {
					return nil, 0, 0, unsupported("parameter %s: more than eight floating-point or vector parameters (the register contract passes eight, in v0–v7)", p.Name.Value)
				}
				continue
			}
			size := int64(s.bits / 8)
			if s.isBool {
				size = 4
			}
			intParams = append(intParams, paramClass{p: p, s: s})
			classes = append(classes, asm.ArgClass{Words: 1, Bytes: size, Align: size})
			continue
		}
		if layout, isValue, err := g.valueLayoutOf(p.Type); isValue {
			if err != nil {
				return nil, 0, 0, err
			}
			if layout.isHFA() {
				return nil, 0, 0, unsupported("parameter %s: %s is a homogeneous floating-point aggregate", p.Name.Value, layout.name)
			}
			regs := 1
			if layout.size <= 16 {
				regs = layout.chunks()
			}
			intParams = append(intParams, paramClass{p: p, layout: layout, kind: 1})
			classes = append(classes, asm.ArgClass{Words: regs, Bytes: int64(regs) * 8, Align: 8})
			continue
		}
		if sp, ok := g.spanTypeOf(p.Type); ok {
			intParams = append(intParams, paramClass{p: p, sp: sp, kind: 2})
			classes = append(classes, asm.ArgClass{Words: 2, Bytes: 16, Align: 8})
			continue
		}
		return nil, 0, 0, unsupported("parameter %s of type %s", p.Name.Value, p.Type.String())
	}
	places, stackArgs := asm.LayoutArguments(classes, g.packedStack)
	g.stackArgs = stackArgs
	nextReg := 0
	for i, pc := range intParams {
		place := places[i]
		name := pc.p.Name.Value
		if !place.OnStack && place.Reg+place.Regs > nextReg {
			nextReg = place.Reg + place.Regs
		}
		switch pc.kind {
		case 0:
			if place.OnStack {
				g.stackParams[name] = place
			} else {
				g.argHomes[name] = place.Reg
			}
		case 1:
			layout := pc.layout
			regs, indirect := 1, layout.size > 16
			if !indirect {
				regs = layout.chunks()
			}
			rp := &recordParam{layout: layout, reg: place.Reg, regs: regs, indirect: indirect}
			if place.OnStack {
				rp.reg = -1
				g.stackParams[name] = place
			}
			if indirect && !recordParamTouched(fn, name) && (!layoutHasArray(layout) || layout.isArray()) && g.usedCallee < calleeHigh-calleeLow+1 {
				// Read in place: the address parked in a callee-saved
				// register, the fields loaded through it (the checker's
				// region rule), no copy into the frame. Types drive it: a
				// parameter the body never writes, borrows, or addresses is
				// the caller's copy for the whole call.
				rp.inPlace, rp.park = true, calleeLow+g.usedCallee
				g.noteLoopHomes(rp.park)
				g.usedCallee++
				g.saveArea = 8 * (calleeHigh - calleeLow + 1)
			}
			g.recordParams[name] = rp
		case 2:
			sp := pc.sp
			sp.argBase, sp.argLen = place.Reg, place.Reg+1
			sp.baseReg, sp.lenReg = sp.argBase, sp.argLen
			if place.OnStack {
				// No register pair arrives: the pair is loaded into
				// callee-saved registers in the prologue.
				sp.argBase, sp.argLen = -1, -1
				g.stackParams[name] = place
			}
			if parkSpans || place.OnStack {
				// Two callee-saved registers, from the pool variables use.
				if g.usedCallee+2 > calleeHigh-calleeLow+1 {
					return nil, 0, 0, unsupported("the span parameters and locals exhaust the callee-saved registers")
				}
				sp.baseReg, sp.lenReg = calleeLow+g.usedCallee, calleeLow+g.usedCallee+1
				g.usedCallee += 2
				g.saveArea = 8 * (calleeHigh - calleeLow + 1)
			}
			g.spans[name] = sp
		}
	}
	if len(g.stackParams) > 0 {
		g.saveArea = 8 * (calleeHigh - calleeLow + 1)
	}
	if !g.hasCalls {
		// x0 (and x1) are left out: the result's registers, written at the
		// end, whatever the result's type.
		for r := nextReg; r < 8; r++ {
			if r <= 1 {
				continue
			}
			g.leafHomes = append(g.leafHomes, r)
		}
	} else {
		g.callerHomes = []int{16, 17}
		for r := nextReg; r < 8; r++ {
			if r <= 1 {
				continue
			}
			g.callerHomes = append(g.callerHomes, r)
		}
	}
	if !g.hasCalls {
		g.leafHomes = append(g.leafHomes, scratchHomes...)
	} else {
		g.callerHomes = append(g.callerHomes, scratchHomes...)
	}
	if fn.ReturnType != nil && fn.ReturnType.String() == "never" {
		// The function leaves by an exception return, never by ret.
		g.never = true
	}
	if fn.ReturnType != nil && !g.never {
		if fn.ReturnType.String() != "()" {
			if layout, isValue, err := g.valueLayoutOf(fn.ReturnType); isValue {
				if err != nil {
					return nil, 0, 0, err
				}
				if layout.isHFA() {
					return nil, 0, 0, unsupported("result of type %s (a homogeneous floating-point aggregate)", layout.name)
				}
				g.resultRecord = layout
				g.resultIndirect = layout.size > 16
				g.resultAreaReg = 8
				if g.resultIndirect && g.hasCalls {
					// A call clobbers x8: park the result area's address.
					if g.usedCallee+1 > calleeHigh-calleeLow+1 {
						return nil, 0, 0, unsupported("the parameters and locals exhaust the callee-saved registers")
					}
					g.resultAreaReg = calleeLow + g.usedCallee
					g.usedCallee++
				}
			} else {
				s, ok := scalarOf(fn.ReturnType)
				if !ok {
					return nil, 0, 0, unsupported("result of type %s", fn.ReturnType.String())
				}
				g.result = &s
			}
		}
	}
	// Scalar parameters occupy the first slots, in order.
	g.pushScope()
	for _, p := range fn.Parameters {
		if s, ok := scalarOf(p.Type); ok {
			if home, isHome := g.argHomes[p.Name.Value]; isHome && !g.hasCalls {
				g.declareAt(p.Name.Value, s, home)
			} else {
				g.declare(p.Name.Value, s)
			}
		}
		if rp, isRecord := g.recordParams[p.Name.Value]; isRecord {
			elem, length, isArray := rp.layout.arrayElem()
			switch {
			case isArray && rp.inPlace:
				rp.local = g.bindArrayParamRef(p.Name.Value, rp, elem, length)
			case isArray:
				// An array parameter is an array local whose storage the
				// prologue fills from the chunks or the caller's copy.
				arr := g.declareArray(p.Name.Value, elem, length)
				rp.local = &recordLocal{offset: arr.offset, layout: rp.layout}
			case rp.inPlace:
				rp.local = g.bindParamRef(p.Name.Value, rp)
			default:
				rp.local = g.declareRecord(p.Name.Value, rp.layout)
			}
		}
	}
	g.head = g.newLabel("head")
	// Callee-saved registers reserved for the loop-invariant pass, saved
	// and restored with the variables' (the count the first lowering
	// wanted; the epilogue and the prologue read usedCallee after this).
	for k := 0; k < reserve && g.usedCallee < calleeHigh-calleeLow+1; k++ {
		g.licmReserve = append(g.licmReserve, calleeLow+g.usedCallee)
		g.usedCallee++
	}
	body, err := g.lowerBody(fn.Body)
	if err != nil {
		return nil, 0, 0, err
	}
	// The frame: [x29, x30] when the body calls, then the slots, rounded to
	// 16 bytes; sp moves once at entry and once before ret.
	frame := g.frameSize()
	if frame > 4080 {
		return nil, 0, 0, unsupported("a frame of %d bytes", frame)
	}
	out := &asm.Function{Name: NativeSymbol(fn), Signature: fn, Line: fn.Token.Line, Fallback: true, Records: records, ADTs: adts, System: g.system, Tables: tableSizes(g.tables)}
	if len(g.usedGlobals) > 0 {
		out.Globals = g.usedGlobals
	}
	g.line = fn.Token.Line
	var prologue []asm.Item
	if frame > 0 {
		out.Frame = frame
		prologue = append(prologue, g.ins("sub", sp(), sp(), imm(frame)))
	}
	if g.hasCalls {
		prologue = append(prologue, g.ins("stp", xr(29), xr(30), mem(g.outgoing)))
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
		if place, onStack := g.stackParams[p.Name.Value]; onStack {
			// Beyond the register contract: the argument lies in the
			// caller's outgoing area, at place.Offset above the entry sp —
			// frame + place.Offset from the moved sp.
			out.Bindings = append(out.Bindings, asm.Binding{Param: p.Name.Value, OnStack: true, Stack: place.Offset, Line: fn.Token.Line})
			at := frame + place.Offset
			if rp, isRecord := g.recordParams[p.Name.Value]; isRecord {
				switch {
				case rp.inPlace:
					prologue = append(prologue, g.ins("ldr", xr(rp.park), mem(at)))
				case rp.indirect:
					prologue = append(prologue, g.ins("ldr", xr(scratchLow), mem(at)))
					prologue = append(prologue, g.copyIn(rp.local, scratchLow)...)
				default:
					for i := 0; i < rp.regs; i++ {
						prologue = append(prologue, g.ins("ldr", xr(scratchLow), mem(at+int64(8*i))), g.ins("str", xr(scratchLow), g.slotMem(rp.local.offset+int64(8*i))))
					}
				}
				continue
			}
			if sp, isSpan := g.spans[p.Name.Value]; isSpan {
				prologue = append(prologue, g.ins("ldr", xr(sp.baseReg), mem(at)), g.ins("ldr", wr(sp.lenReg), mem(at+8)))
				continue
			}
			s, _ := scalarOf(p.Type)
			load := "ldr"
			switch {
			case s.isBool || s.bits == 32:
			case s.bits == 8:
				load = "ldrb"
			case s.bits == 16:
				load = "ldrh"
			}
			prologue = append(prologue, g.ins(load, reg(scratchLow, s), mem(at)))
			prologue = append(prologue, g.normalizeInto(scratchLow, s)...)
			prologue = append(prologue, g.storeVar(p.Name.Value, scratchLow))
			continue
		}
		if rp, isRecord := g.recordParams[p.Name.Value]; isRecord {
			binding := asm.Binding{Register: xr(rp.reg), Param: p.Name.Value, Line: fn.Token.Line}
			if rp.regs == 2 {
				second := xr(rp.reg + 1)
				binding.Length = &second
			}
			out.Bindings = append(out.Bindings, binding)
			if rp.inPlace {
				// The caller's copy stays where it is: its address parks in
				// a callee-saved register (the region fact follows the mov).
				prologue = append(prologue, g.ins("mov", xr(rp.park), xr(rp.reg)))
			} else if rp.indirect {
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
		if s.isFloat || s.isVec {
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
		if v, inReg := g.regs[p.Name.Value]; !inReg || v != i {
			prologue = append(prologue, g.storeVar(p.Name.Value, i))
		}
	}
	// The loop header a tail self-call re-enters: after the parameters are
	// in their slots.
	prologue = append(prologue, asm.Label{Name: g.head, Line: fn.Token.Line})
	// Adjacent element loads of one span pair up (nativegen/pair_loads.go).
	body = pairLoads(body)
	// Loop-invariant code motion (nativegen/licm.go): the registers a rename
	// may take are those neither the prologue nor the body names.
	hoistWanted := 0
	if hoist {
		named := registersNamed(append(append([]asm.Item(nil), prologue...), body...))
		var hoistedInto []int
		var moved int
		body, hoistedInto, moved, hoistWanted = hoistInvariants(body, named, g.loopHomes, g.licmReserve, g.globals, g.trap)
		hoistedLoops[out] = moved
		for _, r := range hoistedInto {
			if r >= 16 && r-16 >= g.ipScratch {
				g.ipScratch = r - 16 + 1 // x16/x17 taken: declared as clobbers below
			}
		}
	}
	out.Items = append(prologue, body...)
	// Clobbers: the scratch registers, the argument registers a call
	// writes beyond the bound parameters, and the link register.
	for r := scratchLow; r <= scratchHigh; r++ {
		out.Clobbers = append(out.Clobbers, xr(r))
	}
	for i := 0; i < g.ipScratch; i++ {
		out.Clobbers = append(out.Clobbers, xr(16+i)) // overflow scratch (overflowScratch)
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
		} else {
			// A leaf's argument-register vector homes (leafVectorPool).
			for r := 1; r <= 7; r++ {
				if g.homesUsedV[vecBase+r] {
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
		for _, r := range []int{16, 17} {
			if g.homesUsed[r] {
				out.Clobbers = append(out.Clobbers, xr(r))
			}
		}
	} else {
		// A leaf writes the argument registers that are homes (a parameter
		// assigned, a local placed there).
		integerResult := g.result != nil && !g.result.isFloat && !g.result.isVec
		for r := 0; r <= 7; r++ {
			if g.homesUsed[r] && !(integerResult && r == 0) {
				out.Clobbers = append(out.Clobbers, xr(r))
			}
		}
	}
	if g.usedX8 {
		out.Clobbers = append(out.Clobbers, xr(8))
	}
	// Every placeable record and union of the program, for the checker's
	// composite binding rules and the verifier's leaf model (nested types
	// included) — also under each signature type's own spelling, which is
	// what the checker and verifier look up (an instantiation is spelled
	// Option[u32] in the signature and Option_u32 in the table).
	out.Composites = Composites(records, adts)
	out.Constants = constants
	out.StackArgs, out.PackedStackArgs = g.stackArgs, g.packedStack
	pressured[out] = g.pressure
	spell := func(expr ast.Expression) {
		if expr == nil {
			return
		}
		if name, isRecord := g.recordTypeName(expr); isRecord {
			if comp, placed := out.Composites[name]; placed {
				out.Composites[expr.String()] = comp
			}
		}
		if layout, isArray := g.arrayLayoutOf(expr); isArray {
			// An owned array of scalars as a value: its one-field composite
			// under the type's spelling.
			out.Composites[expr.String()] = layout.composite()
		}
		if index, isIndex := expr.(*ast.IndexExpression); isIndex && !index.Dot {
			if marker, isMarker := index.Index.(*ast.Identifier); isMarker && (marker.Value == "" || marker.Value == "*") {
				if name, isRecord := g.recordTypeName(index.Left); isRecord {
					if comp, placed := out.Composites[name]; placed {
						out.Composites[index.Left.String()] = comp
					}
				}
			}
		}
	}
	for _, p := range fn.Parameters {
		spell(p.Type)
	}
	spell(fn.ReturnType)
	// The result types of the program's functions too: the verifier
	// summarizes a call returning a record or a sum type from the callee's
	// aggregate value packed by this table (asm/verify.go summarizeCall).
	for _, callee := range g.functions {
		if callee != nil {
			spell(callee.ReturnType)
			for _, p := range callee.Parameters {
				if p != nil {
					spell(p.Type)
				}
			}
		}
	}
	if g.elided > 0 {
		elidedGuards[out] = g.elided
	}
	if g.reduced > 0 {
		reducedOps[out] = g.reduced
	}
	if g.vecHomes > 0 {
		vectorHomesOf[out] = g.vecHomes
	}
	if g.leafVecHomes > 0 {
		leafVectorHomesOf[out] = g.leafVecHomes
	}
	if g.reused > 0 {
		reusedCompares[out] = g.reused
	}
	return out, g.peakScratch, hoistWanted, nil
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
			if p.arr != nil {
				if rec, isValue := g.arrayAsRecord(p.arr); isValue {
					return rec, nil
				}
			}
			return nil, unsupported("%s is not a record", expr.String())
		}
		return p.rec, nil
	case *ast.ArrayLiteral:
		return g.arrayLiteralValue(e, expected)
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

// arrayLiteralValue builds an array literal (`[8]u32{…}`, or an untyped
// one where an array value is expected) in fresh frame storage, one
// element at a time, and yields it as the array's record view.
func (g *generator) arrayLiteralValue(e *ast.ArrayLiteral, expected *recordLayout) (*recordLocal, error) {
	layout := expected
	if e.Type != nil {
		typed, isArray := g.arrayLayoutOf(e.Type)
		if !isArray {
			return nil, unsupported("an array literal of type %s as a value", e.Type.String())
		}
		layout = typed
	}
	if layout == nil {
		return nil, unsupported("an untyped array literal as a value")
	}
	elem, length, isArray := layout.arrayElem()
	if !isArray {
		return nil, unsupported("an array literal where %s is expected", layout.name)
	}
	if int64(len(e.Elements)) != length {
		return nil, unsupported("an array literal of %d elements for %s", len(e.Elements), layout.name)
	}
	if elem.isFloat {
		g.usedFloat = true
	}
	arr := g.allocArray(elem, length)
	for i, element := range e.Elements {
		r, err := g.expr(element, &elem)
		if err != nil {
			return nil, err
		}
		g.emit(storeOf(elem), reg(r, elem), g.slotMem(arr.offset+int64(i)*int64(elem.bits/8)))
		g.release(r)
	}
	rec, _ := g.arrayAsRecord(arr)
	return rec, nil
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
	// Every byte defined: inactive payloads and padding are zero (the C
	// backend leaves them unspecified; zero is one value both realizations'
	// readers never observe, and it lets the verifier compare whole chunks).
	zero, err := g.alloc(scalars["u64"])
	if err != nil {
		return nil, err
	}
	g.emit("mov", xr(zero), imm(0))
	for w := int64(0); w < (layout.size+7)/8; w++ {
		g.emit("str", xr(zero), g.slotMem(rec.offset+8*w))
	}
	g.release(zero)
	tag, err := g.alloc(scalars["u32"])
	if err != nil {
		return nil, err
	}
	g.constant(tag, uint64(info.tag), scalars["u32"])
	g.emit("str", wr(tag), g.slotMem(rec.offset))
	g.release(tag)
	switch {
	case payloadReg >= 0:
		if err := g.fieldStore(&scalarPlace{offset: rec.offset + field.offset, typ: field.typ}, payloadReg); err != nil {
			return nil, err
		}
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
	// A scalar scrutinee with literal patterns: a variable in a register
	// is compared where it lives, anything else evaluated into a scratch.
	typ, err := g.typeOf(match.Scrutinee, nil)
	if err != nil {
		return err
	}
	value, fixed := -1, false
	if ident, isIdent := match.Scrutinee.(*ast.Identifier); isIdent && !typ.isFloat {
		if v, inReg := g.regs[ident.Value]; inReg && v >= 0 && v < vecBase {
			if t, ok := g.types[ident.Value]; ok && !t.isFloat && !t.isVec && t.wide() == typ.wide() {
				value, fixed = v, true
			}
		}
	}
	if !fixed {
		value, err = g.expr(match.Scrutinee, &typ)
		if err != nil {
			return err
		}
	}
	closed := false
	for _, matchArm := range match.Arms {
		next := g.newLabel("arm")
		switch pattern := matchArm.Pattern.(type) {
		case *ast.LiteralPattern:
			// A small literal is the compare's immediate; anything else
			// is materialized.
			if op, isImm := g.simpleOperand(pattern.Value, typ, true); isImm && !typ.isFloat {
				g.emit("cmp", reg(value, typ), op)
			} else {
				lit, err := g.expr(pattern.Value, &typ)
				if err != nil {
					return err
				}
				g.emit("cmp", reg(value, typ), reg(lit, typ))
				g.release(lit)
			}
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
	if !fixed {
		g.release(value)
	}
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
		g.put(g.storeVar(name, r))
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
			if err := g.fieldStore(&scalarPlace{offset: at, typ: field.typ}, values[i].reg); err != nil {
				return nil, err
			}
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
	layout, isValue, err := g.valueLayoutOf(callee.ReturnType)
	if !isValue {
		return nil, unsupported("a call to %s in record position", ident.Value)
	}
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
		if !g.resultIndirect && g.valueOnly(e) {
			// The arms meet in one frame temporary and the result chunks
			// load into x0 (and x1) once, at the join — as a scalar result
			// does (resultInto): a chunk loaded inside an arm would forget
			// the parameters' span and record facts in the linear checker.
			var outs []int
			for i := 0; i < g.resultRecord.chunks(); i++ {
				out, err := g.alloc(scalars["u64"])
				if err != nil {
					return err
				}
				g.emit("mov", xr(out), xr(31)) // defined before the arms (see resultExpr)
				outs = append(outs, out)
			}
			if err := g.resultRecordInto(e, outs); err != nil {
				return err
			}
			for i, out := range outs {
				g.emit("mov", xr(i), xr(out))
				g.release(out)
			}
			return nil
		}
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
			if err := g.lowerStatementsBefore(stmts[:len(stmts)-1], stmts[len(stmts)-1]); err != nil {
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

// resultRecordInto lowers a value-only record result into the scratch
// registers outs, one per chunk: a conditional's arms each load their
// record's chunks there and meet at the join (registers merge in the
// verifier's path model where frame slots do not); a block runs its
// statements and yields its tail.
func (g *generator) resultRecordInto(expr ast.Expression, outs []int) error {
	switch e := expr.(type) {
	case *ast.MatchExpression:
		if whenTrue, whenFalse, ok := boolConditional(e); ok {
			elseLabel, end := g.newLabel("else"), g.newLabel("endif")
			if err := g.condition(e.Scrutinee, elseLabel); err != nil {
				return err
			}
			if err := g.resultRecordInto(whenTrue, outs); err != nil {
				return err
			}
			g.emit("b", asm.Symbol{Name: end})
			g.label(elseLabel)
			if err := g.resultRecordInto(whenFalse, outs); err != nil {
				return err
			}
			g.label(end)
			return nil
		}
		return g.lowerMatch(e, func(body ast.Expression) error { return g.resultRecordInto(body, outs) })
	case *ast.BlockExpression:
		if e.Block != nil && len(e.Block.Statements) > 0 {
			g.pushScope()
			defer g.popScope()
			stmts := e.Block.Statements
			// The trailing expression still reads the block's locals: its
			// uses count before any register is released (nativegen/liveness.go).
			if err := g.lowerStatementsBefore(stmts[:len(stmts)-1], stmts[len(stmts)-1]); err != nil {
				return err
			}
			if es, ok := stmts[len(stmts)-1].(*ast.ExpressionStatement); ok && !es.Discard {
				return g.resultRecordInto(es.Expression, outs)
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
	if rec.inReg || g.slotMem(rec.offset).Offset%8 != 0 {
		aligned := g.tempRecord(g.resultRecord)
		if err := g.copyRecord(aligned, rec); err != nil {
			return err
		}
		g.releaseTemps(rec.temps)
		rec = aligned
	}
	for i, out := range outs {
		g.emit("ldr", xr(out), g.slotMem(rec.offset+int64(8*i)))
	}
	g.releaseTemps(rec.temps)
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
	base := g.outgoing // the outgoing argument area sits at the bottom
	if g.hasCalls {
		base += 16
	}
	return base
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
		if typ.isVec {
			return g.ins("orr", vreg(v-vecBase, "16b"), vreg(r-vecBase, "16b"), vreg(r-vecBase, "16b"))
		}
		return g.ins(moveOf(typ), reg(v, typ), reg(r, typ))
	}
	if typ.isVec {
		return g.ins("str", qreg(r-vecBase), g.slotMem(g.slots[name]))
	}
	return g.ins("str", reg(r, typ), g.slotMem(g.slots[name]))
}

// loadVar brings a variable's value into register r.
func (g *generator) loadVar(name string, r int) asm.Instruction {
	typ := g.types[name]
	if v, inReg := g.regs[name]; inReg && v >= 0 {
		if typ.isVec {
			return g.ins("orr", vreg(r-vecBase, "16b"), vreg(v-vecBase, "16b"), vreg(v-vecBase, "16b"))
		}
		return g.ins(moveOf(typ), reg(r, typ), reg(v, typ))
	}
	if typ.isVec {
		return g.ins("ldr", qreg(r-vecBase), g.slotMem(g.slots[name]))
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

// zeroPair stores two zero words at a frame slot: `stp` while the offset is
// within the pair form's scaled 7-bit immediate (-512..504), two `str`
// otherwise (the single form reaches 32760) — the encoder refuses an
// offset outside its field rather than truncating it.
func (g *generator) zeroPair(zero int, slot asm.Memory) {
	if slot.Offset >= -512 && slot.Offset <= 504 {
		g.emit("stp", xr(zero), xr(zero), slot)
		return
	}
	g.emit("str", xr(zero), slot)
	g.emit("str", xr(zero), asm.Memory{Base: slot.Base, Offset: slot.Offset + 8})
}

func (g *generator) ins(mnemonic string, operands ...asm.Operand) asm.Instruction {
	g.noteWrite(mnemonic, operands)
	return asm.Instruction{Mnemonic: mnemonic, Operands: operands, Line: g.line}
}

// noteWrite records that an instruction writes a scratch register (its
// first operand, unless the mnemonic only reads it), for the call spill.
func (g *generator) noteWrite(mnemonic string, operands []asm.Operand) {
	if len(operands) == 0 || !writesFirstOperand(mnemonic) {
		return
	}
	reg, isReg := operands[0].(asm.Register)
	if !isReg {
		return
	}
	switch reg.Class {
	case asm.ClassV, asm.ClassRV64F:
		g.defined[vecBase+reg.Num] = true
	case asm.ClassRV64V:
		g.defined[rvVBase+reg.Num] = true
	default:
		g.defined[reg.Num] = true
	}
}

// writesFirstOperand reports whether a mnemonic's first operand is its
// destination: every instruction of either lane except the stores, the
// comparisons, and the control transfers.
func writesFirstOperand(mnemonic string) bool {
	switch mnemonic {
	case "stxr", "stlxr", "stxrb", "stlxrb", "stxrh", "stlxrh":
		return true // the store-exclusive status register
	case "cmp", "cmn", "tst", "fcmp", "fcmpe", "cbz", "cbnz", "tbz", "tbnz", "ret", "brk", "bl", "b",
		"beq", "bne", "blt", "bge", "bltu", "bgeu", "j", "jal", "jalr", "call", "ebreak",
		"sd", "sw", "sh", "sb", "fsd", "fsw", "vsetivli", "vsetvli", "vse8.v", "vse16.v", "vse32.v", "vse64.v":
		return false
	}
	return !strings.HasPrefix(mnemonic, "st") && !strings.HasPrefix(mnemonic, "b.")
}

// returnsValue reports whether a function has a result (anything but unit).
func returnsValue(fn *ast.FunctionStatement) bool {
	return fn.ReturnType != nil && fn.ReturnType.String() != "()"
}

// globalOf resolves a name to an addressable global (Lane.Globals) when no
// local of any kind shadows it, with the scalar type its reads and writes
// take.
func (g *generator) globalOf(name string) (asm.Global, scalar, bool) {
	global, isGlobal := g.globals[name]
	if !isGlobal || g.shadowed(name) {
		return asm.Global{}, scalar{}, false
	}
	typ, ok := scalars[global.Type]
	if !ok {
		return asm.Global{}, scalar{}, false
	}
	return global, typ, true
}

// globalAddress materializes a global's address in a fresh 64-bit
// scratch register — `adrp xA, G` then `add xA, xA, :lo12:G`, the pair the
// checker follows and the linker resolves — and records the global as
// one the body addresses.
func (g *generator) globalAddress(name string, global asm.Global) (int, error) {
	if g.rvLane {
		return 0, unsupported("the global %s on the rv64 lane", name)
	}
	addr, err := g.alloc(scalars["u64"])
	if err != nil {
		return 0, err
	}
	g.emit("adrp", xr(addr), asm.Symbol{Name: name})
	g.emit("add", xr(addr), xr(addr), asm.Symbol{Name: name, Lo12: true})
	g.usedGlobals[name] = global
	return addr, nil
}

// globalLoad reads a global's cell into r at its storage width.
func (g *generator) globalLoad(name string, global asm.Global, typ scalar, r int) error {
	addr, err := g.globalAddress(name, global)
	if err != nil {
		return err
	}
	g.emit(globalAccessOf("ldr", global), reg(r, typ), asm.Memory{Base: xr(addr)})
	g.release(addr)
	return nil
}

// globalStore writes r into a global's cell at its storage width.
func (g *generator) globalStore(name string, global asm.Global, typ scalar, r int) error {
	addr, err := g.globalAddress(name, global)
	if err != nil {
		return err
	}
	g.emit(globalAccessOf("str", global), reg(r, typ), asm.Memory{Base: xr(addr)})
	g.release(addr)
	return nil
}

// globalAccessOf is the load or store of a global's storage width: a Bool
// is the C backend's 4-byte cell, read and written whole.
func globalAccessOf(base string, global asm.Global) string {
	switch global.Bits {
	case 8:
		return base + "b"
	case 16:
		return base + "h"
	}
	return base
}

// shadowed reports a local of any kind under the name.
func (g *generator) shadowed(name string) bool {
	if _, isVar := g.types[name]; isVar {
		return true
	}
	if _, isSpan := g.spans[name]; isSpan {
		return true
	}
	if _, isArray := g.arrays[name]; isArray {
		return true
	}
	if _, isRecord := g.records[name]; isRecord {
		return true
	}
	if _, isRecordParam := g.recordParams[name]; isRecordParam {
		return true
	}
	return false
}

// constantOf resolves a name to a constant global when no local of any
// kind shadows it.
func (g *generator) constantOf(name string) (asm.Constant, bool) {
	c, isConst := g.constants[name]
	if !isConst {
		return asm.Constant{}, false
	}
	if _, isVar := g.types[name]; isVar {
		return asm.Constant{}, false
	}
	if _, isSpan := g.spans[name]; isSpan {
		return asm.Constant{}, false
	}
	if _, isArray := g.arrays[name]; isArray {
		return asm.Constant{}, false
	}
	if _, isRecord := g.records[name]; isRecord {
		return asm.Constant{}, false
	}
	if _, isRecordParam := g.recordParams[name]; isRecordParam {
		return asm.Constant{}, false
	}
	if _, known := scalars[c.Type]; !known {
		return asm.Constant{}, false
	}
	return c, true
}

func (g *generator) emit(mnemonic string, operands ...asm.Operand) {
	if g.terminated {
		return
	}
	g.liveFlags = ""
	g.items = append(g.items, g.ins(mnemonic, operands...))
	switch mnemonic {
	case "b", "cbz", "cbnz", "tbz", "tbnz":
		// A transfer that is not a compare's branch: the target's flags
		// are not one compare's.
		if sym, isSym := operands[len(operands)-1].(asm.Symbol); isSym {
			g.flagsTo[sym.Name] = ""
		}
	}
	if mnemonic == "b" || mnemonic == "ret" || mnemonic == "brk" {
		g.terminated = true
	}
}

func (g *generator) branch(cond, label string) {
	g.branchFlags(cond, label, "")
}

// branchFlags is branch recording the compare (its operands' spelling)
// whose flags the branch reads, for the reuse at the label; "" records a
// branch whose flags are not one compare's.
func (g *generator) branchFlags(cond, label, compare string) {
	if g.terminated {
		return
	}
	g.liveFlags = ""
	if known, seen := g.flagsTo[label]; !seen {
		g.flagsTo[label] = compare
	} else if known != compare {
		g.flagsTo[label] = ""
	}
	g.items = append(g.items, asm.Instruction{Mnemonic: "b.", Cond: cond, Operands: []asm.Operand{asm.Symbol{Name: label}}, Line: g.line})
}

func (g *generator) label(name string) {
	// The flags at the label are one compare's when every transfer to it
	// is that compare's branch and nothing falls through (the label
	// follows an unconditional transfer); a backward branch to a label
	// never carries a compare (loop heads are fall-through labels).
	g.liveFlags = ""
	if g.terminated && g.reuseFlags {
		g.liveFlags = g.flagsTo[name]
	}
	g.items = append(g.items, asm.Label{Name: name, Line: g.line})
	g.terminated = false
}

func (g *generator) newLabel(hint string) string {
	g.labels++
	return fmt.Sprintf("%s_%d", hint, g.labels)
}

// reg spells scratch register r at the type's width.
func reg(r int, s scalar) asm.Register {
	if s.isVec {
		return vreg(r-vecBase, s.arr())
	}
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
	if s.isVec {
		return wholeV(n)
	}
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
	if typ.isVec && g.rvLane {
		// The rv64 lane's vector file is its own (nativegen/rv64_simd.go).
		pool = &g.freeV
	} else if typ.isFloat || typ.isVec {
		pool = &g.freeF
		g.usedFloat = true
	}
	if len(*pool) == 0 {
		if typ.isFloat || (typ.isVec && g.rvLane) {
			return 0, unsupported("an expression deeper than the scratch registers")
		}
		r, ok := g.overflowScratch()
		if !ok {
			return 0, unsupported("an expression deeper than the scratch registers")
		}
		g.live = append(g.live, r)
		g.peakScratch = scratchHigh - scratchLow + 1 // every scratch register held, and more
		return r, nil
	}
	r := (*pool)[len(*pool)-1]
	*pool = (*pool)[:len(*pool)-1]
	g.live = append(g.live, r)
	g.notePeak()
	return r, nil
}

// notePeak records the most integer scratch registers live at once (the
// first pass's measurement for the second's homes).
func (g *generator) notePeak() {
	n := 0
	for _, r := range g.live {
		if r < vecBase {
			n++
		}
	}
	if n > g.peakScratch {
		g.peakScratch = n
	}
}

// overflowScratch widens the integer scratch pool when x9–x15 are all live
// in one expression (the OS pilot's N6, a deep expression that fell back):
// x16 and x17 in a function that makes no call (the intra-procedure-call
// registers, unused by the generator and clobbered only by a veneer at a
// `bl`), then the next unclaimed callee-saved register, counted with the
// locals so the prologue saves it and the epilogue restores it. Once
// released the register stays in the pool. The rv64 lane keeps its own
// pools.
func (g *generator) overflowScratch() (int, bool) {
	if g.rvLane {
		return 0, false
	}
	if !g.hasCalls && g.ipScratch < 2 {
		r := 16 + g.ipScratch
		g.ipScratch++
		return r, true
	}
	if g.usedCallee >= calleeHigh-calleeLow+1 {
		if r, ok := g.reclaimReserve(); ok {
			return r, true
		}
		return 0, false
	}
	if g.saveArea == 0 {
		if g.nslots != 0 {
			// Slot offsets already emitted assume no save area.
			return 0, false
		}
		g.saveArea = 8 * (calleeHigh - calleeLow + 1)
	}
	r := calleeLow + g.usedCallee
	g.usedCallee++
	return r, true
}

// put appends one item built elsewhere (ins marks its write for the
// call spill); the emission paths that build their own instruction go
// through here or emit.
func (g *generator) put(item asm.Item) {
	g.liveFlags = ""
	g.items = append(g.items, item)
}

func (g *generator) release(r int) {
	delete(g.defined, r)
	for i, live := range g.live {
		if live == r {
			g.live = append(g.live[:i], g.live[i+1:]...)
			break
		}
	}
	if r >= rvVBase {
		g.freeV = append(g.freeV, r)
		return
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
	// In name order: the pools' order decides which register a later
	// declaration takes, and a map's order would make the lowering differ
	// between two builds of one source.
	names := make([]string, 0, len(top))
	for name := range top {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		// The variable's register or slot returns to the pool for the
		// declarations that follow.
		if b := top[name]; b.arr == nil && b.rec == nil && b.sp == nil && !b.freed {
			switch {
			case b.reg >= vecBase:
				g.releaseVectorHome(b.reg)
			case b.reg >= 0:
				g.freeCallee = append(g.freeCallee, b.reg)
			case b.offset >= 0 && b.typ.isVec:
				g.freeSlots16 = append(g.freeSlots16, b.offset)
			case b.offset >= 0:
				g.freeSlots8 = append(g.freeSlots8, b.offset)
			}
		}
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
	if _, isLiteral := s.Value.(*ast.ArrayLiteral); s.Value != nil && !isLiteral {
		// `state: [8]u32 = h` / `= f(…)`: the value evaluates first (an
		// initializer never sees the array it fills), then copies into
		// storage reserved for the name.
		if _, placeable := fieldRepresentations[elem.name]; !placeable || elem.isBool {
			return unsupported("an array local initialized from %s", s.Value.String())
		}
		from, err := g.recordValueAs(s.Value, g.arrayLayout(elem, length))
		if err != nil {
			return err
		}
		arr := g.allocArray(elem, length)
		dst, _ := g.arrayAsRecord(arr)
		if from.layout != dst.layout {
			return unsupported("an array local %s initialized from a %s", s.Name.Value, from.layout.name)
		}
		if err := g.copyRecord(dst, from); err != nil {
			return err
		}
		g.releaseTemps(from.temps)
		g.bindArray(s.Name.Value, arr)
		return nil
	}
	if !elem.isVec && !elem.isBool && scalarReplaceable(g.fn, s.Name.Value, length) {
		// Every use an element at a literal index: the elements are
		// scalars in registers (nativegen/scalar_arrays.go).
		var literal *ast.ArrayLiteral
		if s.Value != nil {
			lit, isLiteral := s.Value.(*ast.ArrayLiteral)
			if !isLiteral {
				return unsupported("an array local initialized from %s", s.Value.String())
			}
			if int64(len(lit.Elements)) != length {
				return unsupported("an array literal of %d elements for [%d]%s", len(lit.Elements), length, elem.name)
			}
			literal = lit
		}
		return g.declareScalarArray(s, elem, length, literal)
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
				g.zeroPair(zero, g.slotMem(arr.offset+8*w))
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
// bindParamRef binds an in-place record parameter: the caller's memory at
// the parked address register, read-only.
func (g *generator) bindParamRef(name string, rp *recordParam) *recordLocal {
	rec := &recordLocal{inReg: true, reg: rp.park, layout: rp.layout, readOnly: true, paramRef: true}
	delete(g.slots, name)
	delete(g.types, name)
	delete(g.regs, name)
	g.records[name] = rec
	g.scopes[len(g.scopes)-1][name] = slotBinding{reg: -1, rec: rec}
	return rec
}

// bindArrayParamRef binds an in-place array parameter: the caller's array
// at the parked address register, read-only; the record view of it is
// what a call passing it on uses.
func (g *generator) bindArrayParamRef(name string, rp *recordParam, elem scalar, length int64) *recordLocal {
	arr := &arrayLocal{elem: elem, length: length, inReg: true, reg: rp.park, readOnly: true, paramRef: true}
	g.bindArray(name, arr)
	rec, _ := g.arrayAsRecord(arr)
	return rec
}

// recordParamTouched reports whether a body assigns a record parameter or
// a path under it, takes its address (`&p`, `&p.f`: view, span,
// address_of), or calls the function itself (a tail self-call rebinds the
// parameters) — the uses under which the parameter needs a copy of its own.
func recordParamTouched(fn *ast.FunctionStatement, name string) bool {
	touched := false
	walk(fn.Body, func(n ast.Node) {
		switch e := n.(type) {
		case *ast.AssignmentStatement:
			if e.Name != nil && e.Name.Value == name {
				touched = true
			}
		case *ast.IndexAssignmentStatement:
			if root, ok := pathRoot(e.Target); ok && root == name {
				touched = true
			}
		case *ast.PrefixExpression:
			if e.Operator == "&" {
				if root, ok := pathRoot(e.Right); ok && root == name {
					touched = true
				}
			}
		case *ast.InvocationExpression:
			if ident, isIdent := e.Function.(*ast.Identifier); isIdent && fn.Name != nil && ident.Value == fn.Name.Value {
				touched = true
			}
		}
	})
	return touched
}

// pathRoot is the identifier at the root of an access path (`p.f[i].g`).
func pathRoot(expr ast.Expression) (string, bool) {
	for {
		switch e := expr.(type) {
		case *ast.Identifier:
			return e.Value, true
		case *ast.IndexExpression:
			expr = e.Left
		default:
			return "", false
		}
	}
}

// layoutHasArray reports an owned-array field anywhere in a layout: such a
// field is walked through a frame address, which an in-place parameter
// has none of.
func layoutHasArray(l *recordLayout) bool {
	for _, f := range l.fields {
		switch f.kind {
		case fieldArray:
			return true
		case fieldRecord:
			if f.layout != nil && layoutHasArray(f.layout) {
				return true
			}
		}
	}
	return false
}

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
	baseReg, lenReg, ok := g.takeCalleePair()
	if !ok {
		return unsupported("the span local %s: the callee-saved registers are exhausted", s.Name.Value)
	}
	value, owned, err := g.spanValue(s.Value, &target, baseReg, lenReg)
	if err != nil {
		return err
	}
	if owned {
		// Another named span's pair: copy it.
		g.emit("mov", xr(baseReg), xr(value.baseReg))
		g.emit("mov", wr(lenReg), wr(value.lenReg))
	}
	local := span{elem: target.elem, elemLayout: target.elemLayout, writable: target.writable, baseReg: baseReg, lenReg: lenReg, argBase: -1, argLen: -1, array: value.array, frameLen: value.frameLen}
	delete(g.slots, s.Name.Value)
	delete(g.types, s.Name.Value)
	delete(g.regs, s.Name.Value)
	g.spans[s.Name.Value] = local
	g.noteLoopHomes(local.baseReg, local.lenReg)
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
		arr, err := g.arrayOperand(borrow.Right)
		if err != nil {
			return span{}, false, err
		}
		if arr == nil {
			return span{}, false, unsupported("%s of %s (only an owned array)", fn.Value, borrow.Right.String())
		}
		if target != nil && (arr.elem != target.elem || arr.elemLayout != target.elemLayout) {
			return span{}, false, unsupported("%s over %s where the span type's elements are expected", fn.Value, borrow.Right.String())
		}
		if arr.inReg && !arr.readOnly {
			return span{}, false, unsupported("%s of an array inside a computed element", fn.Value)
		}
		out.elem, out.elemLayout, out.writable, out.array, out.frameLen = arr.elem, arr.elemLayout, shape.writable, arr, arr.length
		if arr.inReg {
			// A constant table's address (the checker copies the region).
			if shape.writable {
				return span{}, false, unsupported("span of the constant table %s (read-only)", borrow.Right.String())
			}
			if err := g.addOffset(baseReg, arr.reg, arr.offset); err != nil {
				return span{}, false, err
			}
			g.releaseTemps(arr.temps)
			// The view's elements are addressed from its own base register
			// (the table's temporary is released here and may be reused).
			rebased := *arr
			rebased.reg, rebased.offset, rebased.temps = baseReg, 0, nil
			out.array = &rebased
		} else {
			g.emit("add", xr(baseReg), sp(), imm(g.slotMem(arr.offset).Offset))
		}
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
		// Value-less storage is zero (docs/spec/90-backend.md §6: the C
		// emitter's `{0}`, the interpreter's zero value): the slots are
		// zero-filled whole, as an owned array's are.
		rec := g.declareRecord(s.Name.Value, layout)
		zero, err := g.alloc(scalars["u64"])
		if err != nil {
			return err
		}
		g.emit("mov", xr(zero), imm(0))
		words := (layout.size + 7) / 8
		for w := int64(0); w < words; w += 2 {
			if w+1 < words {
				g.zeroPair(zero, g.slotMem(rec.offset+8*w))
			} else {
				g.emit("str", xr(zero), g.slotMem(rec.offset+8*w))
			}
		}
		g.release(zero)
		return nil
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
	size := int64(sc.typ.bits / 8)
	if sc.typ.isBool {
		load, size = "ldr", 4
	}
	mem, temp, err := g.reachable(sc.loc(), size)
	if err != nil {
		return 0, err
	}
	g.emit(load, reg(r, sc.typ), mem)
	if temp >= 0 {
		g.release(temp)
	}
	return r, nil
}

// fieldStore writes a normalized value of the field's type.
func (g *generator) fieldStore(sc *scalarPlace, r int) error {
	store := storeOf(sc.typ)
	size := int64(sc.typ.bits / 8)
	if sc.typ.isBool {
		store, size = "str", 4
	}
	mem, temp, err := g.reachable(sc.loc(), size)
	if err != nil {
		return err
	}
	g.emit(store, reg(r, sc.typ), mem)
	if temp >= 0 {
		g.release(temp)
	}
	return nil
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
				g.zeroPair(zero, g.slotMem(arr.offset+8*w))
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
	if s.isVec {
		// A vector local: a callee-saved vector register when the function
		// makes no call (a callee may clobber their upper halves), else a
		// sixteen-byte, sixteen-aligned frame slot.
		g.usedFloat = true
		switch {
		case !g.hasCalls && len(g.freeCalleeV) > 0:
			r, g.freeCalleeV = g.freeCalleeV[len(g.freeCalleeV)-1], g.freeCalleeV[:len(g.freeCalleeV)-1]
		case !g.hasCalls && g.usedCalleeV < vecCalleeHigh-vecCalleeLow+1:
			r = vecBase + vecCalleeLow + g.usedCalleeV
			g.usedCalleeV++
		case !g.hasCalls && len(g.freeF) > vecTempReserve:
			// No call clobbers the caller-saved vector registers, so a
			// function without calls keeps locals in them too, leaving the
			// deepest expression its temporaries.
			r, g.freeF = g.freeF[0], g.freeF[1:]
		case g.hasCalls && g.vectorHomePool() > 0:
			// A calling function's vector local in a caller-saved vector
			// register (Lane.VectorHomes): saved around a call only when
			// live after it (callerHomesLive), like the scalar homes.
			r, g.callerHomesV = g.callerHomesV[0], g.callerHomesV[1:]
			g.homesUsedV[r] = true
			g.vecHomes++
		case !g.hasCalls && g.leafVectorPool() > 0:
			// A leaf's vector local in an argument register no parameter
			// occupies (Lane.VectorHomes), as the scalar leaf homes in
			// x2–x7: nothing to save, no call to clobber it. v0 is left
			// out for the result.
			r, g.leafHomesV = g.leafHomesV[0], g.leafHomesV[1:]
			g.homesUsedV[r] = true
			g.leafVecHomes++
		case len(g.freeSlots16) > 0:
			offset, g.freeSlots16 = g.freeSlots16[len(g.freeSlots16)-1], g.freeSlots16[:len(g.freeSlots16)-1]
		default:
			if g.nslots%2 != 0 {
				g.nslots++
			}
			offset = 8 * g.nslots
			g.nslots += 2
		}
	} else if s.isFloat {
		g.usedFloat = true
		switch {
		case len(g.freeCalleeV) > 0:
			r, g.freeCalleeV = g.freeCalleeV[len(g.freeCalleeV)-1], g.freeCalleeV[:len(g.freeCalleeV)-1]
		case g.usedCalleeV < vecCalleeHigh-vecCalleeLow+1:
			r = vecBase + vecCalleeLow + g.usedCalleeV
			g.usedCalleeV++
		case len(g.freeSlots8) > 0:
			offset, g.freeSlots8 = g.freeSlots8[len(g.freeSlots8)-1], g.freeSlots8[:len(g.freeSlots8)-1]
		default:
			offset = 8 * g.nslots
			g.nslots++
		}
	} else if !g.hasCalls && len(g.leafHomes) > 0 {
		r = g.leafHomes[0]
		g.leafHomes = g.leafHomes[1:]
		g.homesUsed[r] = true
	} else if g.lv != nil && len(g.callerHomes) > 0 && !g.lv.crossing(name) {
		// Never live across a call: a caller-saved home costs nothing.
		r = g.callerHomes[0]
		g.callerHomes = g.callerHomes[1:]
		g.homesUsed[r] = true
	} else {
		switch {
		case len(g.freeCallee) > 0:
			r, g.freeCallee = g.freeCallee[len(g.freeCallee)-1], g.freeCallee[:len(g.freeCallee)-1]
		case g.usedCallee < calleeHigh-calleeLow+1:
			r = calleeLow + g.usedCallee
			g.usedCallee++
		case len(g.licmReserve) > 0:
			// The loop-invariant pass's reserve yields to a variable that
			// would otherwise take a caller-saved home or a slot.
			r, _ = g.reclaimReserve()
		case len(g.callerHomes) > 0:
			r = g.callerHomes[0]
			g.callerHomes = g.callerHomes[1:]
			g.homesUsed[r] = true
			g.pressure = true
		case len(g.freeSlots8) > 0:
			g.pressure = true
			offset, g.freeSlots8 = g.freeSlots8[len(g.freeSlots8)-1], g.freeSlots8[:len(g.freeSlots8)-1]
		default:
			g.pressure = true
			offset = 8 * g.nslots
			g.nslots++
		}
	}
	g.slots[name], g.types[name], g.regs[name] = offset, s, r
	g.scopes[len(g.scopes)-1][name] = slotBinding{offset: offset, typ: s, reg: r}
	g.noteLoopHomes(r)
	return offset
}

// vectorHomePool is the pool of vector homes for a calling function
// (Lane.VectorHomes), built on first demand from the caller-saved vector
// registers beyond what the deepest expression (vecTempReserve) and the
// widest call's vector arguments need as scratch; its size.
func (g *generator) vectorHomePool() int {
	if !g.vectorHomes || g.rvLane || !g.hasCalls {
		return 0
	}
	if !g.vecPoolBuilt {
		g.vecPoolBuilt = true
		reserve := vecTempReserve + g.maxVectorArgs(g.fn.Body)
		if n := len(g.freeF) - reserve; n > 0 {
			g.callerHomesV = append(g.callerHomesV, g.freeF[:n]...)
			g.freeF = g.freeF[n:]
		}
	}
	return len(g.callerHomesV)
}

// leafVectorPool is the pool of a leaf's argument-register vector homes
// (Lane.VectorHomes), built on first demand: v1–v7 past the vector and
// float parameters, which arrive in v0 upward; its size.
func (g *generator) leafVectorPool() int {
	if !g.vectorHomes || g.rvLane || g.hasCalls {
		return 0
	}
	if !g.leafPoolBuilt {
		g.leafPoolBuilt = true
		params := 0
		for _, p := range g.fn.Parameters {
			if p != nil {
				if s, ok := scalarOf(p.Type); ok && (s.isVec || s.isFloat) {
					params++
				}
			}
		}
		for r := params; r <= 7; r++ {
			if r == 0 {
				continue
			}
			g.leafHomesV = append(g.leafHomesV, vecBase+r)
		}
	}
	return len(g.leafHomesV)
}

// releaseVectorHome returns a vector register home to the pool it came
// from: a caller-saved one (v16–v31) to the calling function's home pool
// or a leaf's scratch, a callee-saved one (v8–v15) to freeCalleeV.
func (g *generator) releaseVectorHome(r int) {
	switch {
	case r >= vecBase && r <= vecBase+7 && !g.hasCalls:
		g.leafHomesV = append(g.leafHomesV, r)
	case r >= vecBase+vecScratchLow && r <= vecBase+vecScratchHigh && g.hasCalls:
		g.callerHomesV = append(g.callerHomesV, r)
	case r >= vecBase+vecScratchLow && r <= vecBase+vecScratchHigh:
		g.freeF = append([]int{r}, g.freeF...)
	default:
		g.freeCalleeV = append(g.freeCalleeV, r)
	}
}

// maxVectorArgs is the most vector or float arguments any call in the
// body passes: each is held in a scratch register until moved into
// v0–v7, so that many stay out of the vector home pool.
func (g *generator) maxVectorArgs(body ast.Node) int {
	most := 0
	walk(body, func(n ast.Node) {
		call, isCall := n.(*ast.InvocationExpression)
		if !isCall {
			return
		}
		ident, isIdent := call.Function.(*ast.Identifier)
		if !isIdent {
			return
		}
		callee, known := g.functions[g.calleeName(ident)]
		if !known {
			return
		}
		count := 0
		for _, p := range callee.Parameters {
			if p != nil {
				if s, ok := scalarOf(p.Type); ok && (s.isVec || s.isFloat) {
					count++
				}
			}
		}
		if count > most {
			most = count
		}
	})
	return most
}

// noteLoopHomes adds registers handed out as homes inside the loops being
// lowered to those loops' home sets.
func (g *generator) noteLoopHomes(regs ...int) {
	if g.loopHomes == nil {
		return
	}
	for _, head := range g.openLoops {
		set := g.loopHomes[head]
		if set == nil {
			set = map[int]bool{}
			g.loopHomes[head] = set
		}
		for _, r := range regs {
			if r >= 0 && r < vecBase {
				set[r] = true
			}
		}
	}
}

// liveHomes is the set of general registers the variables in scope live
// in: scalar homes, a span local's base and length registers (the length
// register is also the checker's fact carrier for the span), and a record
// local parked in a register.
func (g *generator) liveHomes() map[int]bool {
	homes := map[int]bool{}
	for _, r := range g.regs {
		if r >= 0 && r < vecBase {
			homes[r] = true
		}
	}
	for _, sp := range g.spans {
		if sp.baseReg >= 0 {
			homes[sp.baseReg] = true
		}
		if sp.lenReg >= 0 {
			homes[sp.lenReg] = true
		}
	}
	for _, rec := range g.records {
		if rec != nil && rec.inReg && rec.reg >= 0 && rec.reg < vecBase {
			homes[rec.reg] = true
		}
	}
	return homes
}

// reclaimReserve hands back the last callee-saved register reserved for
// the loop-invariant pass (docs/spec/94-assembler.md §9 "The register
// budget"): a declaration that would otherwise refuse the body, or fall to
// a slot, takes it, and the pass hoists into what remains. The register
// is already counted in usedCallee, so the prologue saves it either way.
func (g *generator) reclaimReserve() (int, bool) {
	if len(g.licmReserve) == 0 {
		return 0, false
	}
	r := g.licmReserve[len(g.licmReserve)-1]
	g.licmReserve = g.licmReserve[:len(g.licmReserve)-1]
	return r, true
}

// takeCalleePair claims two callee-saved registers for a span local's
// base and length: the unclaimed ones, then the invariant pass's reserve.
func (g *generator) takeCalleePair() (base, length int, ok bool) {
	if g.usedCallee+2 <= calleeHigh-calleeLow+1 {
		base, length = calleeLow+g.usedCallee, calleeLow+g.usedCallee+1
		g.usedCallee += 2
		return base, length, true
	}
	if g.usedCallee+1 <= calleeHigh-calleeLow+1 && len(g.licmReserve) >= 1 {
		base = calleeLow + g.usedCallee
		g.usedCallee++
		length, _ = g.reclaimReserve()
		return base, length, true
	}
	if len(g.licmReserve) >= 2 {
		base, _ = g.reclaimReserve()
		length, _ = g.reclaimReserve()
		return base, length, true
	}
	return 0, 0, false
}

// declareAt binds a scalar variable to a given register: a leaf's
// parameter in the argument register it arrived in.
func (g *generator) declareAt(name string, s scalar, r int) {
	g.homesUsed[r] = true
	g.slots[name], g.types[name], g.regs[name] = -1, s, r
	g.scopes[len(g.scopes)-1][name] = slotBinding{offset: -1, typ: s, reg: r}
	g.noteLoopHomes(r)
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
		if c, isConst := g.constantOf(e.Value); isConst {
			return scalars[c.Type], nil
		}
		if _, typ, isGlobal := g.globalOf(e.Value); isGlobal {
			return typ, nil
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
		if lit, isLiteral := e.Right.(*ast.IntegerLiteral); isLiteral && e.Operator == "-" && hint != nil && !hint.isFloat {
			// A negated literal is one constant typed by its context, as the
			// checker's own literal rule reads it (typechecker.checkPrefixExpression);
			// the negation's recorded width is the operand literal's default
			// type, which a literal beyond `int` does not fit.
			_ = lit
			return *hint, nil
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
		if elem, _, _, isArray := g.staticArrayOf(e.Left); isArray {
			return elem, nil
		}
		sp, err := g.spanOperand(e.Left)
		if err != nil {
			return scalar{}, err
		}
		return sp.elem, nil
	case *ast.InvocationExpression:
		if member, isSimd := simdCallee(e.Function); isSimd {
			return g.simdResultType(member, e.Arguments)
		}
		if member, isLibrary := libraryMember(e); isLibrary {
			return instructionFunctionType(member)
		}
		ident, isIdent := e.Function.(*ast.Identifier)
		if !isIdent {
			return scalar{}, unsupported("a call through a value")
		}
		if ident.Value == "len" && len(e.Arguments) == 1 {
			if _, _, _, isArray := g.staticArrayOf(e.Arguments[0]); isArray {
				return scalars["u32"], nil
			}
			if _, err := g.spanOperand(e.Arguments[0]); err != nil {
				return scalar{}, err
			}
			return scalars["u32"], nil
		}
		if spec, isAtomic := semir.LookupAtomicBuiltin(ident.Value); isAtomic {
			if !spec.ReturnsValue() {
				return scalar{}, unsupported("the atomic %s in value position", ident.Value)
			}
			return g.atomicCellType(e.Arguments[0])
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
		if callee, ok := g.functions[g.calleeName(ident)]; ok {
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
	if g.never {
		// The body ended in an exception return: nothing falls through to
		// a ret (the checker refuses one from a never function).
		if !g.terminated {
			return nil, unsupported("a never function whose body does not end in an exception return")
		}
		if g.usedTrap {
			g.label(trapLabel)
			g.emit("brk", imm(1))
		}
		return g.items, nil
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
		g.emit("ldp", xr(29), xr(30), mem(g.outgoing))
	}
	if frame > 0 {
		g.emit("add", sp(), sp(), imm(frame))
	}
	g.emit("ret")
}

// moveResult places a value in the result register.
func (g *generator) moveResult(r int, s scalar) {
	if s.isVec {
		g.vmove(0, r-vecBase)
		return
	}
	if s.isFloat {
		g.emit("fmov", reg(vecBase, s), reg(r, s))
		return
	}
	g.emit("mov", reg(0, s), reg(r, s))
}

// lowerStatements lowers a block; in a function body the last expression
// statement is the result.
func (g *generator) lowerStatements(stmts []ast.Statement, functionBody bool, retLabel string) error {
	return g.lowerStatementList(stmts, functionBody, retLabel, nil)
}

// lowerStatementsBefore lowers a list whose scope continues into `trailing`
// (a block's result expression): a local the trailing node mentions is
// not released within the list.
func (g *generator) lowerStatementsBefore(stmts []ast.Statement, trailing ast.Node) error {
	return g.lowerStatementList(stmts, false, "", trailing)
}

func (g *generator) lowerStatementList(stmts []ast.Statement, functionBody bool, retLabel string, trailing ast.Node) error {
	lastUse := lastUses(stmts, trailing)
	for i, stmt := range stmts {
		last := functionBody && i == len(stmts)-1
		g.line = statementLine(stmt)
		if err := g.lowerStatement(stmt, last, retLabel); err != nil {
			return err
		}
		g.releaseDead(lastUse, i)
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

// lowerStatement lowers one statement of a block; last marks the function
// body's result statement.
func (g *generator) lowerStatement(stmt ast.Statement, last bool, retLabel string) error {
	switch s := stmt.(type) {
	case *ast.VariableDeclaration:
		if elem, length, isArray := arrayOf(s.Type); isArray {
			if err := g.lowerArrayDeclaration(s, elem, length); err != nil {
				return err
			}
			return nil
		}
		if s.Type != nil && g.isArrayType(s.Type) {
			_, elemLayout, length, err := g.arrayTypeOf(s.Type)
			if err != nil {
				return err
			}
			if err := g.lowerRecordArrayDeclaration(s, elemLayout, length); err != nil {
				return err
			}
			return nil
		}
		if typeName, isRecord := g.recordTypeName(s.Type); isRecord {
			if err := g.lowerRecordDeclaration(s, typeName); err != nil {
				return err
			}
			return nil
		}
		if target, isSpan := g.spanTypeOf(s.Type); isSpan {
			if err := g.lowerSpanDeclaration(s, target); err != nil {
				return err
			}
			return nil
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
		g.assignVar(s.Name.Value, r)
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
			return nil
		}
		if arr, isArray := g.arrays[s.Name.Value]; isArray {
			// `h = f(h)`: a whole owned array of scalars assigned as a value.
			dst, isValue := g.arrayAsRecord(arr)
			if !isValue {
				return unsupported("an assignment to the array %s", s.Name.Value)
			}
			if dst.readOnly {
				return unsupported("an assignment to the read-only array %s", s.Name.Value)
			}
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
			return nil
		}
		typ, ok := g.types[s.Name.Value]
		if !ok {
			global, globalType, isGlobal := g.globalOf(s.Name.Value)
			if !isGlobal {
				return unsupported("an assignment to %s", s.Name.Value)
			}
			// `G = e`: the global's cell written through its address.
			r, err := g.expr(s.Value, &globalType)
			if err != nil {
				return err
			}
			if err := g.globalStore(s.Name.Value, global, globalType, r); err != nil {
				return err
			}
			g.release(r)
			return nil
		}
		r, err := g.expr(s.Value, &typ)
		if err != nil {
			return err
		}
		g.assignVar(s.Name.Value, r)
		g.killLoopFacts(s.Name.Value)
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
				return nil
			}
			if g.result == nil {
				// A unit function whose last statement is an expression:
				// a call, an assert, or a conditional or match in
				// statement position.
				if match, isMatch := s.Expression.(*ast.MatchExpression); isMatch {
					return g.lowerConditionalStatement(match)
				}
				if err := g.effect(s.Expression); err != nil {
					return err
				}
				return nil
			}
			if err := g.resultExpr(s.Expression); err != nil {
				return err
			}
			return nil
		}
		if match, isMatch := s.Expression.(*ast.MatchExpression); isMatch {
			if err := g.lowerConditionalStatement(match); err != nil {
				return err
			}
			return nil
		}
		if err := g.effect(s.Expression); err != nil {
			return err
		}
	default:
		return unsupported("%T", stmt)
	}
	return nil
}

// effect evaluates an expression for its effects: a call, or assert.
func (g *generator) effect(expr ast.Expression) error {
	call, isCall := expr.(*ast.InvocationExpression)
	if !isCall {
		return unsupported("an expression statement that is not a call")
	}
	if member, isSimd := simdCallee(call.Function); isSimd {
		r, err := g.simdOp(member, call.Arguments)
		if err != nil {
			return err
		}
		if r >= 0 {
			g.release(r)
		}
		return nil
	}
	if member, isLibrary := libraryMember(call); isLibrary {
		return g.instructionEffect(member, call)
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
	if spec, isAtomic := semir.LookupAtomicBuiltin(ident.Value); isAtomic {
		// A store, a fence, or a read-modify-write whose result is dropped.
		r, err := g.atomic(call, spec, true)
		if err != nil {
			return err
		}
		if r >= 0 {
			g.release(r)
		}
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
	if g.loopHomes != nil {
		g.loopHomes[head] = g.liveHomes() // for the loop-invariant pass
		g.openLoops = append(g.openLoops, head)
		defer func() { g.openLoops = g.openLoops[:len(g.openLoops)-1] }()
	}
	if err := g.condition(loop.Condition, end); err != nil {
		return err
	}
	g.loops = append(g.loops, end)
	facts := len(g.loopFacts)
	g.loopFacts = append(g.loopFacts, loopFactsOf(loop.Condition)...)
	g.pushScope()
	err := g.lowerStatements(loop.Body.Statements, false, "")
	g.popScope()
	g.loopFacts = g.loopFacts[:facts]
	g.loops = g.loops[:len(g.loops)-1]
	if err != nil {
		return err
	}
	g.emit("b", asm.Symbol{Name: head})
	g.label(end)
	return nil
}

func (g *generator) lowerIf(s *ast.IfStatement) error {
	if arms, final, isChain := ifArms(s); isChain {
		if chain, ok := g.recognizeSelectChain(arms, final); ok {
			return g.lowerSelectChain(chain)
		}
	}
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
	whenTrue, whenFalse, ok := statementConditional(match)
	if !ok {
		return g.lowerMatch(match, g.lowerArm)
	}
	// If-conversion (nativegen/select.go): a chain over one comparison
	// whose arms only assign lowers as compare and select.
	if arms, final, isChain := conditionalArms(match); isChain {
		if chain, ok := g.recognizeSelectChain(arms, final); ok {
			return g.lowerSelectChain(chain)
		}
	}
	elseLabel, end := g.newLabel("else"), g.newLabel("endif")
	if err := g.condition(match.Scrutinee, elseLabel); err != nil {
		return err
	}
	if err := g.lowerArm(whenTrue); err != nil {
		return err
	}
	if whenFalse == nil {
		// `cond ? { ... }`: nothing on the other path.
		g.label(elseLabel)
		return nil
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
	if arm == nil {
		return nil
	}
	if chained, isMatch := arm.(*ast.MatchExpression); isMatch {
		// `c1 ? { … } | c2 ? { … } | { … }`: the else arm is a conditional.
		return g.lowerConditionalStatement(chained)
	}
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
	// Selection in condition position (docs/spec/94-assembler.md §9 "Condition
	// selection"): a negation inverts the branch instead of materializing
	// a Bool, and a Bool variable in a register is tested where it lives.
	switch e := expr.(type) {
	case *ast.PrefixExpression:
		if e.Operator == "!" {
			return g.conditionBranch(e.Right, target, !jumpIfFalse)
		}
	case *ast.Identifier:
		if v, inReg := g.regs[e.Value]; inReg && v >= 0 && v < vecBase {
			if t, ok := g.types[e.Value]; ok && t.isBool {
				if jumpIfFalse {
					g.emit("cbz", wr(v), asm.Symbol{Name: target})
				} else {
					g.emit("cbnz", wr(v), asm.Symbol{Name: target})
				}
				return nil
			}
		}
	}
	if infix, ok := expr.(*ast.InfixExpression); ok {
		// Short-circuit connectives branch per operand, so each comparison
		// keeps the `cmp; b.cond` shape whose facts the checker reads
		// (a loop guard `len(v) >= N && i <= len(v) - N` proves the body's
		// vector accesses).
		switch infix.Operator {
		case "&&":
			if jumpIfFalse {
				if err := g.conditionBranch(infix.Left, target, true); err != nil {
					return err
				}
				return g.conditionBranch(infix.Right, target, true)
			}
			skip := g.newLabel("and")
			if err := g.conditionBranch(infix.Left, skip, true); err != nil {
				return err
			}
			if err := g.conditionBranch(infix.Right, target, false); err != nil {
				return err
			}
			g.label(skip)
			return nil
		case "||":
			if !jumpIfFalse {
				if err := g.conditionBranch(infix.Left, target, false); err != nil {
					return err
				}
				return g.conditionBranch(infix.Right, target, false)
			}
			skip := g.newLabel("or")
			if err := g.conditionBranch(infix.Left, skip, false); err != nil {
				return err
			}
			if err := g.conditionBranch(infix.Right, target, true); err != nil {
				return err
			}
			g.label(skip)
			return nil
		}
		if codes, isComparison := conditionCodes[infix.Operator]; isComparison {
			if operand, err := g.operandType(infix); err == nil && !operand.isFloat {
				left, leftOK := g.simpleOperand(infix.Left, operand, false)
				right, rightOK := g.simpleOperand(infix.Right, operand, true)
				if leftOK && !rightOK {
					// A named constant, or a folded conversion: the compare
					// immediate, as a literal's.
					if c, isConst := g.constantOperand(infix.Right, operand); isConst && c < 4096 {
						right, rightOK = imm(int64(c)), true
					}
				}
				computed := -1
				if leftOK && !rightOK {
					// A computed right operand (`len(v) - u32(N)`): into a
					// scratch, then the same compare-and-branch.
					r, err := g.expr(infix.Right, &operand)
					if err != nil {
						return err
					}
					computed, right, rightOK = r, reg(r, operand), true
				}
				if leftOK && rightOK {
					code := codes[0]
					if operand.signed {
						code = codes[1]
					}
					if jumpIfFalse {
						code = inverseCondition[code]
					}
					// The compare a conditional chain's guard made stands at
					// the else label: the same operands (variables in their
					// homes, a length register, an immediate) need no second
					// compare (Lane.ReuseFlags).
					compare := fmt.Sprintf("%v %v", left, right)
					if g.reuseFlags && g.liveFlags != "" && g.liveFlags == compare {
						g.reused++
					} else {
						g.emit("cmp", left, right)
					}
					g.branchFlags(code, target, compare)
					if computed >= 0 {
						g.release(computed)
					}
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
		if c, isConst := g.constantOf(e.Value); isConst {
			g.constant(r, c.Value, typ)
			return r, nil
		}
		if global, globalType, isGlobal := g.globalOf(e.Value); isGlobal {
			if globalType != typ {
				return 0, unsupported("the global %s (%s) read as %s", e.Value, globalType.name, typ.name)
			}
			if err := g.globalLoad(e.Value, global, typ, r); err != nil {
				return 0, err
			}
			return r, nil
		}
		if held, ok := g.forwardedSlot(e.Value); ok {
			// The value just stored to the variable's slot is still in the
			// register that stored it: read it from there (or it is r).
			if held != r {
				g.emit(moveOf(typ), reg(r, typ), reg(held, typ))
			}
			g.defined[r] = true // it holds the value: a call in between spills it
			return r, nil
		}
		g.put(g.loadVar(e.Value, r))
		return r, nil
	case *ast.InfixExpression:
		return g.infix(e, typ)
	case *ast.PrefixExpression:
		return g.prefix(e, typ)
	case *ast.IndexExpression:
		return g.element(e)
	case *ast.InvocationExpression:
		if member, isSimd := simdCallee(e.Function); isSimd {
			r, err := g.simdOp(member, e.Arguments)
			if err != nil {
				return 0, err
			}
			if r < 0 {
				return 0, unsupported("simd.%s in value position", member)
			}
			return r, nil
		}
		if member, isLibrary := libraryMember(e); isLibrary {
			return g.instructionValue(member, e, typ)
		}
		ident, isIdent := e.Function.(*ast.Identifier)
		if !isIdent {
			return 0, unsupported("a call through a value")
		}
		if ident.Value == "len" && len(e.Arguments) == 1 {
			r, err := g.alloc(scalars["u32"])
			if err != nil {
				return 0, err
			}
			if _, _, length, isArray := g.staticArrayOf(e.Arguments[0]); isArray {
				g.constant(r, uint64(length), scalars["u32"])
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
		if spec, isAtomic := semir.LookupAtomicBuiltin(ident.Value); isAtomic {
			return g.atomic(e, spec, false)
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
		es, ok := stmts[len(stmts)-1].(*ast.ExpressionStatement)
		if !ok {
			return 0, unsupported("a block whose last statement is not an expression")
		}
		// The result still mentions the block's locals: their last use is
		// past the statements lowered here.
		if err := g.lowerStatementsBefore(stmts[:len(stmts)-1], es); err != nil {
			return 0, err
		}
		return g.expr(es.Expression, &typ)
	}
	if _, isQuantifier := expr.(*ast.QuantifierExpression); isQuantifier {
		// A bounded quantifier enumerates a domain: the C backend's loop
		// realizes it (docs/spec/10-syntax.md section 3e).
		return 0, unsupported("a bounded quantifier")
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
		g.put(it)
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
	if !g.rvLane {
		// The rv64 lane hooks the same recognizer in its own infix
		// (rvFusedWordLoad); this emission is the AArch64 idiom.
		if w, isWord := g.recognizeWordAssembly(e, typ); isWord {
			return g.fusedWordLoad(w, typ) // nativegen/word_fusion.go
		}
		if k, isConst := constantValue(e); isConst && !typ.isBool && !typ.isFloat && !typ.isVec && !typ.signed {
			// A sum or product of literals (`u32(8) + u32(8)`, an inlined
			// helper's constant guard) is its folded constant: a compare
			// against it then takes the immediate form the seam checker
			// reads a minimum length off (`cmp wL, #16; b.lo`).
			r, err := g.alloc(typ)
			if err != nil {
				return 0, err
			}
			g.constant(r, uint64(k)&mask64(typ.bits), typ)
			return r, nil
		}
	}
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
		if !g.retargetLast(l, out) {
			g.emit("mov", wr(out), wr(l))
		}
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
		if !g.retargetLast(rr, out) {
			g.emit("mov", wr(out), wr(rr))
		}
		g.release(rr)
		g.label(end)
		return out, nil
	case "==", "!=", "<", "<=", ">", ">=":
		operand, err := g.operandType(e)
		if err != nil {
			return 0, err
		}
		if operand.isFloat {
			l, err := g.expr(e.Left, &operand)
			if err != nil {
				return 0, err
			}
			r, err := g.expr(e.Right, &operand)
			if err != nil {
				return 0, err
			}
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
		// The operands where they are: a variable in its own register, a
		// constant as the immediate `cmp` takes; the result in the left
		// operand's scratch, or a fresh one when the left is a variable.
		l, lfixed, err := g.operand(e.Left, operand)
		if err != nil {
			return 0, err
		}
		right, r, rfixed, err := g.sourceOperand(e.Right, operand, "cmp")
		if err != nil {
			return 0, err
		}
		g.emit("cmp", reg(l, operand), right)
		if r >= 0 && !rfixed {
			g.release(r)
		}
		out := l
		if lfixed {
			if out, err = g.alloc(scalars["Bool"]); err != nil {
				return 0, err
			}
		}
		code := conditionCodes[e.Operator][0]
		if operand.signed {
			code = conditionCodes[e.Operator][1]
		}
		g.emit("cset", wr(out), asm.Condition{Code: code})
		return out, nil
	}
	if mnemonic, direct := directArithmetic[e.Operator]; direct && !typ.isFloat && !typ.isVec && !g.reducesMultiply(e, typ) {
		return g.directInfix(e, typ, mnemonic)
	}
	if (e.Operator == "<<" || e.Operator == ">>") && !typ.signed && !typ.isFloat && !typ.isVec {
		if count, isConst := constantValue(e.Right); isConst && count >= 0 && count < int64(typ.bits) {
			// A constant-count shift reads its operand where it lies.
			l, lfixed, err := g.operand(e.Left, typ)
			if err != nil {
				return 0, err
			}
			out := l
			if lfixed {
				if out, err = g.alloc(typ); err != nil {
					return 0, err
				}
			}
			op := "lsl"
			if e.Operator == ">>" {
				op = "lsr"
			}
			g.emit(op, reg(out, typ), reg(l, typ), imm(count))
			// An unsigned value shifted right stays inside its width: no
			// mask after `lsr`.
			if op != "lsr" {
				g.normalize(out, typ)
			}
			return out, nil
		}
	}
	if typ.isFloat {
		// A float local in a register home is read in place, as an
		// integer one is (operand); the result then needs its own
		// register, which assignVar may rename to the home (retargetLast)
		// — `total = total + x` becomes one fadd into the home.
		l, lfixed, err := g.operand(e.Left, typ)
		if err != nil {
			return 0, err
		}
		r, rfixed := l, true
		if !g.sameOperand(e) {
			if r, rfixed, err = g.operand(e.Right, typ); err != nil {
				return 0, err
			}
		}
		op, ok := map[string]string{"+": "fadd", "-": "fsub", "*": "fmul", "/": "fdiv"}[e.Operator]
		if !ok {
			return 0, unsupported("operator %s on %s", e.Operator, typ.name)
		}
		out := l
		if lfixed {
			if out, err = g.alloc(typ); err != nil {
				return 0, err
			}
		}
		g.emit(op, reg(out, typ), reg(l, typ), reg(r, typ))
		if !rfixed {
			g.release(r)
		}
		return out, nil
	}
	// A strength-reduced power of two reads its operand where it lies:
	// `lsl w10, w23, #9` for `mid * u32(512)`, not a copy then the shift
	// in place (docs/spec/90-backend.md §16; the general path below keeps
	// the other constants).
	if g.strength && !g.rvLane && !typ.isFloat && !typ.isVec && (e.Operator == "*" || e.Operator == "/" || e.Operator == "%") {
		if c, isConst := g.constantOperand(e.Right, typ); isConst {
			c &= mask64(typ.bits)
			power := c != 0 && c&(c-1) == 0
			k := int64(bits.TrailingZeros64(c))
			if power && (e.Operator == "*" && k > 0 || e.Operator != "*" && !typ.signed) {
				l, lfixed, err := g.operand(e.Left, typ)
				if err != nil {
					return 0, err
				}
				out := l
				if lfixed {
					if out, err = g.alloc(typ); err != nil {
						return 0, err
					}
				}
				switch {
				case e.Operator == "*":
					g.emit("lsl", reg(out, typ), reg(l, typ), imm(k))
					g.normalize(out, typ)
				case e.Operator == "/" && k > 0:
					g.emit("lsr", reg(out, typ), reg(l, typ), imm(k))
				case e.Operator == "/":
					if out != l {
						g.emit("mov", reg(out, typ), reg(l, typ))
					}
				case k == 0:
					g.emit("movz", reg(out, typ), imm(0))
				default:
					g.emit("and", reg(out, typ), reg(l, typ), imm(int64(c-1)))
				}
				g.reduced++
				return out, nil
			}
		}
	}
	l, err := g.expr(e.Left, &typ)
	if err != nil {
		return 0, err
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
	// Strength reduction (Lane.Strength, docs/spec/90-backend.md §16): a
	// constant right operand of *, /, or % lowers to the instruction the
	// constant licenses — a power of two as a shift (or a mask for %), a
	// nonzero divisor without the zero test — on the AArch64 lane. The
	// verifier proves the body against the Oak semantics or the compiler
	// lowers it again without the reduction (compiler/native_bodies.go).
	if g.strength && !g.rvLane && !typ.isFloat && (e.Operator == "*" || e.Operator == "/" || e.Operator == "%") {
		if c, isConst := g.constantOperand(e.Right, typ); isConst {
			c &= mask64(typ.bits)
			power := c != 0 && c&(c-1) == 0
			k := int64(bits.TrailingZeros64(c))
			switch {
			case e.Operator == "*" && power && k > 0:
				g.emit("lsl", reg(l, typ), reg(l, typ), imm(k))
				g.reduced++
				g.normalize(l, typ)
				return l, nil
			case e.Operator == "/" && power && !typ.signed:
				if k > 0 {
					g.emit("lsr", reg(l, typ), reg(l, typ), imm(k))
				}
				g.reduced++
				g.normalize(l, typ)
				return l, nil
			case e.Operator == "%" && power && !typ.signed:
				if k == 0 {
					g.emit("movz", reg(l, typ), imm(0))
				} else {
					g.emit("and", reg(l, typ), reg(l, typ), imm(int64(c-1)))
				}
				g.reduced++
				g.normalize(l, typ)
				return l, nil
			case (e.Operator == "/" || e.Operator == "%") && c != 0:
				// A nonzero constant divisor cannot trap: the quotient
				// or remainder without the zero test.
				r, err := g.expr(e.Right, &typ)
				if err != nil {
					return 0, err
				}
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
				g.reduced++
				g.release(r)
				g.normalize(l, typ)
				return l, nil
			}
		}
	}
	// The same pure expression on both sides (`x * x`) is evaluated once.
	same := g.sameOperand(e)
	r := l
	if !same {
		var err error
		if r, err = g.expr(e.Right, &typ); err != nil {
			return 0, err
		}
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
	if !same {
		g.release(r)
	}
	g.normalize(l, typ)
	return l, nil
}

// reducesMultiply reports a multiplication by a constant power of two
// under Lane.Strength: it lowers to a shift in the general path rather
// than to a mul of a materialized constant in the direct one.
func (g *generator) reducesMultiply(e *ast.InfixExpression, typ scalar) bool {
	if !g.strength || g.rvLane || e.Operator != "*" {
		return false
	}
	c, isConst := g.constantOperand(e.Right, typ)
	c &= mask64(typ.bits)
	return isConst && c > 1 && c&(c-1) == 0
}

// directArithmetic names the operations whose operands are read where they
// lie (directInfix): a variable in its callee-saved register, a constant
// as an immediate where the instruction's field admits it.
var directArithmetic = map[string]string{"+": "add", "-": "sub", "*": "mul", "&": "and", "|": "orr", "^": "eor"}

// commutative marks the operations whose constant operand may move to the
// right, where the immediate field is.
var commutative = map[string]bool{"add": true, "mul": true, "and": true, "orr": true, "eor": true}

// directInfix lowers `a op b` with the operands in place: `add w9, w19,
// w20` for two variables, `add w9, w19, #1` for a constant right operand,
// instead of moving each into a scratch register first. The result lands
// in the left operand's scratch when it has one, otherwise in a fresh one
// (so the scratch pressure never exceeds the moving form's). The semantics
// are the moving form's: the checker reads the variable registers as any
// source, and the verifier's terms are the same.
func (g *generator) directInfix(e *ast.InfixExpression, typ scalar, mnemonic string) (int, error) {
	left, right := e.Left, e.Right
	if _, leftConst := g.constantOperand(left, typ); leftConst && commutative[mnemonic] {
		if _, rightConst := g.constantOperand(right, typ); !rightConst {
			left, right = right, left
		}
	}
	l, lfixed, err := g.operand(left, typ)
	if err != nil {
		return 0, err
	}
	src, r, rfixed, err := g.sourceOperand(right, typ, mnemonic)
	if err != nil {
		return 0, err
	}
	out := l
	if lfixed {
		if out, err = g.alloc(typ); err != nil {
			return 0, err
		}
	}
	g.emit(mnemonic, reg(out, typ), reg(l, typ), src)
	if r >= 0 && !rfixed {
		g.release(r)
	}
	// A bitwise operation with a constant inside the type's mask leaves a
	// normalized unsigned operand normalized: no mask after it.
	if c, isConst := g.constantOperand(right, typ); !(isConst && !typ.signed && (mnemonic == "and" || mnemonic == "orr" || mnemonic == "eor") && c <= mask64(typ.bits)) {
		g.normalize(out, typ)
	}
	return out, nil
}

// operand evaluates an expression as a source operand: a variable of the
// type in its callee-saved register is read there (fixed: the caller never
// releases it); anything else evaluates into a fresh scratch register.
// sameOperand reports a binary operation whose two operands are the same
// pure expression (`a[i] * a[i]`: the square): evaluated once, the one
// register serves both sides. Pure means no call to a program function
// (a call could observe or change what the second evaluation reads).
func (g *generator) sameOperand(e *ast.InfixExpression) bool {
	if e.Left == nil || e.Right == nil {
		return false
	}
	if _, isLiteral := e.Left.(*ast.IntegerLiteral); isLiteral {
		return false
	}
	return e.Left.String() == e.Right.String() && !g.callsProgramFunction(e.Left)
}

func (g *generator) operand(expr ast.Expression, typ scalar) (int, bool, error) {
	if ident, isIdent := expr.(*ast.Identifier); isIdent && !typ.isVec {
		if v, inReg := g.regs[ident.Value]; inReg && v >= 0 {
			if t, ok := g.types[ident.Value]; ok && t == typ {
				return v, true, nil
			}
		}
	}
	if index, isIndex := expr.(*ast.IndexExpression); isIndex && !typ.isVec {
		if hidden, elem, isScalar := g.scalarElement(index); isScalar && elem == typ {
			if v, inReg := g.regs[hidden]; inReg && v >= 0 {
				return v, true, nil
			}
		}
	}
	// A span's length is read from its length register (`sub w9, w20, #4`
	// for `len(v) - u32(4)`, not a copy then the subtraction in place).
	if call, isCall := expr.(*ast.InvocationExpression); isCall && !typ.wide() && !typ.isFloat && !typ.isVec && !typ.signed && typ.bits == 32 && len(call.Arguments) == 1 {
		if ident, isIdent := call.Function.(*ast.Identifier); isIdent && ident.Value == "len" {
			if sp, err := g.spanOperand(call.Arguments[0]); err == nil && sp.lenReg >= 0 {
				return sp.lenReg, true, nil
			}
		}
	}
	r, err := g.expr(expr, &typ)
	return r, false, err
}

// sourceOperand is the right operand of an instruction: an immediate when
// the expression is a constant the instruction's field admits (a 12-bit
// unsigned for add/sub/cmp, a bitmask immediate for and/orr/eor), else a
// register from operand (r < 0 when an immediate was spelled).
func (g *generator) sourceOperand(expr ast.Expression, typ scalar, mnemonic string) (asm.Operand, int, bool, error) {
	if v, isConst := g.constantOperand(expr, typ); isConst {
		switch mnemonic {
		case "add", "sub", "cmp":
			if v < 4096 {
				return imm(int64(v)), -1, false, nil
			}
		case "and", "orr", "eor":
			width := 32
			if typ.wide() {
				width = 64
			}
			if asm.LogicalImmediate(v&mask64(width), width) {
				return imm(int64(v & mask64(width))), -1, false, nil
			}
		}
	}
	r, fixed, err := g.operand(expr, typ)
	if err != nil {
		return nil, 0, false, err
	}
	return reg(r, typ), r, fixed, nil
}

// constantOperand reads a constant expression's value at a type: a
// literal, a widening constructor over one, or a constant global.
func (g *generator) constantOperand(expr ast.Expression, typ scalar) (uint64, bool) {
	if v, ok := constantValue(expr); ok && v >= 0 {
		return uint64(v), true
	}
	if ident, isIdent := expr.(*ast.Identifier); isIdent {
		if c, isConst := g.constantOf(ident.Value); isConst && !typ.isFloat {
			return c.Value & mask64(scalars[c.Type].bits), true
		}
	}
	return 0, false
}

func mask64(bits int) uint64 {
	if bits >= 64 {
		return ^uint64(0)
	}
	return uint64(1)<<uint(bits) - 1
}

// assignVar stores a computed value into a variable and releases the
// scratch: when the value's producing instruction is the last one emitted
// and the variable lives in a register, the instruction is retargeted to
// write the variable directly (`add w19, w19, #1` instead of `add w9, w19,
// #1; mov w19, w9`); otherwise the move or store as before.
func (g *generator) assignVar(name string, r int) {
	if v, inReg := g.regs[name]; inReg && v >= 0 && (r < vecBase) == (v < vecBase) && g.retargetLast(r, v) {
		g.release(r)
		return
	}
	g.put(g.storeVar(name, r))
	g.release(r)
}

// retargetable names the instructions whose destination may be renamed
// without changing their meaning: they read their sources only (movk reads
// its destination, the exclusives write a status).
var retargetable = map[string]bool{"movi": true, "umin": true, "umax": true, "cmeq": true, "uqsub": true, "ushr": true, "sshr": true, "fmin": true, "fmax": true, "dup": true, "tbl": true, "ext": true, "cnt": true, "fadd": true, "fsub": true, "fmul": true, "fdiv": true, "fneg": true, "fabs": true, "fsqrt": true, "fmov": true, "scvtf": true, "ucvtf": true, "fcvt": true, "add": true, "sub": true, "mul": true, "and": true, "orr": true, "eor": true, "lsl": true, "lsr": true, "asr": true, "udiv": true, "sdiv": true, "msub": true, "madd": true, "mov": true, "movz": true, "mvn": true, "neg": true, "cset": true, "csel": true, "sxtb": true, "sxth": true, "uxtb": true, "uxth": true, "ldr": true, "ldrb": true, "ldrh": true, "ldrsb": true, "ldrsh": true, "ldrsw": true, "clz": true, "rbit": true, "rev": true, "rev16": true, "rev32": true}

// retargetLast rewrites the last emitted instruction's destination from
// scratch register r to register v, when that instruction is the one that
// wrote r and may be renamed.
func (g *generator) retargetLast(r, v int) bool {
	n := len(g.items)
	if n == 0 {
		return false
	}
	ins, isIns := g.items[n-1].(asm.Instruction)
	if !isIns || !retargetable[ins.Mnemonic] || len(ins.Operands) == 0 {
		return false
	}
	dst, isReg := ins.Operands[0].(asm.Register)
	if !isReg {
		return false
	}
	renamed := dst
	switch {
	case (dst.Class == asm.ClassW || dst.Class == asm.ClassX) && dst.Num == r && v < vecBase:
		renamed.Num = v
		renamed.Text = dst.Text[:1] + strconv.Itoa(v)
	case dst.Class == asm.ClassV && (dst.Vec == "s" || dst.Vec == "d") && dst.Lane < 0 && dst.Num == r-vecBase && v >= vecBase:
		// A float scratch in its s or d view: the home keeps the view.
		renamed.Num = v - vecBase
		renamed.Text = dst.Vec + strconv.Itoa(v-vecBase)
	case dst.Class == asm.ClassV && dst.Vec == "q" && dst.Lane < 0 && dst.Num == r-vecBase && v >= vecBase:
		// A vector loaded whole (`ldr q16`): the home takes the load.
		renamed.Num = v - vecBase
		renamed.Text = "q" + strconv.Itoa(v-vecBase)
	case dst.Class == asm.ClassV && isArrangement(dst.Vec) && dst.Lane < 0 && dst.Num == r-vecBase && v >= vecBase:
		// A vector scratch in an arrangement (`v16.16b`): the operation
		// writes the variable's home directly.
		renamed.Num = v - vecBase
		renamed.Text = "v" + strconv.Itoa(v-vecBase) + "." + dst.Vec
	default:
		return false
	}
	operands := append([]asm.Operand{renamed}, ins.Operands[1:]...)
	ins.Operands = operands
	g.items[n-1] = ins
	return true
}

// isArrangement reports a whole-vector arrangement (`16b`, `8h`, `4s`,
// `2d`, and the 64-bit halves), never a scalar view or a lane.
func isArrangement(vec string) bool {
	switch vec {
	case "16b", "8b", "8h", "4h", "4s", "2s", "2d", "1d":
		return true
	}
	return false
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
	case *ast.InfixExpression:
		// A sum or product of two literals converted to one unsigned type,
		// `u32(8) + u32(8)` (an inlined helper's guard once its literal
		// argument substitutes, compiler/inline.go), folds when the result
		// fits the type, so the fold is exact whatever the context;
		// `u8(200) + u8(100)` wraps at run time and is left to the
		// instructions. The extents checker and the Oak-side lowering fold
		// the same shape by the same rule.
		return foldLiteralPair(e, constantValue)
	case *ast.InvocationExpression:
		if ident, ok := e.Function.(*ast.Identifier); ok && len(e.Arguments) == 1 {
			if _, isConv := scalars[ident.Value]; isConv {
				return constantValue(e.Arguments[0])
			}
		}
	}
	return 0, false
}

// foldLiteralPair folds `T(a) + T(b)` and `T(a) * T(b)` for an unsigned
// integer type T when the result fits T, reading each side with value; a
// wrapping result, a signed or mixed type, or a bare literal is not folded.
func foldLiteralPair(e *ast.InfixExpression, value func(ast.Expression) (int64, bool)) (int64, bool) {
	if e.Operator != "+" && e.Operator != "*" {
		return 0, false
	}
	typeName := ""
	for _, side := range []ast.Expression{e.Left, e.Right} {
		call, isCall := side.(*ast.InvocationExpression)
		if !isCall || len(call.Arguments) != 1 {
			return 0, false
		}
		conv, isIdent := call.Function.(*ast.Identifier)
		if !isIdent || (typeName != "" && conv.Value != typeName) {
			return 0, false
		}
		typeName = conv.Value
	}
	typ, isScalar := scalars[typeName]
	if !isScalar || typ.signed || typ.isFloat || typ.isBool || typ.isVec || typ.bits > 64 {
		return 0, false
	}
	left, leftConst := value(e.Left)
	right, rightConst := value(e.Right)
	if !leftConst || !rightConst || left < 0 || right < 0 {
		return 0, false
	}
	var result uint64
	if e.Operator == "+" {
		result = uint64(left) + uint64(right)
	} else {
		if right != 0 && uint64(left) > ^uint64(0)/uint64(right) {
			return 0, false
		}
		result = uint64(left) * uint64(right)
	}
	if typ.bits < 64 && result >= uint64(1)<<uint(typ.bits) || result > 1<<62 {
		return 0, false
	}
	return int64(result), true
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
	// The vector file serves floats and the fixed vectors alike: a function
	// mentioning either reserves the d8–d15 save area.
	isFloatType := func(expr ast.Expression) bool {
		if s, ok := scalarOf(expr); ok && (s.isFloat || s.isVec) {
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
			if _, isSimd := simdCallee(e.Function); isSimd {
				found = true
			}
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
	callee, ok := g.functions[g.calleeName(ident)]
	if !ok {
		return 0, unsupported("a call to %s", ident.Value)
	}
	if len(e.Arguments) != len(callee.Parameters) {
		return 0, unsupported("a call to %s with %d arguments", ident.Value, len(e.Arguments))
	}
	var resultType *scalar
	if callee.ReturnType != nil && callee.ReturnType.String() != "()" {
		if _, isValue, _ := g.valueLayoutOf(callee.ReturnType); isValue {
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
		fixed bool // the registers are a parked span's or a variable's home, never released
		// A constant scalar is materialized straight into its place at the
		// move; an argument already stored to its stack slot needs nothing.
		isConst  bool
		constant uint64
		stored   bool
	}
	// The integer-class arguments' places, from the callee's signature
	// (asm/abi.go): known before the arguments are evaluated, so one bound
	// for the stack is stored as soon as it is computed and holds no
	// scratch register across the arguments after it.
	var classes []asm.ArgClass
	var intArgs []int
	for i, p := range callee.Parameters {
		if s, ok := scalarOf(p.Type); ok && (s.isFloat || s.isVec) {
			continue
		}
		class, ok := g.argClassOf(p.Type)
		if !ok {
			return 0, unsupported("a call to %s (parameter %s: %s)", ident.Value, p.Name.Value, p.Type.String())
		}
		classes = append(classes, class)
		intArgs = append(intArgs, i)
	}
	places, stackBytes := asm.LayoutArguments(classes, g.packedStack)
	if stackBytes > g.outgoing {
		return 0, unsupported("a call to %s: %d bytes of stack arguments, more than the frame reserved", ident.Value, stackBytes)
	}
	placeOf := map[int]asm.ArgPlace{}
	for k, i := range intArgs {
		placeOf[i] = places[k]
	}
	var args []argument
	// push records an argument; one bound for the stack in scratch
	// registers is stored to its slot now and its registers released.
	push := func(i int, a argument) {
		place := placeOf[i]
		if place.OnStack && !a.fixed && !a.isConst && len(a.regs) > 0 {
			for j, r := range a.regs {
				g.emit(stackStoreOf(a.types[j], len(a.regs) == 1), reg(r, a.types[j]), mem(place.Offset+int64(8*j)))
				g.release(r)
			}
			a.regs, a.stored = nil, true
		}
		args = append(args, a)
	}
	for i, arg := range e.Arguments {
		p := callee.Parameters[i]
		if p.Variadic {
			return 0, unsupported("a call to %s (parameter %s is variadic)", ident.Value, p.Name.Value)
		}
		if s, ok := scalarOf(p.Type); ok {
			if !s.isFloat && !s.isVec {
				// A constant, or a variable whose home is no argument
				// register, is read at the move itself: no scratch held.
				if v, isConst := g.constantOperand(arg, s); isConst {
					push(i, argument{types: []scalar{s}, isConst: true, constant: v})
					continue
				}
				if ident, isIdent := arg.(*ast.Identifier); isIdent {
					if v, inReg := g.regs[ident.Value]; inReg && v > 7 && v < vecBase {
						if t, known := g.types[ident.Value]; known && t == s {
							push(i, argument{regs: []int{v}, types: []scalar{s}, fixed: true})
							continue
						}
					}
				}
			}
			r, err := g.expr(arg, &s)
			if err != nil {
				return 0, err
			}
			push(i, argument{regs: []int{r}, types: []scalar{s}})
			continue
		}
		if layout, isValue, err := g.valueLayoutOf(p.Type); isValue {
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
				return 0, unsupported("a call to %s: a %s where %s is expected", ident.Value, rec.layout.name, layout.name)
			}
			if layout.size > 16 && rec.paramRef {
				// An in-place parameter passed on: the same address (the
				// callee copies it if it writes its own; a read-only one
				// reads the caller's memory, which nothing writes meanwhile).
				push(i, argument{regs: []int{rec.reg}, types: []scalar{scalars["u64"]}, fixed: true})
				continue
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
				push(i, argument{regs: []int{base}, types: []scalar{scalars["u64"]}})
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
			push(i, argument{regs: chunks, types: kinds})
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
		push(i, argument{regs: []int{value.baseReg, value.lenReg}, types: []scalar{scalars["u64"], scalars["u32"]}, fixed: named})
	}
	// Variables in caller-saved homes: saved before the argument registers
	// are written (a home may be one of them) and restored after the call.
	homes := g.callerHomesLive(e)
	for _, r := range homes {
		g.emit("str", spillReg(r), g.slotMem(g.spillSlot(r)))
	}
	vector := 0
	for i, arg := range args {
		place := placeOf[i]
		if arg.stored {
			continue
		}
		if arg.isConst {
			typ := arg.types[0]
			if !place.OnStack {
				g.constant(place.Reg, arg.constant, typ)
				continue
			}
			tmp, err := g.alloc(typ)
			if err != nil {
				return 0, err
			}
			g.constant(tmp, arg.constant, typ)
			g.emit(stackStoreOf(typ, true), reg(tmp, typ), mem(place.Offset))
			g.release(tmp)
			continue
		}
		for j, r := range arg.regs {
			typ := arg.types[j]
			switch {
			case typ.isVec:
				g.vmove(vector, r-vecBase)
				vector++
			case typ.isFloat:
				g.emit("fmov", reg(vecBase+vector, typ), reg(r, typ))
				vector++
			case !place.OnStack:
				g.emit("mov", reg(place.Reg+j, typ), reg(r, typ))
			default:
				g.emit(stackStoreOf(typ, len(arg.regs) == 1), reg(r, typ), mem(place.Offset+int64(8*j)))
			}
			if !arg.fixed {
				g.release(r)
			}
		}
	}
	if vector > 8 {
		return 0, unsupported("a call to %s: the arguments exhaust the floating-point argument registers", ident.Value)
	}
	if recordResult != nil && recordResult.layout.size > 16 {
		// The callee writes its result into the temp through x8.
		g.usedX8 = true
		g.emit("add", xr(8), sp(), imm(g.slotMem(recordResult.offset).Offset))
	}
	// Spill the live scratch registers that hold a value: the callee owns
	// x9–x15 and v16–v23 (one allocated for an enclosing expression's
	// result and not yet written holds nothing, and a spill would read it
	// uninitialized — which the checker refuses).
	var spilled []int
	for _, r := range g.live {
		if !g.defined[r] {
			continue
		}
		g.emit("str", spillReg(r), g.slotMem(g.spillSlot(r)))
		spilled = append(spilled, r)
	}
	target := g.calleeName(ident)
	if callee, declared := g.functions[target]; declared {
		// A callee under the vector contract is reached at its native
		// entry; the compiler lowers it natively or drops this caller.
		target = NativeSymbol(callee)
	}
	g.emit("bl", asm.Symbol{Name: target})
	for _, r := range spilled {
		g.emit("ldr", spillReg(r), g.slotMem(g.spill[r]))
	}
	for _, r := range homes {
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
	if resultType.isVec {
		g.vmove(out-vecBase, 0)
	} else if resultType.isFloat {
		g.emit("fmov", reg(out, *resultType), reg(vecBase, *resultType))
	} else {
		g.emit("mov", reg(out, *resultType), reg(0, *resultType))
		if !resultType.isBool {
			// AAPCS64 leaves the bits above a narrow result unspecified, as
			// it does above a narrow argument: the caller normalizes, and
			// the verifier's call summary holds it to that (a fresh
			// unknown above the result's width).
			g.normalize(out, *resultType)
		}
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
	arr, err := g.arrayOperand(borrow.Right)
	if err != nil {
		return nil, err
	}
	if arr == nil {
		return nil, unsupported("%s of %s (only an owned array local)", ident.Value, borrow.Right.String())
	}
	if arr.elem != target.elem {
		return nil, unsupported("%s over [%d]%s where %s elements are expected", ident.Value, arr.length, arr.elem.name, target.elem.name)
	}
	return arr, nil
}

// forwardedSlot reports the scratch register that the last emitted
// instruction stored to a slot variable's slot: a read of the variable that
// follows its store directly (`t: u32 = f(x); t != NONE`) takes the value
// from the register instead of loading it back. Nothing has written the
// register since — the store is the last instruction.
func (g *generator) forwardedSlot(name string) (int, bool) {
	if v, inReg := g.regs[name]; inReg && v >= 0 {
		return 0, false
	}
	slot, isSlot := g.slots[name]
	if !isSlot || slot < 0 {
		return 0, false
	}
	n := len(g.items)
	if n == 0 {
		return 0, false
	}
	ins, isIns := g.items[n-1].(asm.Instruction)
	if !isIns || ins.Mnemonic != "str" || len(ins.Operands) != 2 {
		return 0, false
	}
	src, isReg := ins.Operands[0].(asm.Register)
	memory, isMem := ins.Operands[1].(asm.Memory)
	if !isReg || !isMem || (src.Class != asm.ClassW && src.Class != asm.ClassX) || src.Num < scratchLow || src.Num > scratchHigh {
		return 0, false
	}
	want := g.slotMem(slot)
	if memory.Base.Class != asm.ClassSP || memory.Offset != want.Offset || memory.Index != nil {
		return 0, false
	}
	return src.Num, true
}

// stackStoreOf is the store that writes a scalar argument to its stack
// slot at the value's own size: a narrow scalar under the packing
// convention shares its 8 bytes with its neighbors, so a u8 is `strb` and a
// u16 `strh`; a word of a span or a record chunk is a whole `str`.
func stackStoreOf(typ scalar, scalarWord bool) string {
	if !scalarWord || typ.isBool || typ.wide() || typ.bits == 32 {
		return "str"
	}
	switch typ.bits {
	case 8:
		return "strb"
	case 16:
		return "strh"
	}
	return "str"
}

// argClassOf is a parameter type's integer-class layout description
// (asm/abi.go): a scalar one register and its natural size, a span two
// registers and sixteen bytes, a record its chunks or one register for a
// reference; false for a type outside the subset (floats and vectors take
// their own registers).
func (g *generator) argClassOf(typ ast.Expression) (asm.ArgClass, bool) {
	if s, ok := scalarOf(typ); ok {
		if s.isFloat || s.isVec {
			return asm.ArgClass{}, false
		}
		size := int64(s.bits / 8)
		if s.isBool {
			size = 4
		}
		return asm.ArgClass{Words: 1, Bytes: size, Align: size}, true
	}
	if layout, isValue, err := g.valueLayoutOf(typ); isValue {
		if err != nil || layout.isHFA() {
			return asm.ArgClass{}, false
		}
		regs := 1
		if layout.size <= 16 {
			regs = layout.chunks()
		}
		return asm.ArgClass{Words: regs, Bytes: int64(regs) * 8, Align: 8}, true
	}
	if _, ok := g.spanTypeOf(typ); ok {
		return asm.ArgClass{Words: 2, Bytes: 16, Align: 8}, true
	}
	return asm.ArgClass{}, false
}

// outgoingArea sizes the stack-argument area this body's calls need: the
// largest over its calls to program functions, from the callees'
// signatures under the same layout the callees read (rounded to 16).
func (g *generator) outgoingArea(body ast.Expression) int64 {
	most := int64(0)
	walk(body, func(n ast.Node) {
		call, isCall := n.(*ast.InvocationExpression)
		if !isCall {
			return
		}
		ident, isIdent := call.Function.(*ast.Identifier)
		if !isIdent {
			return
		}
		callee, known := g.functions[ident.Value]
		if !known {
			return
		}
		var classes []asm.ArgClass
		for _, p := range callee.Parameters {
			if class, ok := g.argClassOf(p.Type); ok {
				classes = append(classes, class)
			}
		}
		if _, bytes := asm.LayoutArguments(classes, g.packedStack); bytes > most {
			most = bytes
		}
	})
	return most
}

// callerHomesLive lists the caller-saved homes of the variables in scope,
// in register order: the registers a call would clobber that hold a value
// the body may still read.
func (g *generator) callerHomesLive(call *ast.InvocationExpression) []int {
	at, known := -1, false
	if g.lv != nil {
		at, known = g.lv.calls[call]
	}
	seen := map[int]bool{}
	var out []int
	for name, r := range g.regs {
		if !isCallerHome(r) || seen[r] {
			continue
		}
		if known && !g.lv.liveAfter(name, at) {
			continue // dead after this call: nothing to keep
		}
		seen[r] = true
		out = append(out, r)
	}
	sort.Ints(out)
	return out
}

// isCallerHome reports a register of the caller-saved home pools: the
// integer ones, and the vector ones v16–v31 of Lane.VectorHomes.
func isCallerHome(r int) bool {
	return r == 16 || r == 17 || (r >= 2 && r <= 7) || (r >= scratchLow && r <= scratchHigh) || (r >= vecBase+vecScratchLow && r <= vecBase+vecScratchHigh)
}

// spillSlot is a register's spill slot, allotted on first use: eight
// bytes for an integer register, sixteen aligned bytes for a vector one
// (a q register spills whole; a scratch may hold a vector or a float).
func (g *generator) spillSlot(r int) int64 {
	if _, ok := g.spill[r]; !ok {
		if r >= vecBase {
			if g.nslots%2 != 0 {
				g.nslots++
			}
			g.spill[r] = 8 * g.nslots
			g.nslots += 2
		} else {
			g.spill[r] = 8 * g.nslots
			g.nslots++
		}
	}
	return g.spill[r]
}

// spillReg is the whole-register view a scratch register spills as.
func spillReg(r int) asm.Register {
	if r >= vecBase {
		return qreg(r - vecBase)
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

// statementConditional recognizes `cond ? a` and `cond ? a | b` in
// statement position: the true arm, and the false arm or nil when the
// conditional has none (the parser's sugar leaves the false arm empty).
func statementConditional(match *ast.MatchExpression) (whenTrue, whenFalse ast.Expression, ok bool) {
	if match.Scrutinee == nil || len(match.Arms) == 0 || len(match.Arms) > 2 {
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
			whenFalse = arm.Body
		default:
			return nil, nil, false
		}
	}
	return whenTrue, whenFalse, whenTrue != nil
}

// calleeName resolves the function a call names: `is_valid_utf8` is the
// standard library's validator `utf8.valid` when a module build carries it
// (docs/spec/70-strings.md section 8; the C backend makes the same call),
// otherwise the name as spelled.
func (g *generator) calleeName(ident *ast.Identifier) string {
	if ident.Value == "is_valid_utf8" {
		if _, has := g.functions["utf8__valid"]; has {
			return "utf8__valid"
		}
	}
	return ident.Value
}

// mentionsCall reports a body with a call to a program function or assert
// (a conversion `u32(x)` is not a call).
func mentionsCall(body ast.Node) bool {
	found := false
	walk(body, func(n ast.Node) {
		if call, ok := n.(*ast.InvocationExpression); ok {
			if _, isLibrary := libraryMember(call); isLibrary {
				return // an instruction function is an instruction, not a call
			}
			if _, isSimd := simdCallee(call.Function); isSimd {
				return // a vector operation is an instruction too
			}
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
	return g.guardedIndexAt(sp, index, nil)
}

// guardedIndexAt is guardedIndex for the access at tok: when the checker
// proved the index in range (IndexProven) and the lowering elides, the
// guard is left out and the index is read from the variable's own
// callee-saved register where it has one — the register the loop's exit
// test compared, so the checker's fact from that test admits the access
// without a second compare.
func (g *generator) guardedIndexAt(sp span, index ast.Expression, tok *token.Token) (int, error) {
	// GuardLines is keyed by the line the emitted instructions carry (the
	// statement's, g.line), the line a checker finding names.
	if g.elide && tok != nil && g.tc != nil && !g.guardLines[g.line] && (g.tc.IndexProven(*tok) || rewriteProvenIndex(*tok)) {
		idxType, err := g.typeOf(index, nil)
		if err == nil && !idxType.signed && !idxType.isBool && !idxType.isFloat && !idxType.wide() {
			if ident, isIdent := index.(*ast.Identifier); isIdent {
				if v, inReg := g.regs[ident.Value]; inReg && v >= 0 {
					// The variable's register is the index; the load's
					// destination is a fresh scratch (the caller allocates).
					g.elided++
					return -v - 2, nil // encoded: a fixed register, not a scratch
				}
			}
			r, err := g.indexValue(index)
			if err != nil {
				return 0, err
			}
			g.elided++
			return r, nil
		}
	}
	if ident, isIdent := index.(*ast.Identifier); isIdent && tok != nil {
		// An index that is a register variable of unsigned 32-bit type:
		// the guard compares the variable's own register and the access
		// indexes by it — no copy (the checker keys its fact on the
		// compared register, whichever it is).
		if v, inReg := g.regs[ident.Value]; inReg && v >= 0 && v < vecBase {
			if t, ok := g.types[ident.Value]; ok && !t.signed && !t.isBool && !t.isFloat && !t.isVec && !t.wide() {
				g.usedTrap = true
				if sp.frameLen > 0 && sp.frameLen <= maxCmpImmediate {
					g.emit("cmp", wr(v), imm(sp.frameLen))
				} else {
					g.emit("cmp", wr(v), wr(sp.lenReg))
				}
				g.branch("hs", g.trap)
				return -v - 2, nil
			}
		}
	}
	r, err := g.indexValue(index)
	if err != nil {
		return 0, err
	}
	g.usedTrap = true
	if sp.frameLen > 0 && sp.frameLen <= maxCmpImmediate {
		// A span over a frame array: the frame idiom's constant guard, so
		// the checker bounds the access inside the declared frame.
		g.emit("cmp", wr(r), imm(sp.frameLen))
	} else {
		g.emit("cmp", wr(r), wr(sp.lenReg))
	}
	g.branch("hs", g.trap)
	return r, nil
}

// maxCmpImmediate is the largest unshifted `cmp wI, #K` immediate (12 bits).
const maxCmpImmediate = 4095

// indexValue evaluates an element index into a 32-bit register: a u32 as
// is; a u64 after checking its high word is zero (an index of 2^32 or more
// is past every span and array, so it traps), leaving the low word for the
// checker's 32-bit index idiom.
func (g *generator) indexValue(index ast.Expression) (int, error) {
	if k, isConst := constantValue(index); isConst && k >= 0 && k < 1<<32 {
		// A bare literal index (`cursor[0]`) is the unsigned constant it
		// spells, whatever type inference would default it to.
		r, err := g.alloc(scalars["u32"])
		if err != nil {
			return 0, err
		}
		g.constant(r, uint64(k), scalars["u32"])
		return r, nil
	}
	idxType, err := g.typeOf(index, nil)
	if err != nil {
		return 0, err
	}
	if idxType.isBool || idxType.isFloat || (idxType.signed && idxType.bits != 32) {
		return 0, unsupported("an element index of type %s (indices are unsigned or i32)", idxType.name)
	}
	// An i32 index guards as its 32-bit pattern: a negative one is a huge
	// unsigned value `cmp wI, wLen; b.hs` traps, as the C backend's
	// `(u64)(i)` does, and a non-negative one is its own zero-extension.
	r, err := g.expr(index, &idxType)
	if err != nil {
		return 0, err
	}
	if idxType.wide() {
		high, err := g.alloc(scalars["u64"])
		if err != nil {
			return 0, err
		}
		g.emit("lsr", xr(high), xr(r), imm(32))
		g.usedTrap = true
		g.emit("cbnz", xr(high), asm.Symbol{Name: g.trap})
		g.release(high)
	}
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
func (g *generator) arrayOperand(expr ast.Expression) (*arrayLocal, error) {
	p, err := g.placeOf(expr)
	if err != nil {
		return nil, err
	}
	return p.arr, nil
}

// staticArrayOf resolves the array an expression names — an owned array
// local, or an array field through any chain of record fields and record
// elements — without emitting code: the element type and length only. The
// type queries (typeOf, `len`) go through it, so a query never lowers an
// element address; placeOf does that once, when the access is lowered.
func (g *generator) staticArrayOf(expr ast.Expression) (elem scalar, elemLayout *recordLayout, length int64, ok bool) {
	switch e := expr.(type) {
	case *ast.Identifier:
		if arr, isArray := g.arrays[e.Value]; isArray {
			return arr.elem, arr.elemLayout, arr.length, true
		}
		if sa, isScalar := g.scalarArrays[e.Value]; isScalar {
			return sa.elem, nil, sa.length, true
		}
		if gl, isTable := g.tables[e.Value]; isTable {
			return scalars[gl.Elem], nil, gl.Length, true
		}
		if decl, isAggregate := g.aggregates[e.Value]; isAggregate && !g.shadowed(e.Value) {
			if elem, elemLayout, length, err := g.arrayTypeOf(decl.Type); err == nil {
				return elem, elemLayout, length, true
			}
		}
	case *ast.IndexExpression:
		if !e.Dot {
			return scalar{}, nil, 0, false
		}
		base, err := g.recordLayoutOfExpr(e.Left)
		if err != nil {
			return scalar{}, nil, 0, false
		}
		if name, isName := e.Index.(*ast.Identifier); isName {
			if field, has := base.fields[name.Value]; has && field.kind == fieldArray {
				return field.typ, field.layout, field.length, true
			}
		}
	}
	return scalar{}, nil, 0, false
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
		// A constant element: its place — rebased through a temporary when
		// the offset is past the load's immediate (a field far into a large
		// element, the OS pilot's N8), returned as the base to release.
		mem, temp, err := g.reachable(arr.loc().plus(k*size), size)
		if err != nil {
			return asm.Memory{}, 0, 0, err
		}
		return mem, -1, temp, nil
	}
	r, err := g.indexValue(index)
	if err != nil {
		return asm.Memory{}, 0, 0, err
	}
	return g.arrayAddressReg(arr, r)
}

// arrayAddressReg is arrayAddress over an index already evaluated into
// the 32-bit scratch register r (an index computed before the place, when
// its expression calls — the call's clobber must precede the place's
// facts, docs/spec/94-assembler.md §9).
func (g *generator) arrayAddressReg(arr *arrayLocal, r int) (address asm.Memory, indexReg, baseReg int, err error) {
	size := int64(arr.elem.bits / 8)
	base, err := g.alloc(scalars["u64"])
	if err != nil {
		return asm.Memory{}, 0, 0, err
	}
	if arr.inReg {
		// An array field inside a computed element: its address is the
		// element's plus the field offset (the checker narrows the region).
		if err := g.addOffset(base, arr.reg, arr.offset); err != nil {
			return asm.Memory{}, 0, 0, err
		}
	} else {
		g.emit("add", xr(base), sp(), imm(g.slotMem(arr.offset).Offset))
	}
	if err := g.constantGuard(r, arr.length); err != nil {
		return asm.Memory{}, 0, 0, err
	}
	idx := wr(r)
	return asm.Memory{Base: xr(base), Index: &idx, Shift: log2Bytes(int(size)), Extend: "uxtw"}, r, base, nil
}

// callsProgramFunction reports an expression that calls one of the
// program's functions (a `bl` in the lowering, which clobbers every
// scratch register and, to the checker, every fact about them).
func (g *generator) callsProgramFunction(expr ast.Expression) bool {
	found := false
	walk(expr, func(n ast.Node) {
		if call, isCall := n.(*ast.InvocationExpression); isCall && !found {
			if ident, isIdent := call.Function.(*ast.Identifier); isIdent {
				if _, known := g.functions[ident.Value]; known {
					found = true
				}
			}
		}
	})
	return found
}

// constantGuard emits the constant index guard `cmp wI, #N; b.hs trap`
// over an array of N elements; a length past the compare immediate is
// materialized in a scratch register first (`movz wK, #N; cmp wI, wK`),
// which the checker reads as the same constant guard (asm/check.go, a
// compare against a register holding a known constant).
func (g *generator) constantGuard(r int, length int64) error {
	g.usedTrap = true
	if length <= maxCmpImmediate {
		g.emit("cmp", wr(r), imm(length))
	} else {
		k, err := g.alloc(scalars["u32"])
		if err != nil {
			return err
		}
		g.constant(k, uint64(length), scalars["u32"])
		g.emit("cmp", wr(r), wr(k))
		g.release(k)
	}
	g.branch("hs", g.trap)
	return nil
}

// arrayElement lowers a load from an owned array local.
func (g *generator) arrayElement(arr *arrayLocal, index ast.Expression) (int, error) {
	return g.arrayElementReg(arr, index, -1)
}

// arrayElementReg is arrayElement over an index already in register r
// (r < 0: evaluate index here).
func (g *generator) arrayElementReg(arr *arrayLocal, index ast.Expression, r int) (int, error) {
	var address asm.Memory
	var idx, base int
	var err error
	if r >= 0 {
		address, idx, base, err = g.arrayAddressReg(arr, r)
	} else {
		address, idx, base, err = g.arrayAddress(arr, index)
	}
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
		if err := g.fieldStore(target.sc, value); err != nil {
			return err
		}
		g.release(value)
		g.releaseTemps(target.sc.temps)
		return nil
	case target.rec != nil:
		src, err := g.recordValueAs(s.Value, target.rec.layout)
		if err != nil {
			return err
		}
		return g.storeRecordToPlace(target, src, s)
	case target.arr != nil:
		// `r.h = f(r.h)` / `r.h = [8]u32{…}`: a whole owned array of
		// scalars stored as one value.
		if dst, isValue := g.arrayAsRecord(target.arr); isValue {
			src, err := g.recordValueAs(s.Value, dst.layout)
			if err != nil {
				return err
			}
			return g.storeRecordToPlace(place{rec: dst}, src, s)
		}
	}
	return unsupported("a store to the array %s", s.Target.String())
}

// storeRecordToPlace copies an evaluated record value into a record place.
func (g *generator) storeRecordToPlace(target place, src *recordLocal, s *ast.IndexAssignmentStatement) error {
	if target.rec == nil {
		return unsupported("a store to the array %s", s.Target.String())
	}
	if target.rec.readOnly {
		return unsupported("a store into %s through a read-only view", s.Target.String())
	}
	if src.layout != target.rec.layout {
		return unsupported("a %s stored into %s (a %s)", src.layout.name, s.Target.String(), target.rec.layout.name)
	}
	err := g.copyBytes(target.rec.loc(), src.loc(), target.rec.layout.size)
	g.releaseTemps(src.temps)
	g.releaseTemps(target.rec.temps)
	return err
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
	if _, _, _, isArray := g.staticArrayOf(e.Left); isArray && g.callsProgramFunction(e.Index) {
		// The index calls: evaluate it before the place, so the call's
		// clobber of the scratch registers precedes the element address
		// and the facts the checker holds about it (the OS pilot's N8).
		if _, isConst := constantValue(e.Index); !isConst {
			r, err := g.indexValue(e.Index)
			if err != nil {
				return 0, err
			}
			arr, err := g.arrayOperand(e.Left)
			if err != nil {
				return 0, err
			}
			if arr == nil {
				return 0, unsupported("an index into %s (not an array)", e.Left.String())
			}
			return g.arrayElementReg(arr, e.Index, r)
		}
	}
	if hidden, elem, isScalar := g.scalarElement(e); isScalar {
		// An element of a scalar-replaced array: its hidden local.
		r, err := g.alloc(elem)
		if err != nil {
			return 0, err
		}
		g.put(g.loadVar(hidden, r))
		return r, nil
	}
	arr, err := g.arrayOperand(e.Left)
	if err != nil {
		return 0, err
	}
	if arr != nil {
		return g.arrayElement(arr, e.Index)
	}
	sp, err := g.spanOperand(e.Left)
	if err != nil {
		return 0, err
	}
	if sp.array != nil && sp.elemLayout == nil {
		// A local view of an owned array: the array's own element idiom.
		return g.arrayElement(sp.array, e.Index)
	}
	r, err := g.guardedIndexAt(sp, e.Index, &e.Token)
	if err != nil {
		return 0, err
	}
	if r < -1 {
		// The index is a variable's own register (an elided guard): the
		// element lands in a fresh scratch register.
		fixed := -r - 2
		index := wr(fixed)
		address := asm.Memory{Base: xr(sp.baseReg), Index: &index, Shift: log2Bytes(sp.elem.bits / 8), Extend: "uxtw"}
		out, err := g.alloc(sp.elem)
		if err != nil {
			return 0, err
		}
		if sp.elem.isFloat {
			g.emit("ldr", reg(out, sp.elem), address)
			return out, nil
		}
		g.emit(loadOf(sp.elem), reg(out, sp.elem), address)
		return out, nil
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

// placeStore lowers `p.f = e` and `pool[i].f = e`. When the value calls,
// it is evaluated before the place: an element address computed first
// would be held across the call, spilled and reloaded, and the checker
// cannot carry a region through a spill (docs/spec/94-assembler.md §9).
// The place is computed once to learn its type — that computation is
// rolled back — then again after the value.
func (g *generator) placeStore(s *ast.IndexAssignmentStatement) error {
	if !mentionsCall(s.Value) {
		target, err := g.placeOf(s.Target)
		if err != nil {
			return err
		}
		return g.storeToPlace(target, s)
	}
	mark := len(g.items)
	probe, err := g.placeOf(s.Target)
	if err != nil {
		return err
	}
	g.items = g.items[:mark]
	switch {
	case probe.sc != nil:
		g.releaseTemps(probe.sc.temps)
		if probe.sc.readOnly {
			return unsupported("a store into %s through a read-only view", s.Target.String())
		}
		typ := probe.sc.typ
		value, err := g.expr(s.Value, &typ)
		if err != nil {
			return err
		}
		target, err := g.placeOf(s.Target)
		if err != nil {
			return err
		}
		if target.sc == nil {
			return unsupported("the place %s changed shape", s.Target.String())
		}
		if err := g.fieldStore(target.sc, value); err != nil {
			return err
		}
		g.release(value)
		g.releaseTemps(target.sc.temps)
		return nil
	case probe.rec != nil:
		g.releaseTemps(probe.rec.temps)
		if probe.rec.readOnly {
			return unsupported("a store into %s through a read-only view", s.Target.String())
		}
		layout := probe.rec.layout
		src, err := g.recordValueAs(s.Value, layout)
		if err != nil {
			return err
		}
		if src.layout != layout {
			return unsupported("a %s stored into %s (a %s)", src.layout.name, s.Target.String(), layout.name)
		}
		target, err := g.placeOf(s.Target)
		if err != nil {
			return err
		}
		if target.rec == nil {
			return unsupported("the place %s changed shape", s.Target.String())
		}
		err = g.copyBytes(target.rec.loc(), src.loc(), layout.size)
		g.releaseTemps(src.temps)
		g.releaseTemps(target.rec.temps)
		return err
	}
	target, err := g.placeOf(s.Target)
	if err != nil {
		return err
	}
	return g.storeToPlace(target, s)
}

// elementStore lowers `v[i] = e` through a writable span.
func (g *generator) elementStore(s *ast.IndexAssignmentStatement) error {
	if s.Target.Dot {
		return g.placeStore(s)
	}
	if hidden, elem, isScalar := g.scalarElement(s.Target); isScalar {
		// An element of a scalar-replaced array: an assignment to its
		// hidden local, renamed into its home when the value's last
		// instruction allows (assignVar).
		r, err := g.expr(s.Value, &elem)
		if err != nil {
			return err
		}
		g.assignVar(hidden, r)
		g.killLoopFacts(hidden)
		return nil
	}
	if layout := g.recordArrayElementLayout(s.Target.Left); layout != nil {
		// `pool[i] = r`: a record element replaced. A value that calls is
		// evaluated before the place: a `bl` clobbers the scratch
		// registers and, to the checker, the element address's provenance
		// (a reload from the spill slot is no element region), so the
		// address is formed after the call — `out[0] =
		// time.time_source_native()` in the dbs pilot's time source.
		var early *recordLocal
		if g.callsProgramFunction(s.Value) && !g.callsProgramFunction(s.Target.Index) {
			src, err := g.recordValueAs(s.Value, layout)
			if err != nil {
				return err
			}
			early = src
		}
		target, err := g.placeOf(s.Target)
		if err != nil {
			return err
		}
		if early != nil {
			return g.storeRecordToPlace(target, early, s)
		}
		return g.storeToPlace(target, s)
	}
	// Operands that call are evaluated before the place: a `bl` clobbers
	// the scratch registers and, to the checker, every fact about them,
	// so an element address computed first would come back from its spill
	// slot without provenance (the OS pilot's N8, `s[dom].pages[cell(i, j)]`).
	value, idxReg := -1, -1
	if elem, _, _, isArray := g.staticArrayOf(s.Target.Left); isArray && (g.callsProgramFunction(s.Value) || g.callsProgramFunction(s.Target.Index)) {
		v, err := g.expr(s.Value, &elem)
		if err != nil {
			return err
		}
		value = v
		if _, isConst := constantValue(s.Target.Index); !isConst {
			r, err := g.indexValue(s.Target.Index)
			if err != nil {
				return err
			}
			idxReg = r
		}
	}
	arr, err := g.arrayOperand(s.Target.Left)
	if err != nil {
		return err
	}
	if arr == nil {
		// A local span over an owned array stores through the array's own
		// idiom (a view refuses below, as any view does).
		if sp, err := g.spanOperand(s.Target.Left); err == nil && sp.array != nil && sp.elemLayout == nil && sp.writable {
			arr = sp.array
		}
	}
	if arr != nil {
		if arr.readOnly {
			return unsupported("a store into %s through a view", s.Target.Left.String())
		}
		if value < 0 {
			v, err := g.expr(s.Value, &arr.elem)
			if err != nil {
				return err
			}
			value = v
		}
		var address asm.Memory
		var idx, base int
		if idxReg >= 0 {
			address, idx, base, err = g.arrayAddressReg(arr, idxReg)
		} else {
			address, idx, base, err = g.arrayAddress(arr, s.Target.Index)
		}
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
	value, err = g.expr(s.Value, &sp.elem)
	if err != nil {
		return err
	}
	r, err := g.guardedIndexAt(sp, s.Target.Index, &s.Target.Token)
	if err != nil {
		return err
	}
	fixed := r < -1
	if fixed {
		r = -r - 2
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
	if !fixed {
		g.release(r)
	}
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
		if g.result != nil && !g.result.isFloat && g.valueOnly(e) {
			// Every arm yields a value: they meet in one scratch register
			// and the result register is written once, at the join. The
			// checker is linear, so a result written inside an arm would
			// forget the parameters' span and record facts for the arms
			// after it (docs/spec/94-assembler.md §9).
			out, err := g.alloc(*g.result)
			if err != nil {
				return err
			}
			// Defined before the arms: an arm that calls before writing it
			// spills it, and a spill of a never-written register is a read
			// the checker and the verifier refuse.
			g.zeroInit(out, *g.result)
			if err := g.resultInto(e, out); err != nil {
				return err
			}
			g.moveResult(out, *g.result)
			g.release(out)
			return nil
		}
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
			if err := g.lowerStatementsBefore(stmts[:len(stmts)-1], stmts[len(stmts)-1]); err != nil {
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

// valueOnly reports whether a result expression yields its value through
// plain arms alone: no self tail call (the loop shape the verifier
// recognizes keeps its own layout) and no call to a never function,
// anywhere down its conditionals and blocks.
func (g *generator) valueOnly(expr ast.Expression) bool {
	switch e := expr.(type) {
	case *ast.MatchExpression:
		for _, arm := range e.Arms {
			if arm == nil || arm.Body == nil || !g.valueOnly(arm.Body) {
				return false
			}
		}
		return true
	case *ast.BlockExpression:
		if e.Block == nil || len(e.Block.Statements) == 0 {
			return false
		}
		last, ok := e.Block.Statements[len(e.Block.Statements)-1].(*ast.ExpressionStatement)
		return ok && !last.Discard && g.valueOnly(last.Expression)
	case *ast.InvocationExpression:
		if g.isTailCall(e) {
			return false
		}
		if ident, ok := e.Function.(*ast.Identifier); ok {
			if callee := g.functions[ident.Value]; callee != nil && callee.ReturnType != nil && callee.ReturnType.String() == "never" {
				return false
			}
		}
	}
	return true
}

// zeroInit defines a register as zero at a scalar's kind: the zero
// register moved for an integer, `movi #0` for a fixed vector (the zero
// register has no vector form), `fmov` from the zero register for a float.
func (g *generator) zeroInit(r int, s scalar) {
	switch {
	case s.isVec:
		g.emit("movi", reg(r, s), imm(0))
	case s.isFloat:
		g.emit("fmov", reg(r, s), zeroReg(s))
	default:
		g.emit("mov", reg(r, s), zeroReg(s))
	}
}

// zeroReg spells the zero register at a scalar's width.
func zeroReg(s scalar) asm.Register {
	if s.wide() {
		return xr(31)
	}
	return wr(31)
}

// resultInto lowers a value-only result expression into the register out:
// a conditional's arms each write out and meet at the join; a block runs
// its statements and yields its tail.
func (g *generator) resultInto(expr ast.Expression, out int) error {
	switch e := expr.(type) {
	case *ast.MatchExpression:
		if whenTrue, whenFalse, ok := boolConditional(e); ok {
			elseLabel, end := g.newLabel("else"), g.newLabel("endif")
			if err := g.condition(e.Scrutinee, elseLabel); err != nil {
				return err
			}
			if err := g.resultInto(whenTrue, out); err != nil {
				return err
			}
			g.emit("b", asm.Symbol{Name: end})
			g.label(elseLabel)
			if err := g.resultInto(whenFalse, out); err != nil {
				return err
			}
			g.label(end)
			return nil
		}
		return g.lowerMatch(e, func(body ast.Expression) error { return g.resultInto(body, out) })
	case *ast.BlockExpression:
		if e.Block != nil && len(e.Block.Statements) > 0 {
			g.pushScope()
			defer g.popScope()
			stmts := e.Block.Statements
			// The trailing expression still reads the block's locals: its
			// uses count before any register is released (nativegen/liveness.go).
			if err := g.lowerStatementsBefore(stmts[:len(stmts)-1], stmts[len(stmts)-1]); err != nil {
				return err
			}
			if es, ok := stmts[len(stmts)-1].(*ast.ExpressionStatement); ok && !es.Discard {
				return g.resultInto(es.Expression, out)
			}
		}
	}
	r, err := g.expr(expr, g.result)
	if err != nil {
		return err
	}
	if r != out {
		g.emit("mov", reg(out, *g.result), reg(r, *g.result))
		g.release(r)
	}
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
		g.put(g.storeVar(g.fn.Parameters[i].Name.Value, r))
		g.release(r)
	}
	g.emit("b", asm.Symbol{Name: g.head})
	return nil
}

// isTailCall recognizes a self-call the loop lowering handles.
func (g *generator) isTailCall(expr ast.Expression) bool {
	call, ok := expr.(*ast.InvocationExpression)
	if !ok || len(g.spans) != 0 || len(g.stackParams) != 0 {
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
		if bind.OnStack {
			fmt.Fprintf(&b, "  bind [sp, #%d] = %s\n", bind.Stack, bind.Param)
			continue
		}
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
			fmt.Fprintf(&b, "  %s\n", fn.Spell(it))
		}
	}
	b.WriteString("}\n")
	return b.String()
}

// ---- instruction functions --------------------------------------------------

// libraryMember reads `arm64.member(...)`: a call to an instruction function
// of the compiler-known machine library (docs/spec/92-ffi.md §3,
// 95–98-aarch64-*.md). The native backend lowers it to the instruction it
// names, through the assembler's own parser, so the spelling the checker
// and encoder see is the units' — and the seam checker's system capability
// judges every register access as it judges a unit's.
func libraryMember(call *ast.InvocationExpression) (string, bool) {
	access, isAccess := call.Function.(*ast.IndexExpression)
	if !isAccess || !access.Dot {
		return "", false
	}
	base, isIdent := access.Left.(*ast.Identifier)
	if !isIdent || base.Value != "arm64" {
		return "", false
	}
	member, isIdent := access.Index.(*ast.Identifier)
	if !isIdent {
		return "", false
	}
	return member.Value, true
}

// scalarInstructions are the one-instruction integer functions of the
// library: the mnemonic and the operand width.
var scalarInstructions = map[string]struct {
	mnemonic string
	typ      string
}{
	"rev32": {"rev", "u32"}, "rev64": {"rev", "u64"},
	"rbit32": {"rbit", "u32"}, "rbit64": {"rbit", "u64"},
	"clz32": {"clz", "u32"}, "clz64": {"clz", "u64"},
}

// instructionFunctionType is the result type of an instruction function in
// value position: a system-register read is a u64, a scalar instruction its
// width; the unit-valued ones (writes, barriers, event control) and the
// never-valued control transfers have no value.
func instructionFunctionType(member string) (scalar, error) {
	if spec, found, write := semir.LookupArm64SysRegMember(member); found && !write {
		_ = spec
		return scalars["u64"], nil
	}
	if op, isScalar := scalarInstructions[member]; isScalar {
		return scalars[op.typ], nil
	}
	return scalar{}, unsupported("the instruction function arm64.%s in value position", member)
}

// instructionValue lowers an instruction function with a value: `mrs` for a
// system-register read (under the system capability), or the scalar
// instruction over its one operand.
func (g *generator) instructionValue(member string, e *ast.InvocationExpression, typ scalar) (int, error) {
	if spec, found, write := semir.LookupArm64SysRegMember(member); found && !write {
		if len(e.Arguments) != 0 {
			return 0, unsupported("arm64.%s takes no argument", member)
		}
		g.system = true
		r, err := g.alloc(scalars["u64"])
		if err != nil {
			return 0, err
		}
		g.emit("mrs", xr(r), asm.SysReg{Name: strings.ToLower(spec.Asm)})
		return r, nil
	}
	if op, isScalar := scalarInstructions[member]; isScalar {
		if len(e.Arguments) != 1 {
			return 0, unsupported("arm64.%s takes one argument", member)
		}
		operand := scalars[op.typ]
		r, err := g.expr(e.Arguments[0], &operand)
		if err != nil {
			return 0, err
		}
		g.emit(op.mnemonic, reg(r, operand), reg(r, operand))
		return r, nil
	}
	return 0, unsupported("the instruction function arm64.%s", member)
}

// instructionEffect lowers an instruction function in statement position:
// `msr` for a system-register write, the barrier or event-control
// instruction the catalog names, or an exception return with its carried
// registers (`eret_x0(v)`: `mov x0, v` then `eret`, which ends the body of a
// never function).
func (g *generator) instructionEffect(member string, call *ast.InvocationExpression) error {
	emitText := func(text string) error {
		instr, err := asm.ParseInstructionLine(asm.ArchArm64, text, g.line)
		if err != nil {
			return unsupported("arm64.%s: %v", member, err)
		}
		if g.terminated {
			return nil
		}
		g.put(instr)
		return nil
	}
	if spec, found, write := semir.LookupArm64SysRegMember(member); found {
		if !write {
			return unsupported("arm64.%s (a system-register read) as a statement", member)
		}
		if len(call.Arguments) != 1 {
			return unsupported("arm64.%s takes one argument", member)
		}
		u64 := scalars["u64"]
		r, err := g.expr(call.Arguments[0], &u64)
		if err != nil {
			return err
		}
		g.system = true
		g.emit("msr", asm.SysReg{Name: strings.ToLower(spec.Asm)}, xr(r))
		g.release(r)
		return nil
	}
	if spec, isBarrier := semir.LookupArm64Barrier(member); isBarrier {
		if len(call.Arguments) != 0 {
			return unsupported("arm64.%s takes no argument", member)
		}
		switch spec.Operation {
		case semir.BarrierISB:
			return emitText("isb")
		case semir.BarrierDMB:
			return emitText("dmb " + barrierScope(spec.Scope))
		case semir.BarrierDSB:
			return emitText("dsb " + barrierScope(spec.Scope))
		}
		return unsupported("the barrier arm64.%s", member)
	}
	if spec, isEvent := semir.LookupArm64EventControl(member); isEvent {
		if len(call.Arguments) != 0 {
			return unsupported("arm64.%s takes no argument", member)
		}
		if strings.HasPrefix(spec.Instruction, "msr") {
			g.system = true
		}
		return emitText(spec.Instruction)
	}
	if spec, isTransfer := semir.LookupArm64ControlTransfer(member); isTransfer {
		if !g.never {
			return unsupported("arm64.%s outside a never function", member)
		}
		if len(call.Arguments) != len(spec.Carries) {
			return unsupported("arm64.%s takes %d arguments", member, len(spec.Carries))
		}
		// The carried values evaluate into scratch registers first, then
		// move to their registers (a later argument may read an earlier
		// one's register otherwise).
		var values []int
		u64 := scalars["u64"]
		for _, arg := range call.Arguments {
			r, err := g.expr(arg, &u64)
			if err != nil {
				return err
			}
			values = append(values, r)
		}
		for i, r := range values {
			var num int
			if _, err := fmt.Sscanf(spec.Carries[i], "x%d", &num); err != nil {
				return unsupported("arm64.%s carries %s", member, spec.Carries[i])
			}
			g.emit("mov", xr(num), xr(r))
			g.release(r)
		}
		g.system = true
		if err := emitText(spec.Instruction); err != nil {
			return err
		}
		g.terminated = true
		return nil
	}
	if _, isScalar := scalarInstructions[member]; isScalar {
		return unsupported("arm64.%s (a value) as a statement", member)
	}
	return unsupported("the instruction function arm64.%s", member)
}

// barrierScope spells a barrier's scope option as the ARM ARM does.
func barrierScope(scope semir.BarrierScope) string {
	switch scope {
	case semir.BarrierScopeISHLD:
		return "ishld"
	case semir.BarrierScopeISH:
		return "ish"
	case semir.BarrierScopeSY:
		return "sy"
	}
	return "sy"
}
