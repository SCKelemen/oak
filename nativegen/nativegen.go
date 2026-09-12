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
	baseReg  int // x register holding the base
	lenReg   int // w register holding the length
	// argBase/argLen: the argument registers the pair arrived in. In a
	// function that calls, the pair is parked in callee-saved registers
	// (baseReg/lenReg) by the prologue — the checker follows the copies —
	// so the callee's clobber of x0–x17 never touches it.
	argBase, argLen int
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
	offset int64 // slot offset (slotMem-relative), 8-byte aligned
	elem   scalar
	length int64
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
	name   string
	size   int64
	fields map[string]recordField
	order  []string
}

type recordField struct {
	typ    scalar
	offset int64
	size   int64 // the C field's size: a Bool field is the 4-byte enum
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

// Composites is the checker's table of the program's placeable record
// types (asm.Function.Composites): every declared record whose layout the
// backend can place, by name.
func Composites(records map[string]*ast.RecordLiteral) map[string]asm.Composite {
	g := &generator{recordDecls: records, layouts: map[string]*recordLayout{}}
	out := map[string]asm.Composite{}
	for name := range records {
		if layout, err := g.layoutOf(name); err == nil {
			out[name] = asm.Composite{Size: layout.size, HFA: layout.isHFA()}
		}
	}
	return out
}

// recordLocal is an owned record in the frame.
type recordLocal struct {
	offset int64 // slot offset (slotMem-relative), 8-byte aligned
	layout *recordLayout
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
		return nil, unsupported("the type %s is not a declared record", name)
	}
	if decl.Layout != nil && decl.Layout.Packed {
		return nil, unsupported("the packed record %s", name)
	}
	var reps []semir.RecordFieldRepresentation
	layout := &recordLayout{name: name, fields: map[string]recordField{}}
	for _, field := range decl.FieldOrder {
		typ, isScalar := scalarOf(field.Value)
		rep, placeable := fieldRepresentations[field.Value.String()]
		if !isScalar || !placeable {
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
		layout.fields[field.Name] = recordField{typ: typ, size: int64(rep.Size)}
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
	g.layouts[name] = layout
	return layout, nil
}

// recordTypeName reads a type expression naming a declared record.
func (g *generator) recordTypeName(expr ast.Expression) (string, bool) {
	ident, isIdent := expr.(*ast.Identifier)
	if !isIdent {
		return "", false
	}
	_, isRecord := g.recordDecls[ident.Value]
	return ident.Value, isRecord
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
	layouts     map[string]*recordLayout
	records     map[string]*recordLocal
	// Record parameters and results under AAPCS64's composite rules: up to
	// 16 bytes as ceil(size/8) x-register chunks, larger by reference to a
	// copy the caller owns (a result beyond 16 bytes is written through the
	// area the caller passes in x8, parked in a callee-saved register when
	// the body calls).
	recordParams   map[string]*recordParam
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
func Compile(fn *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, records map[string]*ast.RecordLiteral, tc *typechecker.TypeChecker) (*asm.Function, error) {
	if fn.Body == nil || fn.ExternSymbol != "" || fn.Receiver != nil || len(fn.TypeParams) > 0 || fn.AsmBacked {
		return nil, unsupported("not an ordinary function body")
	}
	if len(fn.Parameters) > 8 {
		return nil, unsupported("more than eight parameters")
	}
	g := &generator{fn: fn, tc: tc, functions: functions, slots: map[string]int64{}, types: map[string]scalar{}, spans: map[string]span{}, arrays: map[string]*arrayLocal{}, recordDecls: records, layouts: map[string]*recordLayout{}, records: map[string]*recordLocal{}, recordParams: map[string]*recordParam{}, regs: map[string]int{}, spill: map[int]int64{}, line: fn.Token.Line}
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
		if sp, ok := spanOf(p.Type); ok {
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
	off := int64(0)
	for ; off+8 <= size; off += 8 {
		g.emit("ldr", xr(tmp), g.slotMem(src.offset+off))
		g.emit("str", xr(tmp), asm.Memory{Base: xr(base), Offset: off})
	}
	for _, piece := range []struct {
		bytes       int64
		load, store string
	}{{4, "ldr", "str"}, {2, "ldrh", "strh"}, {1, "ldrb", "strb"}} {
		if off+piece.bytes <= size {
			g.emit(piece.load, wr(tmp), g.slotMem(src.offset+off))
			g.emit(piece.store, wr(tmp), asm.Memory{Base: xr(base), Offset: off})
			off += piece.bytes
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
	switch e := expr.(type) {
	case *ast.Identifier:
		rec, isRecord := g.records[e.Value]
		if !isRecord {
			return nil, unsupported("%s is not a record local", e.Value)
		}
		return rec, nil
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

// fillRecord evaluates a literal's fields (in layout order, before the
// record is bound) into a new record local named name (a temp when empty).
func (g *generator) fillRecord(layout *recordLayout, literal *ast.RecordLiteral, name string) (*recordLocal, error) {
	if len(literal.Fields) != len(layout.order) {
		return nil, unsupported("a partial %s literal", layout.name)
	}
	var values []int
	for _, field := range layout.order {
		expr, given := literal.Fields[field]
		if !given {
			return nil, unsupported("a %s literal without the field %s", layout.name, field)
		}
		typ := layout.fields[field].typ
		r, err := g.expr(expr, &typ)
		if err != nil {
			return nil, err
		}
		values = append(values, r)
	}
	var rec *recordLocal
	if name == "" {
		rec = g.tempRecord(layout)
	} else {
		rec = g.declareRecord(name, layout)
	}
	for i, field := range layout.order {
		g.fieldStore(rec, layout.fields[field], values[i])
		g.release(values[i])
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
	rec, err := g.recordValue(expr)
	if err != nil {
		return err
	}
	if rec.layout != g.resultRecord {
		return unsupported("a %s result where %s is declared", rec.layout.name, g.resultRecord.name)
	}
	if g.resultIndirect {
		return g.copyOut(g.resultAreaReg, rec)
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
		if _, ok := n.(*ast.VariableDeclaration); ok {
			found = true
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
		// A shadowed outer binding comes back into view.
		for i := len(g.scopes) - 1; i >= 0; i-- {
			if b, ok := g.scopes[i][name]; ok {
				if b.arr != nil {
					g.arrays[name] = b.arr
				} else if b.rec != nil {
					g.records[name] = b.rec
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
	bytes := length * int64(elem.bits/8)
	arr := &arrayLocal{offset: 8 * g.nslots, elem: elem, length: length}
	g.nslots += (bytes + 7) / 8
	delete(g.slots, name)
	delete(g.types, name)
	delete(g.regs, name)
	g.arrays[name] = arr
	g.scopes[len(g.scopes)-1][name] = slotBinding{reg: -1, arr: arr}
	return arr
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
	// The elements evaluate before the name is bound (an initializer never
	// sees the array it fills).
	var values []int
	for _, element := range literal.Elements {
		r, err := g.expr(element, &elem)
		if err != nil {
			return err
		}
		values = append(values, r)
	}
	arr := g.declareArray(s.Name.Value, elem, length)
	for i, r := range values {
		g.emit(storeOf(elem), reg(r, elem), g.slotMem(arr.offset+int64(i)*int64(elem.bits/8)))
		g.release(r)
	}
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
	// A copy of another record value: a local, a parameter, a call's result.
	src, err := g.recordValue(s.Value)
	if err != nil {
		return err
	}
	if src.layout != layout {
		return unsupported("the %s local %s initialized from a %s", typeName, s.Name.Value, src.layout.name)
	}
	rec := g.declareRecord(s.Name.Value, layout)
	return g.copyRecord(rec, src)
}

// copyRecord copies a record slot-wise (the padding travels too, as the C
// struct assignment copies it).
func (g *generator) copyRecord(dst, src *recordLocal) error {
	tmp, err := g.alloc(scalars["u64"])
	if err != nil {
		return err
	}
	words := (dst.layout.size + 7) / 8
	for w := int64(0); w < words; w++ {
		g.emit("ldr", xr(tmp), g.slotMem(src.offset+8*w))
		g.emit("str", xr(tmp), g.slotMem(dst.offset+8*w))
	}
	g.release(tmp)
	return nil
}

// fieldMem is a field's frame address.
func (g *generator) fieldMem(rec *recordLocal, field recordField) asm.Memory {
	return g.slotMem(rec.offset + field.offset)
}

// fieldLoad reads a field into a fresh register at its type: a Bool field
// is the 4-byte C enum holding 0 or 1, so its load is a 32-bit `ldr`.
func (g *generator) fieldLoad(rec *recordLocal, field recordField) (int, error) {
	r, err := g.alloc(field.typ)
	if err != nil {
		return 0, err
	}
	load := loadOf(field.typ)
	if field.typ.isBool {
		load = "ldr"
	}
	g.emit(load, reg(r, field.typ), g.fieldMem(rec, field))
	return r, nil
}

// fieldStore writes a normalized value of the field's type.
func (g *generator) fieldStore(rec *recordLocal, field recordField, r int) {
	store := storeOf(field.typ)
	if field.typ.isBool {
		store = "str"
	}
	g.emit(store, reg(r, field.typ), g.fieldMem(rec, field))
}

// fieldOperand reads `p.f` over a record local.
func (g *generator) fieldOperand(e *ast.IndexExpression) (*recordLocal, recordField, error) {
	ident, isIdent := e.Left.(*ast.Identifier)
	if !isIdent {
		return nil, recordField{}, unsupported("a field access on %s", e.Left.String())
	}
	rec, isRecord := g.records[ident.Value]
	if !isRecord {
		return nil, recordField{}, unsupported("a field access on %s (not a record local)", ident.Value)
	}
	name, isName := e.Index.(*ast.Identifier)
	if !isName {
		return nil, recordField{}, unsupported("a field access %s", e.String())
	}
	field, has := rec.layout.fields[name.Value]
	if !has {
		return nil, recordField{}, unsupported("the field %s of %s", name.Value, rec.layout.name)
	}
	return rec, field, nil
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
		name, isRecord := g.recordTypeName(decl.Type)
		if !isRecord {
			return
		}
		for _, field := range g.recordDecls[name].FieldOrder {
			if s, ok := scalarOf(field.Value); ok && s.isFloat {
				found = true
			}
		}
	})
	return found
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
			_, field, err := g.fieldOperand(e)
			if err != nil {
				return scalar{}, err
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
			return scalar{}, unsupported("a match that is not a Bool conditional")
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
			if typeName, isRecord := g.recordTypeName(s.Type); isRecord {
				if err := g.lowerRecordDeclaration(s, typeName); err != nil {
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
				// `q = p` / `q = f(p)`: a whole-record copy.
				from, err := g.recordValue(s.Value)
				if err != nil {
					return err
				}
				if from.layout != dst.layout {
					return unsupported("an assignment of a %s to the %s %s", from.layout.name, dst.layout.name, s.Name.Value)
				}
				if err := g.copyRecord(dst, from); err != nil {
					return err
				}
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
		return unsupported("a statement-level match that is not a Bool conditional")
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
		return unsupported("a conditional arm in statement position that is not a block")
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
		whenTrue, whenFalse, _ := boolConditional(e)
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
			rec, err := g.recordValue(arg)
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
				base, err := g.alloc(scalars["u64"])
				if err != nil {
					return 0, err
				}
				g.emit("add", xr(base), sp(), imm(g.slotMem(copied.offset).Offset))
				args = append(args, argument{regs: []int{base}, types: []scalar{scalars["u64"]}})
				continue
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
		target, isSpan := spanOf(p.Type)
		if !isSpan {
			return 0, unsupported("a call to %s (parameter %s: %s)", ident.Value, p.Name.Value, p.Type.String())
		}
		if forwarded, isIdent := arg.(*ast.Identifier); isIdent {
			// A span parameter passed on: its parked pair.
			sp, isParam := g.spans[forwarded.Value]
			if !isParam {
				return 0, unsupported("a call to %s: %s is not a span parameter", ident.Value, forwarded.Value)
			}
			if sp.elem != target.elem || (target.writable && !sp.writable) {
				return 0, unsupported("a call to %s: %s does not fit parameter %s", ident.Value, forwarded.Value, p.Name.Value)
			}
			args = append(args, argument{regs: []int{sp.baseReg, sp.lenReg}, types: []scalar{scalars["u64"], scalars["u32"]}, fixed: true})
			continue
		}
		arr, err := g.arrayArgument(arg, target)
		if err != nil {
			return 0, unsupported("a call to %s: %v", ident.Value, err)
		}
		base, err := g.alloc(scalars["u64"])
		if err != nil {
			return 0, err
		}
		length, err := g.alloc(scalars["u32"])
		if err != nil {
			return 0, err
		}
		g.emit("add", xr(base), sp(), imm(g.slotMem(arr.offset).Offset))
		g.constant(length, uint64(arr.length), scalars["u32"])
		args = append(args, argument{regs: []int{base, length}, types: []scalar{scalars["u64"], scalars["u32"]}})
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
				if isConversion(ident.Value) || ident.Value == "assert" || ident.Value == "len" || ident.Value == "view" || ident.Value == "span" || typechecker.FloatIntrinsicName(ident.Value) {
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
	ident, isIdent := expr.(*ast.Identifier)
	if !isIdent {
		return nil
	}
	return g.arrays[ident.Value]
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
		return g.slotMem(arr.offset + k*size), -1, -1, nil
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
	g.emit("add", xr(base), sp(), imm(g.slotMem(arr.offset).Offset))
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
	return out, nil
}

// element lowers `v[i]`: a guarded, whole-element load through the bound
// base, zero- or sign-extending as the element type reads in C.
func (g *generator) element(e *ast.IndexExpression) (int, error) {
	if e.Dot {
		rec, field, err := g.fieldOperand(e)
		if err != nil {
			return 0, err
		}
		return g.fieldLoad(rec, field)
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
		rec, field, err := g.fieldOperand(s.Target)
		if err != nil {
			return err
		}
		value, err := g.expr(s.Value, &field.typ)
		if err != nil {
			return err
		}
		g.fieldStore(rec, field, value)
		g.release(value)
		return nil
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
