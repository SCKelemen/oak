package asm

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
)

// Argument placement under AAPCS64 beyond the eight integer registers
// (docs/spec/94-assembler.md §9, twenty-sixth increment). The general
// registers x0–x7 take arguments in order; once an argument does not fit
// the registers left, it and every integer-class argument after it go to
// the stack, at increasing offsets from the caller's sp at the call (the
// callee's sp at entry). Two stack conventions exist: the standard one
// rounds every stack argument to an 8-byte slot; Apple's arm64 ABI packs
// fundamental types at their natural size and alignment (composites stay
// 8-aligned). The compiler and the checker compute the same layout from
// the signature — the checker from its own reading, so a lowering that
// reads the wrong slot is refused, not trusted.

// ArgClass describes one argument for the layout: the registers it takes
// when it fits, and its size and alignment on the stack under the packing
// convention (the standard one rounds an integer-class argument to 8-byte
// slots; a vector-class one — a float or a fixed vector, in v0–v7 while
// they fit — keeps its natural size and alignment, at least 8).
type ArgClass struct {
	Words  int   // registers when passed in registers (1 scalar, 2 span, chunks of a small record, 1 for a reference, 1 for a vector)
	Bytes  int64 // natural size on the stack (packed): 1, 2, 4, 8 for scalars; 16 for a span; chunks*8 for a record; 4, 8, 16 for a float or vector
	Align  int64 // natural alignment on the stack (packed)
	Vector bool  // the vector class: a float or a fixed vector, its registers v0–v7
}

// ArgPlace is where an argument lands.
type ArgPlace struct {
	Reg     int   // first register, when in registers (x0–x7, or v0–v7 for the vector class)
	Regs    int   // registers taken
	OnStack bool  // else at Offset from the entry sp
	Offset  int64 // entry-relative byte offset of the argument's first byte
	Vector  bool  // the vector class (its register is a v register)
}

// LayoutArguments places arguments in order — the integer class in x0–x7
// and the vector class in v0–v7 while they fit, each class going to the
// stack from its first argument that does not, at increasing offsets from
// one cursor shared by both (AAPCS64's NSAA); it returns the places and
// the bytes of the stack area they take, rounded to 16. Maintained line
// for line with Oak.ArgumentLayout.layoutFrom (spec/lean/Oak/ArgumentLayout.lean).
func LayoutArguments(args []ArgClass, packed bool) ([]ArgPlace, int64) {
	places := make([]ArgPlace, len(args))
	next, nextV, off, stack, stackV := 0, 0, int64(0), false, false
	for i, a := range args {
		if a.Vector {
			if !stackV && nextV+a.Words <= 8 {
				places[i] = ArgPlace{Reg: nextV, Regs: a.Words, Vector: true}
				nextV += a.Words
				continue
			}
			stackV = true
		} else {
			if !stack && next+a.Words <= 8 {
				places[i] = ArgPlace{Reg: next, Regs: a.Words}
				next += a.Words
				continue
			}
			stack = true
		}
		size, align := stackSize(packed, a), stackAlign(packed, a)
		off = (off + align - 1) / align * align
		places[i] = ArgPlace{OnStack: true, Offset: off, Vector: a.Vector}
		off += size
	}
	return places, (off + 15) / 16 * 16
}

// stackSize is the bytes an argument takes on the stack: its natural size
// when packed; otherwise an integer-class argument its registers' worth
// and a vector-class one its natural size, at least 8
// (Oak.ArgumentLayout.stackSize).
func stackSize(packed bool, a ArgClass) int64 {
	switch {
	case packed:
		return a.Bytes
	case a.Vector:
		return max(a.Bytes, 8)
	}
	return int64(a.Words) * 8
}

// stackAlign is its stack alignment: natural when packed; otherwise 8, or
// a vector-class argument's natural alignment when larger; never below 1
// (Oak.ArgumentLayout.stackAlign).
func stackAlign(packed bool, a ArgClass) int64 {
	align := int64(8)
	switch {
	case packed:
		align = a.Align
	case a.Vector:
		align = max(a.Align, 8)
	}
	return max(align, 1)
}

// argKind is the integer-class shape of a parameter for the layout.
type argKind int

const (
	argScalar argKind = iota // one register; on the stack its natural size (Bool the C int)
	argSpan                  // {base, len}: two registers; sixteen bytes
	argRecord                // a record: its chunks up to 16 bytes, else one register holding a reference
	argVector                // a float or vector: the v registers, outside the integer layout
)

// signatureArg is one parameter classified for the layout.
type signatureArg struct {
	param    *ast.FunctionParameter
	kind     argKind
	class    ArgClass
	scalarSz int64 // a scalar's natural size (its stack footprint under packing; the callee reads that many bytes)
	elem     int64 // a span's element size
	writable bool  // a span's `[*]` marker
	comp     Composite
	indirect bool // a record beyond 16 bytes, passed by reference
	problem  string
}

// classifyArguments reads a signature's parameters as the checker binds
// them (bindContract) and the backend places them (nativegen.argClassOf):
// a record its chunks or a reference, a span a pair, a scalar one
// register with its natural size, a float or vector outside the integer
// layout. A parameter the subset cannot carry has a problem and no class.
func classifyArguments(params []*ast.FunctionParameter, composites map[string]Composite) []signatureArg {
	out := make([]signatureArg, 0, len(params))
	for _, param := range params {
		arg := signatureArg{param: param}
		text := typeText(param.Type)
		if comp, isComposite := composites[text]; isComposite {
			arg.kind, arg.comp = argRecord, comp
			if comp.HFA {
				arg.problem = fmt.Sprintf("parameter %s: %s is a homogeneous floating-point aggregate (v registers); v1 leaves it to the C backend", param.Name.Value, text)
				out = append(out, arg)
				continue
			}
			regs, indirect := compositeChunks(comp.Size)
			arg.indirect = indirect
			arg.class = ArgClass{Words: regs, Bytes: int64(regs) * 8, Align: 8}
			out = append(out, arg)
			continue
		}
		if elem, writable, isSpan := spanShapeIn(param.Type, composites); isSpan {
			arg.kind, arg.elem, arg.writable = argSpan, elem, writable
			arg.class = ArgClass{Words: 2, Bytes: 16, Align: 8}
			out = append(out, arg)
			continue
		}
		class, ok := contractClass(param.Type)
		if !ok {
			arg.problem = fmt.Sprintf("parameter %s: type %s cannot cross the asm boundary in v1 (fixed-width integers, Bool, simd vectors)", param.Name.Value, text)
			out = append(out, arg)
			continue
		}
		if class == ClassV {
			// A float or a fixed vector: the vector class, in v0–v7 while
			// they fit, on the stack at its natural size and alignment past
			// them (a 128-bit vector sixteen bytes, sixteen-aligned).
			arg.kind = argVector
			bytes := int64(16)
			if bits, _, known := contractBits(param.Type); known && bits <= 64 {
				bytes = int64(bits+7) / 8
			}
			arg.class = ArgClass{Words: 1, Bytes: bytes, Align: bytes, Vector: true}
			out = append(out, arg)
			continue
		}
		size := int64(8)
		if bits, _, known := contractBits(param.Type); known && bits <= 32 {
			size = 4 // a narrow scalar's stack slot under the packing convention: the C int it widens to
			if text != "Bool" {
				size = int64(bits+7) / 8
			}
		}
		arg.kind, arg.scalarSz = argScalar, size
		arg.class = ArgClass{Words: 1, Bytes: size, Align: size}
		out = append(out, arg)
	}
	return out
}

// spanShapeIn is spanShape extended to spans of records: `[]R` / `[*]R`
// over a composite the function declares, with the record's size as the
// element size.
func spanShapeIn(expr ast.Expression, composites map[string]Composite) (elem int64, writable bool, ok bool) {
	if elem, writable, ok = spanShape(expr); ok {
		return elem, writable, true
	}
	indexExpr, isIndex := expr.(*ast.IndexExpression)
	if !isIndex || indexExpr.Dot {
		return 0, false, false
	}
	marker, isMarker := indexExpr.Index.(*ast.Identifier)
	if !isMarker || (marker.Value != "*" && marker.Value != "") {
		return 0, false, false
	}
	comp, isComposite := composites[typeText(indexExpr.Left)]
	if !isComposite || comp.Size <= 0 {
		return 0, false, false
	}
	return comp.Size, marker.Value == "*", true
}

// compositeChunks is the register class of a record parameter under
// AAPCS64: up to 16 bytes in ceil(size/8) consecutive registers, each an
// 8-byte chunk of the memory image; larger by reference in one register.
// Maintained line for line with Oak.ArgumentLayout.compositeChunks
// (spec/lean/Oak/ArgumentLayout.lean), which proves the chunks cover the
// record's bytes with none empty; asm/abi_refinement_test.go renders the
// layouts the Lean file states as examples.
func compositeChunks(size int64) (regs int, indirect bool) {
	if size > 16 {
		return 1, true
	}
	return int((size + 7) / 8), false
}
