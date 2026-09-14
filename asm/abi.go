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

// ArgClass describes one integer-class argument for the layout: the
// registers it takes when it fits, and its size and alignment on the stack
// under the packing convention (the standard one rounds both to 8).
type ArgClass struct {
	Words int   // registers when passed in registers (1 scalar, 2 span, chunks of a small record, 1 for a reference)
	Bytes int64 // natural size on the stack (packed): 1, 2, 4, 8 for scalars; 16 for a span; chunks*8 for a record
	Align int64 // natural alignment on the stack (packed)
}

// ArgPlace is where an argument lands.
type ArgPlace struct {
	Reg     int   // first register, when in registers
	Regs    int   // registers taken
	OnStack bool  // else at Offset from the entry sp
	Offset  int64 // entry-relative byte offset of the argument's first byte
}

// LayoutArguments places integer-class arguments in order; it returns the
// places and the bytes of the stack area they take, rounded to 16.
func LayoutArguments(args []ArgClass, packed bool) ([]ArgPlace, int64) {
	places := make([]ArgPlace, len(args))
	next, off, stack := 0, int64(0), false
	for i, a := range args {
		if !stack && next+a.Words <= 8 {
			places[i] = ArgPlace{Reg: next, Regs: a.Words}
			next += a.Words
			continue
		}
		stack = true
		size, align := int64(a.Words)*8, int64(8)
		if packed {
			size, align = a.Bytes, a.Align
		}
		if align < 1 {
			align = 1
		}
		off = (off + align - 1) / align * align
		places[i] = ArgPlace{OnStack: true, Offset: off}
		off += size
	}
	return places, (off + 15) / 16 * 16
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
			regs, indirect := 1, comp.Size > 16
			if !indirect {
				regs = int((comp.Size + 7) / 8)
			}
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
			arg.kind = argVector
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
