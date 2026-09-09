package evaluator

// Interpreter semantics for the portable simd library
// (docs/spec/93-simd.md section 4): every operation runs natively with the
// exact lane semantics of Oak.Simd, so interpreted and compiled vector
// programs agree. Loads and stores are bounds-checked against the backing
// array, the interpreter analog of the native trap.

import (
	"encoding/binary"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
)

// simdLayout describes the lane geometry of one vector kind.
type simdLayout struct {
	VectorKind string
	ElemBytes  int
	Lanes      int
}

var simdLayouts = map[string]simdLayout{
	"u8x16": {VectorKind: "U8x16", ElemBytes: 1, Lanes: 16},
	"u16x8": {VectorKind: "U16x8", ElemBytes: 2, Lanes: 8},
	"u32x4": {VectorKind: "U32x4", ElemBytes: 4, Lanes: 4},
	"u64x2": {VectorKind: "U64x2", ElemBytes: 8, Lanes: 2},
}

func (layout simdLayout) laneMask() uint64 {
	if layout.ElemBytes == 8 {
		return ^uint64(0)
	}
	return (uint64(1) << (8 * layout.ElemBytes)) - 1
}

func (layout simdLayout) getLane(v *object.Vector, i int) uint64 {
	start := i * layout.ElemBytes
	switch layout.ElemBytes {
	case 1:
		return uint64(v.Bytes[start])
	case 2:
		return uint64(binary.LittleEndian.Uint16(v.Bytes[start : start+2]))
	case 4:
		return uint64(binary.LittleEndian.Uint32(v.Bytes[start : start+4]))
	default:
		return binary.LittleEndian.Uint64(v.Bytes[start : start+8])
	}
}

func (layout simdLayout) setLane(v *object.Vector, i int, lane uint64) {
	start := i * layout.ElemBytes
	switch layout.ElemBytes {
	case 1:
		v.Bytes[start] = byte(lane)
	case 2:
		binary.LittleEndian.PutUint16(v.Bytes[start:start+2], uint16(lane))
	case 4:
		binary.LittleEndian.PutUint32(v.Bytes[start:start+4], uint32(lane))
	default:
		binary.LittleEndian.PutUint64(v.Bytes[start:start+8], lane)
	}
}

// evalSimdOp implements the operation catalog of docs/spec/93-simd.md
// section 1.2. Member names come from the fixed compiler catalog; anything
// else is an error.
func evalSimdOp(member string, args []ast.Expression, env *object.Environment) object.Object {
	splitAt := strings.LastIndex(member, "_")
	if splitAt <= 0 {
		return newError("the simd library has no operation simd.%s", member)
	}
	opName, suffix := member[:splitAt], member[splitAt+1:]
	layout, known := simdLayouts[suffix]
	if !known {
		return newError("the simd library has no operation simd.%s", member)
	}

	evaluated := make([]object.Object, len(args))
	for i, arg := range args {
		evaluated[i] = Eval(arg, env)
		if isError(evaluated[i]) {
			return evaluated[i]
		}
	}

	switch opName {
	case "splat":
		operand, ok := argInteger(evaluated, 0)
		if !ok {
			return newError("simd.%s requires an integer operand", member)
		}
		result := &object.Vector{VectorKind: layout.VectorKind}
		for i := 0; i < layout.Lanes; i++ {
			layout.setLane(result, i, uint64(operand)&layout.laneMask())
		}
		return result

	case "load":
		buffer, offset, ok := argArrayOffset(evaluated)
		if !ok {
			return newError("simd.%s requires a view and a u32 offset", member)
		}
		if offset+layout.Lanes > buffer.length || offset < 0 {
			return newError("simd.%s out of bounds: offset %d, %d lanes, length %d",
				member, offset, layout.Lanes, buffer.length)
		}
		result := &object.Vector{VectorKind: layout.VectorKind}
		for i := 0; i < layout.Lanes; i++ {
			element, isInt := buffer.get(offset + i).(*object.Integer)
			if !isInt {
				return newError("simd.%s requires integer elements", member)
			}
			layout.setLane(result, i, uint64(element.Value)&layout.laneMask())
		}
		return result

	case "store":
		buffer, offset, ok := argArrayOffset(evaluated)
		if !ok {
			return newError("simd.%s requires a span and a u32 offset", member)
		}
		if !buffer.writable {
			return newError("simd.%s requires a writable span, got a read-only view", member)
		}
		vec, isVec := evaluated[2].(*object.Vector)
		if !isVec || vec.VectorKind != layout.VectorKind {
			return newError("simd.%s requires a simd.%s value", member, layout.VectorKind)
		}
		if offset+layout.Lanes > buffer.length || offset < 0 {
			return newError("simd.%s out of bounds: offset %d, %d lanes, length %d",
				member, offset, layout.Lanes, buffer.length)
		}
		for i := 0; i < layout.Lanes; i++ {
			buffer.set(offset+i, &object.Integer{Value: int64(layout.getLane(vec, i))})
		}
		return NULL

	case "add", "sub", "and", "or", "xor", "min", "max", "eq":
		a, b, ok := argVectorPair(evaluated, layout.VectorKind)
		if !ok {
			return newError("simd.%s requires two simd.%s values", member, layout.VectorKind)
		}
		result := &object.Vector{VectorKind: layout.VectorKind}
		mask := layout.laneMask()
		for i := 0; i < layout.Lanes; i++ {
			x, y := layout.getLane(a, i), layout.getLane(b, i)
			var lane uint64
			switch opName {
			case "add":
				lane = (x + y) & mask
			case "sub":
				lane = (x - y) & mask
			case "and":
				lane = x & y
			case "or":
				lane = x | y
			case "xor":
				lane = x ^ y
			case "min":
				lane = min(x, y)
			case "max":
				lane = max(x, y)
			case "eq":
				// Two-valued mask (Oak.Simd.eqMask): all-ones or zero.
				if x == y {
					lane = mask
				} else {
					lane = 0
				}
			}
			layout.setLane(result, i, lane)
		}
		return result

	case "any", "all":
		vec, isVec := evaluated[0].(*object.Vector)
		if len(evaluated) != 1 || !isVec || vec.VectorKind != layout.VectorKind {
			return newError("simd.%s requires a simd.%s value", member, layout.VectorKind)
		}
		anyNonzero, allNonzero := false, true
		for i := 0; i < layout.Lanes; i++ {
			if layout.getLane(vec, i) != 0 {
				anyNonzero = true
			} else {
				allNonzero = false
			}
		}
		if opName == "any" {
			return nativeBool(anyNonzero)
		}
		return nativeBool(allNonzero)
	}
	return newError("the simd library has no operation simd.%s", member)
}

func nativeBool(value bool) object.Object {
	if value {
		return TRUE
	}
	return FALSE
}

func argInteger(args []object.Object, i int) (int64, bool) {
	if i >= len(args) {
		return 0, false
	}
	integer, ok := args[i].(*object.Integer)
	if !ok {
		return 0, false
	}
	return integer.Value, true
}

// argArrayOffset reads a (view-or-array, offset) argument pair as an
// element window: owned arrays and borrowed views/spans alike.
func argArrayOffset(args []object.Object) (window, int, bool) {
	if len(args) < 2 {
		return window{}, 0, false
	}
	buffer, isWindow := elementWindow(args[0])
	offset, isInt := argInteger(args, 1)
	if !isWindow || !isInt {
		return window{}, 0, false
	}
	return buffer, int(offset), true
}

func argVectorPair(args []object.Object, kind string) (*object.Vector, *object.Vector, bool) {
	if len(args) != 2 {
		return nil, nil, false
	}
	a, aOK := args[0].(*object.Vector)
	b, bOK := args[1].(*object.Vector)
	if !aOK || !bOK || a.VectorKind != kind || b.VectorKind != kind {
		return nil, nil, false
	}
	return a, b, true
}
