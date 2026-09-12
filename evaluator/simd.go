package evaluator

// Interpreter semantics for the portable simd library
// (docs/spec/93-simd.md section 4): every operation runs natively with the
// exact lane semantics of Oak.Simd, so interpreted and compiled vector
// programs agree. Loads and stores are bounds-checked against the backing
// array, the interpreter analog of the native trap.

import (
	"encoding/binary"
	"math"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
)

// simdLayout describes the lane geometry of one vector kind.
type simdLayout struct {
	VectorKind string
	ElemBytes  int
	Lanes      int
	// FloatBits is 32 or 64 for the floating-point vectors (docs/spec/
	// 20-types.md section 11.3.7), whose lanes hold IEEE bit patterns.
	FloatBits int
}

var simdLayouts = map[string]simdLayout{
	"u8x16": {VectorKind: "U8x16", ElemBytes: 1, Lanes: 16},
	"u16x8": {VectorKind: "U16x8", ElemBytes: 2, Lanes: 8},
	"u32x4": {VectorKind: "U32x4", ElemBytes: 4, Lanes: 4},
	"u64x2": {VectorKind: "U64x2", ElemBytes: 8, Lanes: 2},
	"f32x4": {VectorKind: "F32x4", ElemBytes: 4, Lanes: 4, FloatBits: 32},
	"f64x2": {VectorKind: "F64x2", ElemBytes: 8, Lanes: 2, FloatBits: 64},
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

	if layout.FloatBits != 0 {
		return evalSimdFloatOp(member, opName, layout, evaluated)
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

	case "shr":
		// Lane-wise logical shift right; a count reaching the lane width
		// traps, as the scalar shift does (docs/spec/93-simd.md §1.2).
		vec, isVec := evaluated[0].(*object.Vector)
		count, okCount := argInteger(evaluated, 1)
		if len(evaluated) != 2 || !isVec || vec.VectorKind != layout.VectorKind || !okCount {
			return newError("simd.%s requires a simd.%s value and a u32 count", member, layout.VectorKind)
		}
		if count < 0 || count >= int64((layout.ElemBytes*8)) {
			return newError("simd.%s: shift count %d reaches the lane width %d (trap)", member, count, (layout.ElemBytes * 8))
		}
		result := &object.Vector{VectorKind: layout.VectorKind}
		for i := 0; i < layout.Lanes; i++ {
			layout.setLane(result, i, layout.getLane(vec, i)>>uint(count))
		}
		return result

	case "tbl":
		// Byte-table lookup: an index at or above 16 selects 0 (Oak.Simd.tbl).
		table, idx, ok := argVectorPair(evaluated, layout.VectorKind)
		if !ok || layout.VectorKind != "U8x16" {
			return newError("simd.%s requires two simd.U8x16 values", member)
		}
		result := &object.Vector{VectorKind: layout.VectorKind}
		for i := 0; i < 16; i++ {
			index := layout.getLane(idx, i)
			var lane uint64
			if index < 16 {
				lane = layout.getLane(table, int(index))
			}
			layout.setLane(result, i, lane)
		}
		return result

	case "prev":
		// The 16 bytes ending n before the end of prev ++ cur (Oak.Simd.prev).
		if len(evaluated) != 3 || layout.VectorKind != "U8x16" {
			return newError("simd.%s requires two simd.U8x16 values and a u32 count", member)
		}
		prev, cur, ok := argVectorPair(evaluated[:2], layout.VectorKind)
		count, okCount := argInteger(evaluated, 2)
		if !ok || !okCount {
			return newError("simd.%s requires two simd.U8x16 values and a u32 count", member)
		}
		if count < 0 || count > 16 {
			return newError("simd.%s: byte count %d exceeds the vector (trap)", member, count)
		}
		n := int(count)
		result := &object.Vector{VectorKind: layout.VectorKind}
		for i := 0; i < 16; i++ {
			if i < n {
				layout.setLane(result, i, layout.getLane(prev, 16-n+i))
			} else {
				layout.setLane(result, i, layout.getLane(cur, i-n))
			}
		}
		return result

	case "add", "sub", "subs", "and", "or", "xor", "min", "max", "eq":
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
			case "subs":
				// Saturating: never below zero (Oak.Simd.subSat).
				if x > y {
					lane = x - y
				} else {
					lane = 0
				}
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

// evalSimdFloatOp implements the floating-point vector operations
// (docs/spec/20-types.md section 11.3.7). Lanes hold IEEE bit patterns;
// each lane obeys the scalar rules: f32 arithmetic in float32, fma in one
// rounding, min/max with the IEEE 754-2019 semantics, reduce_add as the
// pairwise tree.
func evalSimdFloatOp(member, opName string, layout simdLayout, evaluated []object.Object) object.Object {
	bits := layout.FloatBits
	lane := func(v *object.Vector, i int) float64 {
		if bits == 32 {
			return float64(math.Float32frombits(uint32(layout.getLane(v, i))))
		}
		return math.Float64frombits(layout.getLane(v, i))
	}
	setLane := func(v *object.Vector, i int, x float64) {
		if bits == 32 {
			layout.setLane(v, i, uint64(math.Float32bits(float32(x))))
			return
		}
		layout.setLane(v, i, math.Float64bits(x))
	}
	round := func(x float64) float64 {
		if bits == 32 {
			return float64(float32(x))
		}
		return x
	}
	floatArg := func(i int) (float64, bool) {
		if i >= len(evaluated) {
			return 0, false
		}
		f, ok := evaluated[i].(*object.Float)
		if !ok {
			return 0, false
		}
		return f.Value, true
	}
	vectorArg := func(i int) (*object.Vector, bool) {
		if i >= len(evaluated) {
			return nil, false
		}
		v, ok := evaluated[i].(*object.Vector)
		return v, ok && v.VectorKind == layout.VectorKind
	}
	result := &object.Vector{VectorKind: layout.VectorKind}

	switch opName {
	case "splat":
		x, ok := floatArg(0)
		if !ok {
			return newError("simd.%s requires a floating-point operand", member)
		}
		for i := 0; i < layout.Lanes; i++ {
			setLane(result, i, x)
		}
		return result
	case "load":
		buffer, offset, ok := argArrayOffset(evaluated)
		if !ok {
			return newError("simd.%s requires a view and a u32 offset", member)
		}
		if offset+layout.Lanes > buffer.length || offset < 0 {
			return newError("simd.%s out of bounds: offset %d, %d lanes, length %d", member, offset, layout.Lanes, buffer.length)
		}
		for i := 0; i < layout.Lanes; i++ {
			element, isFloat := buffer.get(offset + i).(*object.Float)
			if !isFloat {
				return newError("simd.%s requires floating-point elements", member)
			}
			setLane(result, i, element.Value)
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
		vec, isVec := vectorArg(2)
		if !isVec {
			return newError("simd.%s requires a simd.%s value", member, layout.VectorKind)
		}
		if offset+layout.Lanes > buffer.length || offset < 0 {
			return newError("simd.%s out of bounds: offset %d, %d lanes, length %d", member, offset, layout.Lanes, buffer.length)
		}
		for i := 0; i < layout.Lanes; i++ {
			buffer.set(offset+i, floatOf(lane(vec, i), bits))
		}
		return NULL
	case "add", "sub", "mul", "div", "min", "max":
		a, aOK := vectorArg(0)
		b, bOK := vectorArg(1)
		if len(evaluated) != 2 || !aOK || !bOK {
			return newError("simd.%s requires two simd.%s values", member, layout.VectorKind)
		}
		for i := 0; i < layout.Lanes; i++ {
			x, y := lane(a, i), lane(b, i)
			var r float64
			switch opName {
			case "add":
				r = round(x + y)
				if bits == 32 {
					r = float64(float32(x) + float32(y))
				}
			case "sub":
				r = round(x - y)
				if bits == 32 {
					r = float64(float32(x) - float32(y))
				}
			case "mul":
				r = round(x * y)
				if bits == 32 {
					r = float64(float32(x) * float32(y))
				}
			case "div":
				r = round(x / y)
				if bits == 32 {
					r = float64(float32(x) / float32(y))
				}
			case "min":
				r = ieeeMinimum(x, y)
			case "max":
				r = ieeeMaximum(x, y)
			}
			setLane(result, i, r)
		}
		return result
	case "sqrt", "neg", "abs":
		a, ok := vectorArg(0)
		if len(evaluated) != 1 || !ok {
			return newError("simd.%s requires a simd.%s value", member, layout.VectorKind)
		}
		for i := 0; i < layout.Lanes; i++ {
			x := lane(a, i)
			var r float64
			switch opName {
			case "sqrt":
				r = round(math.Sqrt(x))
			case "neg":
				r = -x
			case "abs":
				r = math.Abs(x)
			}
			setLane(result, i, r)
		}
		return result
	case "fma":
		a, aOK := vectorArg(0)
		b, bOK := vectorArg(1)
		c, cOK := vectorArg(2)
		if len(evaluated) != 3 || !aOK || !bOK || !cOK {
			return newError("simd.%s requires three simd.%s values", member, layout.VectorKind)
		}
		for i := 0; i < layout.Lanes; i++ {
			if bits == 32 {
				setLane(result, i, fma32(float32(lane(a, i)), float32(lane(b, i)), float32(lane(c, i))))
			} else {
				setLane(result, i, math.FMA(lane(a, i), lane(b, i), lane(c, i)))
			}
		}
		return result
	case "extract":
		v, vOK := vectorArg(0)
		index, iOK := argInteger(evaluated, 1)
		if len(evaluated) != 2 || !vOK || !iOK {
			return newError("simd.%s requires a simd.%s value and a u32 lane", member, layout.VectorKind)
		}
		if index < 0 || int(index) >= layout.Lanes {
			return newError("simd.%s lane %d out of range (the compiled program traps)", member, index)
		}
		return floatOf(lane(v, int(index)), bits)
	case "insert":
		v, vOK := vectorArg(0)
		index, iOK := argInteger(evaluated, 1)
		x, xOK := floatArg(2)
		if len(evaluated) != 3 || !vOK || !iOK || !xOK {
			return newError("simd.%s requires a simd.%s value, a u32 lane, and a %s", member, layout.VectorKind, map[int]string{32: "f32", 64: "f64"}[bits])
		}
		if index < 0 || int(index) >= layout.Lanes {
			return newError("simd.%s lane %d out of range (the compiled program traps)", member, index)
		}
		result.Bytes = v.Bytes
		setLane(result, int(index), x)
		return result
	case "reduce_add":
		v, ok := vectorArg(0)
		if len(evaluated) != 1 || !ok {
			return newError("simd.%s requires a simd.%s value", member, layout.VectorKind)
		}
		// The pairwise tree is the semantics.
		if layout.Lanes == 4 {
			if bits == 32 {
				l := [4]float32{float32(lane(v, 0)), float32(lane(v, 1)), float32(lane(v, 2)), float32(lane(v, 3))}
				return floatOf(float64((l[0]+l[1])+(l[2]+l[3])), 32)
			}
			return floatOf((lane(v, 0)+lane(v, 1))+(lane(v, 2)+lane(v, 3)), 64)
		}
		if bits == 32 {
			return floatOf(float64(float32(lane(v, 0))+float32(lane(v, 1))), 32)
		}
		return floatOf(lane(v, 0)+lane(v, 1), 64)
	}
	return newError("the simd library has no operation simd.%s", member)
}
