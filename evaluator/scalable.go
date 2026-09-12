package evaluator

// The scalable vector API (docs/spec/93-simd.md section 4): the interpreter
// realizes an active extent as min(remaining, capacity) with the portable
// capacity (one 16-byte vector), and every operation touches only the
// active lanes. ScalableExtentCap lowers the capacity so a test can show a
// program's result does not depend on the extent the backend chose — the
// determinism the spec promises (Oak.Simd.chunked_*).

import (
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
)

// ScalableExtentCap bounds the active extent in lanes (0: the portable
// capacity). Tests set it to stress strip-mined loops.
var ScalableExtentCap = 0

var scalableLayouts = map[string]simdLayout{
	"active_u8":  {VectorKind: "ScalableU8", ElemBytes: 1, Lanes: 16},
	"active_u32": {VectorKind: "ScalableU32", ElemBytes: 4, Lanes: 4},
}

// isScalableMember reports the scalable-API operations.
func isScalableMember(member string) bool {
	return member == "count" || strings.HasPrefix(member, "active_") || strings.Contains(member, "_active_")
}

// activeCount reads an Active value's extent (lanes).
func activeCount(obj object.Object) (int, bool) {
	active, ok := obj.(*object.Vector)
	if !ok || active.VectorKind != "Active" {
		return 0, false
	}
	return int(active.Bytes[0]) | int(active.Bytes[1])<<8 | int(active.Bytes[2])<<16 | int(active.Bytes[3])<<24, true
}

func makeActive(count int) *object.Vector {
	active := &object.Vector{VectorKind: "Active"}
	active.Bytes[0], active.Bytes[1], active.Bytes[2], active.Bytes[3] = byte(count), byte(count>>8), byte(count>>16), byte(count>>24)
	return active
}

func evalScalableOp(member string, args []ast.Expression, env *object.Environment) object.Object {
	evaluated := make([]object.Object, len(args))
	for i, arg := range args {
		evaluated[i] = Eval(arg, env)
		if isError(evaluated[i]) {
			return evaluated[i]
		}
	}
	if member == "count" {
		count, ok := activeCount(evaluated[0])
		if !ok {
			return newError("simd.count requires an Active extent")
		}
		return &object.Integer{Value: int64(count)}
	}
	// active_u8(remaining): the extent.
	if layout, isActive := scalableLayouts[member]; isActive {
		remaining, ok := argInteger(evaluated, 0)
		if !ok || remaining < 0 {
			return newError("simd.%s requires a u32 remaining count", member)
		}
		capacity := layout.Lanes
		if ScalableExtentCap > 0 && ScalableExtentCap < capacity {
			capacity = ScalableExtentCap
		}
		count := int(remaining)
		if count > capacity {
			count = capacity
		}
		return makeActive(count)
	}
	splitAt := strings.Index(member, "_active_")
	if splitAt <= 0 {
		return newError("the simd library has no operation simd.%s", member)
	}
	opName, suffix := member[:splitAt], member[splitAt+1:]
	layout, known := scalableLayouts[suffix]
	if !known {
		return newError("the simd library has no operation simd.%s", member)
	}
	count, ok := activeCount(evaluated[len(evaluated)-1])
	if !ok || count > layout.Lanes {
		return newError("simd.%s requires an Active extent of %s lanes as its last operand", member, layout.VectorKind)
	}
	vector := func(i int) (*object.Vector, bool) {
		v, ok := evaluated[i].(*object.Vector)
		return v, ok && v.VectorKind == layout.VectorKind
	}
	switch opName {
	case "splat":
		operand, ok := argInteger(evaluated, 0)
		if !ok {
			return newError("simd.%s requires an integer operand", member)
		}
		result := &object.Vector{VectorKind: layout.VectorKind}
		for i := 0; i < count; i++ {
			layout.setLane(result, i, uint64(operand)&layout.laneMask())
		}
		return result
	case "load":
		buffer, offset, ok := argArrayOffset(evaluated)
		if !ok {
			return newError("simd.%s requires a view and a u32 offset", member)
		}
		if offset < 0 || offset+count > buffer.length {
			return newError("simd.%s out of bounds: offset %d, %d active lanes, length %d", member, offset, count, buffer.length)
		}
		result := &object.Vector{VectorKind: layout.VectorKind}
		for i := 0; i < count; i++ {
			element, isInt := buffer.get(offset + i).(*object.Integer)
			if !isInt {
				return newError("simd.%s requires integer elements", member)
			}
			layout.setLane(result, i, uint64(element.Value)&layout.laneMask())
		}
		return result
	case "store":
		buffer, offset, ok := argArrayOffset(evaluated)
		v, isVector := vector(2)
		if !ok || !isVector {
			return newError("simd.%s requires a span, a u32 offset, and a %s", member, layout.VectorKind)
		}
		if !buffer.writable {
			return newError("simd.%s requires a span, not a view", member)
		}
		if offset < 0 || offset+count > buffer.length {
			return newError("simd.%s out of bounds: offset %d, %d active lanes, length %d", member, offset, count, buffer.length)
		}
		for i := 0; i < count; i++ {
			buffer.set(offset+i, &object.Integer{Value: int64(layout.getLane(v, i))})
		}
		return NULL
	case "load_masked":
		// Lanes whose mask lane is zero are not read and come back zero;
		// the whole extent still lies within the view.
		buffer, offset, ok := argArrayOffset(evaluated)
		m, isVector := vector(2)
		if !ok || !isVector {
			return newError("simd.%s requires a view, a u32 offset, and a %s mask", member, layout.VectorKind)
		}
		if offset < 0 || offset+count > buffer.length {
			return newError("simd.%s out of bounds: offset %d, %d active lanes, length %d", member, offset, count, buffer.length)
		}
		result := &object.Vector{VectorKind: layout.VectorKind}
		for i := 0; i < count; i++ {
			if layout.getLane(m, i) == 0 {
				continue
			}
			element, isInt := buffer.get(offset + i).(*object.Integer)
			if !isInt {
				return newError("simd.%s requires integer elements", member)
			}
			layout.setLane(result, i, uint64(element.Value)&layout.laneMask())
		}
		return result
	case "store_masked":
		// Only lanes whose mask lane is nonzero are written; the others
		// keep the span's values.
		buffer, offset, ok := argArrayOffset(evaluated)
		m, isMask := vector(2)
		v, isVector := vector(3)
		if !ok || !isMask || !isVector {
			return newError("simd.%s requires a span, a u32 offset, a %s mask, and a %s", member, layout.VectorKind, layout.VectorKind)
		}
		if !buffer.writable {
			return newError("simd.%s requires a span, not a view", member)
		}
		if offset < 0 || offset+count > buffer.length {
			return newError("simd.%s out of bounds: offset %d, %d active lanes, length %d", member, offset, count, buffer.length)
		}
		for i := 0; i < count; i++ {
			if layout.getLane(m, i) != 0 {
				buffer.set(offset+i, &object.Integer{Value: int64(layout.getLane(v, i))})
			}
		}
		return NULL
	case "select":
		m, isMask := vector(0)
		x, okX := vector(1)
		y, okY := vector(2)
		if !isMask || !okX || !okY {
			return newError("simd.%s requires a %s mask and two %s operands", member, layout.VectorKind, layout.VectorKind)
		}
		result := &object.Vector{VectorKind: layout.VectorKind}
		for i := 0; i < count; i++ {
			if layout.getLane(m, i) != 0 {
				layout.setLane(result, i, layout.getLane(x, i))
			} else {
				layout.setLane(result, i, layout.getLane(y, i))
			}
		}
		return result
	case "count_nonzero":
		m, isMask := vector(0)
		if !isMask {
			return newError("simd.%s requires a %s mask", member, layout.VectorKind)
		}
		n := 0
		for i := 0; i < count; i++ {
			if layout.getLane(m, i) != 0 {
				n++
			}
		}
		return &object.Integer{Value: int64(n)}
	case "shr":
		v, isVector := vector(0)
		n, isInt := argInteger(evaluated, 1)
		if !isVector || !isInt {
			return newError("simd.%s requires a %s and a u32 count", member, layout.VectorKind)
		}
		if n < 0 || int(n) >= layout.ElemBytes*8 {
			return newError("simd.%s: shift count %d reaches the lane width", member, n)
		}
		result := &object.Vector{VectorKind: layout.VectorKind}
		for i := 0; i < count; i++ {
			layout.setLane(result, i, layout.getLane(v, i)>>uint(n))
		}
		return result
	case "any", "all":
		v, isVector := vector(0)
		if !isVector {
			return newError("simd.%s requires a %s", member, layout.VectorKind)
		}
		for i := 0; i < count; i++ {
			nonzero := layout.getLane(v, i) != 0
			if opName == "any" && nonzero {
				return nativeBool(true)
			}
			if opName == "all" && !nonzero {
				return nativeBool(false)
			}
		}
		return nativeBool(opName == "all")
	case "reduce_add":
		v, isVector := vector(0)
		if !isVector {
			return newError("simd.%s requires a %s", member, layout.VectorKind)
		}
		sum := uint64(0)
		for i := 0; i < count; i++ {
			sum = (sum + layout.getLane(v, i)) & layout.laneMask()
		}
		return &object.Integer{Value: int64(sum)}
	}
	a, okA := vector(0)
	b, okB := vector(1)
	if !okA || !okB {
		return newError("simd.%s requires two %s operands", member, layout.VectorKind)
	}
	result := &object.Vector{VectorKind: layout.VectorKind}
	mask := layout.laneMask()
	for i := 0; i < count; i++ {
		x, y := layout.getLane(a, i), layout.getLane(b, i)
		var lane uint64
		switch opName {
		case "add":
			lane = (x + y) & mask
		case "sub":
			lane = (x - y) & mask
		case "subs":
			if x > y {
				lane = x - y
			}
		case "and":
			lane = x & y
		case "or":
			lane = x | y
		case "xor":
			lane = x ^ y
		case "min":
			lane = x
			if y < x {
				lane = y
			}
		case "max":
			lane = x
			if y > x {
				lane = y
			}
		case "eq":
			if x == y {
				lane = mask
			}
		case "ne":
			if x != y {
				lane = mask
			}
		case "lt":
			if x < y {
				lane = mask
			}
		case "gt":
			if x > y {
				lane = mask
			}
		default:
			return newError("the simd library has no operation simd.%s", member)
		}
		layout.setLane(result, i, lane)
	}
	return result
}
