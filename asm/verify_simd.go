package asm

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// The Oak side of the vector increment (docs/spec/94-assembler.md §8): a
// `simd.<Name>` type is an owned array of lanes, and a `simd.<op>_<shape>`
// call is the lane function spec/lean/Oak/Simd.lean gives the operation
// (the same constructors the machine side applies to the NEON
// instructions, asm/verify_vector.go), so a vector local, parameter, or
// result is an aggregate of lane terms like any other array.

// simdMember recognizes the callee `simd.<member>` of a call.
func simdMember(fn ast.Expression) (string, bool) {
	access, isAccess := fn.(*ast.IndexExpression)
	if !isAccess || !access.Dot {
		return "", false
	}
	library, isLibrary := access.Left.(*ast.Identifier)
	member, isMember := access.Index.(*ast.Identifier)
	if !isLibrary || !isMember || library.Value != "simd" {
		return "", false
	}
	return member.Value, true
}

// simdOpShape splits a vector member into its operation and shape
// ("tbl_u8x16" → "tbl", U8x16; "fma_f32x4" → "fma", F32x4); the scalar
// helpers (ctz_u32, popcount_u64) are not vector operations.
func simdOpShape(member string) (string, typechecker.SimdShape, bool) {
	underscore := strings.LastIndexByte(member, '_')
	if underscore <= 0 {
		return "", typechecker.SimdShape{}, false
	}
	shape, ok := typechecker.SimdShapeBySuffix(member[underscore+1:])
	if !ok {
		return "", typechecker.SimdShape{}, false
	}
	return member[:underscore], shape, true
}

// simdVectorOps are the members producing a vector, with their arity.
var simdVectorOps = map[string]int{"splat": 1, "load": 2, "add": 2, "sub": 2, "and": 2, "or": 2, "xor": 2, "min": 2, "max": 2, "eq": 2, "subs": 2, "shr": 2, "tbl": 2, "prev": 3,
	"mul": 2, "div": 2, "fma": 3, "sqrt": 1, "neg": 1, "abs": 1, "insert": 3}

// simdFloatOps are the operations the float shapes have (docs/spec/93-simd.md
// §1.2a) and simdIntegerOps the integer shapes' (§1.2); the two sets share
// splat, load, store, add, sub, min, and max.
var simdFloatOps = map[string]bool{"splat": true, "load": true, "add": true, "sub": true, "mul": true, "div": true, "fma": true, "min": true, "max": true, "sqrt": true, "neg": true, "abs": true, "insert": true, "extract": true, "reduce_add": true, "store": true}
var simdIntegerOps = map[string]bool{"splat": true, "load": true, "store": true, "add": true, "sub": true, "and": true, "or": true, "xor": true, "min": true, "max": true, "eq": true, "subs": true, "shr": true, "tbl": true, "prev": true, "any": true, "all": true, "movemask": true}

// simdFloatScalarWidth is the lane width of a scalar-producing float
// member (extract, reduce_add), or false.
func simdFloatScalarWidth(member string) (int, bool) {
	op, shape, ok := simdOpShape(member)
	if !ok || !shape.Float || (op != "extract" && op != "reduce_add") {
		return 0, false
	}
	return laneWidth(shape), true
}

// simdScalarWidth is the width of a scalar-producing member (any/all as
// Bool, movemask as u32, the mask helpers at their integer width).
func simdScalarWidth(member string) (int, bool) {
	switch member {
	case "ctz_u32", "popcount_u32":
		return 32, true
	case "ctz_u64", "popcount_u64":
		return 64, true
	}
	op, shape, ok := simdOpShape(member)
	if !ok {
		return 0, false
	}
	switch op {
	case "any", "all":
		return 1, true
	case "movemask":
		return 32, true
	case "extract", "reduce_add":
		if shape.Float {
			return laneWidth(shape), true
		}
	}
	return 0, false
}

// vectorType is the lane array of a vector shape, one shared *oakType per
// shape (the inliner compares a callee's declared result by identity).
func (lo *oakLowering) vectorType(shape typechecker.SimdShape) *oakType {
	name := "simd." + shape.TypeName
	if typ, cached := lo.types[name]; cached && typ != nil {
		return typ
	}
	if lo.types == nil {
		lo.types = map[string]*oakType{}
	}
	typ := vectorTypeOf(shape)
	lo.types[name] = typ
	return typ
}

// vectorTypeOf is the lane array of a shape (structural; compare with
// sameType, or take the shared instance from vectorType).
func vectorTypeOf(shape typechecker.SimdShape) *oakType {
	return &oakType{kind: oakArray, name: "simd." + shape.TypeName, length: int64(shape.Lanes), elem: &oakType{kind: oakScalar, width: laneWidth(shape)}}
}

// vectorLanes lowers a vector-valued expression to its lane terms.
func (lo *oakLowering) vectorLanes(expr ast.Expression, shape typechecker.SimdShape) ([]*term, string, bool) {
	value, reason, ok := lo.aggregateValue(expr, lo.vectorType(shape))
	if !ok {
		return nil, reason, false
	}
	lanes := make([]*term, len(value.elems))
	for k, elem := range value.elems {
		if elem.scalar == nil {
			return nil, "a vector lane without a value", false
		}
		lanes[k] = narrowLane(elem.scalar, laneWidth(shape))
	}
	return lanes, "", true
}

// vectorOfLanes wraps lane terms as the aggregate value of the type.
func vectorOfLanes(lanes []*term, typ *oakType) *oakValue {
	out := &oakValue{typ: typ}
	for _, lane := range lanes {
		out.elems = append(out.elems, &oakValue{typ: typ.elem, scalar: lane})
	}
	return out
}

// simdVectorValue lowers a vector-producing `simd.<op>_<shape>(...)` call
// to the aggregate of its lanes (Oak.Simd's definitions, lane by lane).
func (lo *oakLowering) simdVectorValue(member string, args []ast.Expression, typ *oakType) (*oakValue, string, bool) {
	op, shape, ok := simdOpShape(member)
	if !ok {
		return nil, fmt.Sprintf("the simd operation %s", member), false
	}
	arity, isVectorOp := simdVectorOps[op]
	if !isVectorOp {
		return nil, fmt.Sprintf("simd.%s in vector position", member), false
	}
	if len(args) != arity {
		return nil, fmt.Sprintf("simd.%s with %d operands", member, len(args)), false
	}
	if !sameType(typ, vectorTypeOf(shape)) {
		return nil, fmt.Sprintf("simd.%s where a %s is expected", member, typ.name), false
	}
	bits := laneWidth(shape)
	if (shape.Float && !simdFloatOps[op]) || (!shape.Float && !simdIntegerOps[op]) {
		return nil, fmt.Sprintf("simd.%s (the operation is not one of the %s's)", member, shape.TypeName), false
	}
	binary := func(fn func(x, y *term) *term) (*oakValue, string, bool) {
		left, reason, ok := lo.vectorLanes(args[0], shape)
		if !ok {
			return nil, reason, false
		}
		right, reason, ok := lo.vectorLanes(args[1], shape)
		if !ok {
			return nil, reason, false
		}
		lanes := make([]*term, len(left))
		for k := range lanes {
			lanes[k] = fn(left[k], right[k])
		}
		return vectorOfLanes(lanes, typ), "", true
	}
	switch op {
	case "splat":
		// The operand at its own width, masked to the lane (a wider
		// parameter keeps its low bits, as dup does); a float operand at
		// the lane's format (a literal's bits are those of its width).
		width := 64
		if shape.Float {
			width = bits
		}
		value, reason, ok := lo.lower(args[0], width)
		if !ok {
			return nil, reason, false
		}
		lane := narrowLane(value, bits)
		lanes := make([]*term, shape.Lanes)
		for k := range lanes {
			lanes[k] = lane
		}
		return vectorOfLanes(lanes, typ), "", true
	case "load":
		lanes, reason, ok := lo.vectorLoad(args[0], args[1], shape)
		if !ok {
			return nil, reason, false
		}
		return vectorOfLanes(lanes, typ), "", true
	case "add", "sub", "and", "or", "xor", "min", "max", "eq", "subs", "mul", "div":
		if shape.Float {
			// The IEEE operation per lane (asm/floats_ops.go), min/max the
			// 754-2019 minimum/maximum (floatMinMax).
			switch op {
			case "min", "max":
				return binary(func(x, y *term) *term { return floatMinMax(op, x, y, bits) })
			}
			mnemonic := map[string]string{"add": "fadd", "sub": "fsub", "mul": "fmul", "div": "fdiv"}[op]
			return binary(func(x, y *term) *term { return floatTerm(mnemonic, bits, x, y) })
		}
		lane := map[string]string{"add": "add", "sub": "sub", "and": "and", "or": "or", "xor": "xor", "min": "umin", "max": "umax", "eq": "cmeq", "subs": "uqsub"}[op]
		return binary(func(x, y *term) *term { return laneBinary(lane, x, y) })
	case "fma":
		a, reason, ok := lo.vectorLanes(args[0], shape)
		if !ok {
			return nil, reason, false
		}
		b, reason, ok := lo.vectorLanes(args[1], shape)
		if !ok {
			return nil, reason, false
		}
		c, reason, ok := lo.vectorLanes(args[2], shape)
		if !ok {
			return nil, reason, false
		}
		lanes := make([]*term, len(a))
		for k := range lanes {
			lanes[k] = floatTerm("fma", bits, a[k], b[k], c[k])
		}
		return vectorOfLanes(lanes, typ), "", true
	case "sqrt", "neg", "abs":
		lanes, reason, ok := lo.vectorLanes(args[0], shape)
		if !ok {
			return nil, reason, false
		}
		out := make([]*term, len(lanes))
		for k := range out {
			switch op {
			case "sqrt":
				out[k] = floatTerm("fsqrt", bits, lanes[k])
			case "neg":
				out[k] = floatNeg(lanes[k], bits)
			default:
				out[k] = floatAbs(lanes[k], bits)
			}
		}
		return vectorOfLanes(out, typ), "", true
	case "insert":
		// The vector with one lane replaced; the lane is a constant here
		// (the backend traps on an index past the lanes).
		lanes, reason, ok := lo.vectorLanes(args[0], shape)
		if !ok {
			return nil, reason, false
		}
		index, isConst := lo.constantIndexValue(args[1])
		if !isConst || index < 0 || index >= int64(shape.Lanes) {
			return nil, fmt.Sprintf("simd.%s at a lane that is not a constant below %d", member, shape.Lanes), false
		}
		value, reason, ok := lo.lower(args[2], bits)
		if !ok {
			return nil, reason, false
		}
		out := append([]*term{}, lanes...)
		out[index] = value
		return vectorOfLanes(out, typ), "", true
	case "shr":
		count, isConst := lo.constantIndexValue(args[1])
		if !isConst {
			return nil, fmt.Sprintf("simd.%s by a count that is not a constant", member), false
		}
		if count < 0 || count >= int64(bits) {
			return nil, fmt.Sprintf("simd.%s by %d (the count reaches the lane width and traps)", member, count), false
		}
		lanes, reason, ok := lo.vectorLanes(args[0], shape)
		if !ok {
			return nil, reason, false
		}
		out := make([]*term, len(lanes))
		for k := range out {
			out[k] = laneShift("shr", lanes[k], count)
		}
		return vectorOfLanes(out, typ), "", true
	case "tbl":
		if shape.TypeName != "U8x16" {
			return nil, fmt.Sprintf("simd.%s over %s lanes", member, shape.ElemName), false
		}
		return lo.simdTable(args, shape, typ)
	case "prev":
		if shape.TypeName != "U8x16" {
			return nil, fmt.Sprintf("simd.%s over %s lanes", member, shape.ElemName), false
		}
		n, isConst := lo.constantIndexValue(args[2])
		if !isConst {
			return nil, fmt.Sprintf("simd.%s by a count that is not a constant", member), false
		}
		if n < 0 || n > 16 {
			return nil, fmt.Sprintf("simd.%s by %d (above sixteen traps)", member, n), false
		}
		prev, reason, ok := lo.vectorLanes(args[0], shape)
		if !ok {
			return nil, reason, false
		}
		cur, reason, ok := lo.vectorLanes(args[1], shape)
		if !ok {
			return nil, reason, false
		}
		// The sixteen lanes ending n before the end of prev ++ cur
		// (Oak.Simd.prev): ext #(16 - n) on the machine.
		return vectorOfLanes(laneExtract(prev, cur, 16-int(n)), typ), "", true
	}
	return nil, fmt.Sprintf("the simd operation %s", member), false
}

// simdTable is the byte-table lookup as an aggregate (Oak.Simd.tbl).
func (lo *oakLowering) simdTable(args []ast.Expression, shape typechecker.SimdShape, typ *oakType) (*oakValue, string, bool) {
	table, reason, ok := lo.vectorLanes(args[0], shape)
	if !ok {
		return nil, reason, false
	}
	index, reason, ok := lo.vectorLanes(args[1], shape)
	if !ok {
		return nil, reason, false
	}
	lanes := make([]*term, len(index))
	for k := range lanes {
		lanes[k] = laneTable(table, index[k])
	}
	return vectorOfLanes(lanes, typ), "", true
}

// vectorLoad lowers `simd.load_<shape>(v, i)`: the lanes are the span's
// elements i .. i+lanes-1 (Oak.Simd.load; the backend guards the bound,
// the checker proves the guard), or the elements of an owned array local
// under `view(&arr)` / `span(&arr)` at a constant offset.
func (lo *oakLowering) vectorLoad(source, index ast.Expression, shape typechecker.SimdShape) ([]*term, string, bool) {
	bits := laneWidth(shape)
	if name := addressOfOperand(source); name != "" {
		if local, isLocal := lo.locals[name]; isLocal && local.agg != nil {
			// An owned array: elements at a constant offset.
			if local.agg.typ.kind != oakArray || local.agg.typ.elem.width != bits {
				return nil, fmt.Sprintf("a vector load over %s (not an array of %s)", name, shape.ElemName), false
			}
			offset, isConst := lo.constantIndexValue(index)
			if !isConst || offset < 0 || offset+int64(shape.Lanes) > local.agg.typ.length {
				return nil, "a vector load from an owned array at an index that is not a constant inside it", false
			}
			lanes := make([]*term, shape.Lanes)
			for k := range lanes {
				lanes[k] = narrowLane(local.agg.elems[offset+int64(k)].scalar, bits)
			}
			return lanes, "", true
		}
	}
	// A span parameter by name, or a constant table of the program under
	// `view(&T)` / `span(&T)`: declared as the span T (declareTables), its
	// elements the terms the machine's load through `adrl` gives.
	name := addressOfOperand(source)
	if name == "" {
		return nil, "a vector load from an operand that is not a span parameter", false
	}
	contract, isSpan := lo.spans[name]
	if !isSpan {
		return nil, fmt.Sprintf("a vector load from %s (not a span parameter)", name), false
	}
	if contract.elemWidth != bits {
		return nil, fmt.Sprintf("a vector load of %s lanes over %d-bit elements", shape.ElemName, contract.elemWidth), false
	}
	at, reason, ok := lo.lower(index, 32)
	if !ok {
		return nil, reason, false
	}
	root := lo.spanRoot(name)
	if lo.concrete != nil || lo.trapDomainTracked {
		// Widen before adding: a u32 index near its maximum must not wrap
		// back inside the span when the vector's lane count is added.
		end := binaryTerm("add", zeroExtend(at, 64), constTerm(uint64(shape.Lanes), 64))
		lo.addTrap(cmpTerm("hi", end, zeroExtend(lo.witnessBound(name), 64)))
		if lo.witnessTrapped {
			return nil, fmt.Sprintf("a vector load past len(%s) on this input", name), false
		}
	}
	lanes := make([]*term, shape.Lanes)
	for k := range lanes {
		position := at
		if k > 0 {
			position = binaryTerm("add", at, constTerm(uint64(k), 32))
		}
		// The entry memory, behind the path's writes (asm/effects.go): a
		// load after a vector store reads the stored lanes.
		var entry *term
		if lo.concrete != nil && position.kind == termConst {
			entry = constTerm(elementValue(name, position.value, bits), bits)
		} else {
			entry = selectTerm(name, position, bits)
		}
		lanes[k] = memoryAt(lo.writes[root], position, entry)
	}
	return lanes, "", true
}

// simdStore lowers `simd.store_<shape>(v, i, x)` in statement position:
// the lanes of x become the span's elements i .. i+lanes-1 in the path's
// write log under the path condition (asm/effects.go; Oak.Simd.store,
// store_lane), or the elements of an owned array local at a literal offset.
// The bound is the checker's (the store is dominated by a length guard).
// Reports whether the call was a vector store.
func (lo *oakLowering) simdStore(call *ast.InvocationExpression) (handled bool, reason string, ok bool) {
	member, isSimd := simdMember(call.Function)
	if !isSimd {
		return false, "", false
	}
	op, shape, isOp := simdOpShape(member)
	if !isOp || op != "store" {
		return false, "", false
	}
	if len(call.Arguments) != 3 {
		return true, fmt.Sprintf("simd.%s with %d operands", member, len(call.Arguments)), false
	}
	// In a loop body the store is the iteration's: an owned array's
	// elements take the lanes as an indexed assignment would (a body-local
	// array, or a loop-carried one's leaves), and a span's elements join
	// the iteration's write log under the path, as assignIndexed appends
	// them (the coupling proof compares the two sides' stores).
	bits := laneWidth(shape)
	lanes, reason, okLanes := lo.vectorLanes(call.Arguments[2], shape)
	if !okLanes {
		return true, reason, false
	}
	source := call.Arguments[0]
	if name := addressOfOperand(source); name != "" {
		if local, isLocal := lo.locals[name]; isLocal && local.agg != nil {
			// An owned array: its elements at a literal offset take the lanes.
			if local.agg.typ.kind != oakArray || local.agg.typ.elem.width != bits {
				return true, fmt.Sprintf("a vector store into %s (not an array of %s)", name, shape.ElemName), false
			}
			offset, isConst := lo.constantIndexValue(call.Arguments[1])
			if !isConst || offset < 0 || offset+int64(shape.Lanes) > local.agg.typ.length {
				return true, "a vector store into an owned array at an index that is not a constant inside it", false
			}
			// Under a conditional the arm runs on a snapshot of the locals
			// and the statement merges the array's leaves on the condition
			// (lowerConditionalStatement), so the store is the arm's.
			for k, lane := range lanes {
				local.agg.elems[offset+int64(k)].scalar = lane
			}
			return true, "", true
		}
	}
	ident, isIdent := source.(*ast.Identifier)
	if !isIdent {
		return true, "a vector store through an operand that is not a span parameter", false
	}
	if _, shadowed := lo.locals[ident.Value]; shadowed {
		return true, fmt.Sprintf("a vector store through %s (a local, not a span parameter)", ident.Value), false
	}
	contract, isSpan := lo.spans[ident.Value]
	if !isSpan {
		return true, fmt.Sprintf("a vector store through %s (not a span parameter)", ident.Value), false
	}
	if contract.elemWidth != bits {
		return true, fmt.Sprintf("a vector store of %s lanes over %d-bit elements", shape.ElemName, contract.elemWidth), false
	}
	index, reason, okIndex := lo.lower(call.Arguments[1], 32)
	if !okIndex {
		return true, reason, false
	}
	root := lo.spanRoot(ident.Value)
	if lo.concrete != nil || lo.trapDomainTracked {
		end := binaryTerm("add", zeroExtend(index, 64), constTerm(uint64(len(lanes)), 64))
		lo.addTrap(cmpTerm("hi", end, zeroExtend(lo.witnessBound(ident.Value), 64)))
		if lo.witnessTrapped {
			return true, fmt.Sprintf("a vector store past len(%s) on this input", ident.Value), false
		}
	}
	for k, lane := range lanes {
		at := index
		if k > 0 {
			at = binaryTerm("add", index, constTerm(uint64(k), 32))
		}
		lo.writes = appendWrite(lo.writes, root, at, truncate(lane, bits), lo.path)
	}
	return true, "", true
}

// simdScalar lowers a scalar-producing simd call at the context width:
// movemask, any, all, and the mask helpers ctz / popcount.
func (lo *oakLowering) simdScalar(member string, call *ast.InvocationExpression, width int) (*term, string, bool) {
	args := call.Arguments
	switch member {
	case "ctz_u32", "ctz_u64", "popcount_u32", "popcount_u64":
		if len(args) != 1 {
			return nil, fmt.Sprintf("simd.%s with %d operands", member, len(args)), false
		}
		bits, _ := simdScalarWidth(member)
		operand, reason, ok := lo.lower(args[0], bits)
		if !ok {
			return nil, reason, false
		}
		var value *term
		if strings.HasPrefix(member, "ctz") {
			// Trailing zeros as the leading zeros of the bit reversal;
			// ctz(0) is the width, as clz(0) is (Oak.Intrinsics.ctz_zero).
			value = binaryTerm("clz", binaryTerm("rbit", operand, constTerm(0, bits)), constTerm(0, bits))
		} else {
			value = binaryTerm("cnt", operand, constTerm(0, bits))
		}
		return adaptWidth(value, width), "", true
	}
	op, shape, ok := simdOpShape(member)
	if !ok {
		return nil, fmt.Sprintf("the simd operation %s", member), false
	}
	bits := laneWidth(shape)
	if shape.Float {
		switch op {
		case "extract":
			// The lane (a constant here; the backend traps past the lanes).
			if len(args) != 2 {
				return nil, fmt.Sprintf("simd.%s with %d operands", member, len(args)), false
			}
			lanes, reason, ok := lo.vectorLanes(args[0], shape)
			if !ok {
				return nil, reason, false
			}
			index, isConst := lo.constantIndexValue(args[1])
			if !isConst || index < 0 || index >= int64(shape.Lanes) {
				return nil, fmt.Sprintf("simd.%s at a lane that is not a constant below %d", member, shape.Lanes), false
			}
			return adaptWidth(lanes[index], width), "", true
		case "reduce_add":
			// The pairwise tree (l0 + l1) + (l2 + l3), or l0 + l1 for two
			// lanes: the grouping is the semantics (docs/spec/93-simd.md
			// §1.2a, Oak.Simd.reduceTree4), so it is these operations in
			// this order and no other.
			if len(args) != 1 {
				return nil, fmt.Sprintf("simd.%s with %d operands", member, len(args)), false
			}
			lanes, reason, ok := lo.vectorLanes(args[0], shape)
			if !ok {
				return nil, reason, false
			}
			var total *term
			if len(lanes) == 4 {
				total = floatTerm("fadd", bits, floatTerm("fadd", bits, lanes[0], lanes[1]), floatTerm("fadd", bits, lanes[2], lanes[3]))
			} else {
				total = floatTerm("fadd", bits, lanes[0], lanes[1])
			}
			return adaptWidth(total, width), "", true
		}
	}
	if len(args) != 1 {
		return nil, fmt.Sprintf("simd.%s with %d operands", member, len(args)), false
	}
	switch op {
	case "movemask", "any", "all":
		lanes, reason, ok := lo.vectorLanes(args[0], shape)
		if !ok {
			return nil, reason, false
		}
		switch op {
		case "movemask":
			return adaptWidth(laneMovemask(lanes), width), "", true
		case "any":
			return zeroExtend(truncate(laneAny(lanes), 1), width), "", true
		default:
			return zeroExtend(truncate(laneAll(lanes), 1), width), "", true
		}
	case "store":
		return nil, fmt.Sprintf("simd.%s in value position (a statement)", member), false
	}
	if _, isVectorOp := simdVectorOps[op]; isVectorOp {
		return nil, fmt.Sprintf("the vector simd.%s in scalar position", member), false
	}
	return nil, fmt.Sprintf("the simd operation %s", member), false
}
