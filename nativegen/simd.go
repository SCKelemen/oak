package nativegen

import (
	"fmt"
	"strconv"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
)

// Portable SIMD on the AArch64 lane (docs/spec/93-simd.md section 1, section
// 1.4 "native lowering"): the fixed vectors simd.U8x16, U16x8, U32x4, and
// U64x2 are 128-bit scalars of the generator held in the vector register
// file — scratch in v16–v23 like floats, locals in v8–v15 when the function
// makes no call (AAPCS64 preserves only their low halves across a call, so
// a function that calls keeps vector locals in 16-byte frame slots),
// parameters and results in v0–v7 — and every `simd.op_shape(...)` call
// lowers to the NEON instruction the C backend's helper wraps: the
// portable lane semantics are the specification, the selection is not.
// Whatever this file does not lower (float vectors, vectors inside records
// or arrays, a shift by a non-literal count) is reported Unsupported and
// the function stays on the C backend.

// vecShapes are the integer vector types by their qualified spelling.
var vecShapes = map[string]scalar{
	"U8x16": {name: "simd.U8x16", bits: 128, isVec: true, lanes: 16, laneBits: 8},
	"U16x8": {name: "simd.U16x8", bits: 128, isVec: true, lanes: 8, laneBits: 16},
	"U32x4": {name: "simd.U32x4", bits: 128, isVec: true, lanes: 4, laneBits: 32},
	"U64x2": {name: "simd.U64x2", bits: 128, isVec: true, lanes: 2, laneBits: 64},
}

// The vector types join the scalar table under their qualified spelling,
// which is how a `simd.U8x16` annotation reads (one identifier).
func init() {
	for _, s := range vecShapes {
		scalars[s.name] = s
	}
}

// vecShapeBySuffix: the op suffix ("u8x16") to its type.
func vecShapeBySuffix(suffix string) (scalar, bool) {
	for name, s := range vecShapes {
		if "u"+name[1:] == suffix {
			return s, true
		}
	}
	return scalar{}, false
}

// arr is the NEON arrangement of a vector type's lanes.
func (s scalar) arr() string {
	switch s.laneBits {
	case 8:
		return "16b"
	case 16:
		return "8h"
	case 32:
		return "4s"
	}
	return "2d"
}

// vecTypeOf reads `simd.Name` in type position.
func vecTypeOf(expr ast.Expression) (scalar, bool) {
	access, isAccess := expr.(*ast.IndexExpression)
	if !isAccess {
		return scalar{}, false
	}
	base, isIdent := access.Left.(*ast.Identifier)
	member, isMember := access.Index.(*ast.Identifier)
	if !isIdent || !isMember || base.Value != "simd" {
		return scalar{}, false
	}
	s, ok := vecShapes[member.Value]
	return s, ok
}

// simdCallee reads `simd.member` in callee position.
func simdCallee(fn ast.Expression) (member string, ok bool) {
	access, isAccess := fn.(*ast.IndexExpression)
	if !isAccess {
		return "", false
	}
	base, isIdent := access.Left.(*ast.Identifier)
	memberIdent, isMember := access.Index.(*ast.Identifier)
	if !isIdent || !isMember || base.Value != "simd" {
		return "", false
	}
	return memberIdent.Value, true
}

// simdOpParts splits "tbl_u8x16" into the op and its shape; the scalar
// helpers ctz/popcount carry an integer width instead.
func simdOpParts(member string) (op string, shape scalar, ok bool) {
	for i := len(member) - 1; i > 0; i-- {
		if member[i] == '_' {
			if s, known := vecShapeBySuffix(member[i+1:]); known {
				return member[:i], s, true
			}
			return "", scalar{}, false
		}
	}
	return "", scalar{}, false
}

// vreg spells vector register n with an arrangement; qreg its q view; breg
// its b view; laneB0 its first byte lane.
func vreg(n int, arr string) asm.Register {
	return asm.Register{Text: "v" + strconv.Itoa(n) + "." + arr, Class: asm.ClassV, Num: n, Vec: arr, Lane: -1}
}
func qreg(n int) asm.Register {
	return asm.Register{Text: "q" + strconv.Itoa(n), Class: asm.ClassV, Num: n, Vec: "q", Lane: -1}
}
func breg(n int) asm.Register {
	return asm.Register{Text: "b" + strconv.Itoa(n), Class: asm.ClassV, Num: n, Vec: "b", Lane: -1}
}
func laneB0(n int) asm.Register {
	return asm.Register{Text: "v" + strconv.Itoa(n) + ".b[0]", Class: asm.ClassV, Num: n, Vec: "b", Lane: 0}
}
func wholeV(n int) asm.Register {
	return asm.Register{Text: "v" + strconv.Itoa(n), Class: asm.ClassV, Num: n, Vec: "", Lane: -1}
}

// vmove copies a vector register (orr, the move of the vector file).
func (g *generator) vmove(dst, src int) {
	if dst == src {
		return
	}
	g.emit("orr", vreg(dst, "16b"), vreg(src, "16b"), vreg(src, "16b"))
}

// simdResultType is the type a simd call produces.
func (g *generator) simdResultType(member string, args []ast.Expression) (scalar, error) {
	switch member {
	case "ctz_u32", "popcount_u32":
		return scalars["u32"], nil
	case "ctz_u64", "popcount_u64":
		return scalars["u64"], nil
	}
	op, shape, ok := simdOpParts(member)
	if !ok {
		return scalar{}, unsupported("the simd operation %s", member)
	}
	switch op {
	case "any", "all":
		return scalars["Bool"], nil
	case "movemask":
		return scalars["u32"], nil
	case "store":
		return scalar{}, unsupported("simd.%s in value position", member)
	case "splat", "load", "add", "sub", "and", "or", "xor", "min", "max", "eq", "subs", "shr", "tbl", "prev":
		return shape, nil
	}
	return scalar{}, unsupported("the simd operation %s", member)
}

// simdOp lowers one simd call; the result register is a vector scratch for
// a vector result, a general scratch for Bool/u32/u64, -1 for store.
func (g *generator) simdOp(member string, args []ast.Expression) (int, error) {
	switch member {
	case "ctz_u32", "ctz_u64":
		return g.simdCtz(member, args)
	case "popcount_u32", "popcount_u64":
		return g.simdPopcount(member, args)
	}
	op, shape, ok := simdOpParts(member)
	if !ok {
		return 0, unsupported("the simd operation %s", member)
	}
	arity := map[string]int{"splat": 1, "load": 2, "store": 3, "add": 2, "sub": 2, "and": 2, "or": 2, "xor": 2, "min": 2, "max": 2, "eq": 2, "subs": 2, "shr": 2, "any": 1, "all": 1, "tbl": 2, "prev": 3, "movemask": 1}
	want, known := arity[op]
	if !known {
		return 0, unsupported("the simd operation %s", member)
	}
	if len(args) != want {
		return 0, unsupported("simd.%s with %d operands", member, len(args))
	}
	switch op {
	case "splat":
		elem := scalars[shape.laneName()]
		r, err := g.expr(args[0], &elem)
		if err != nil {
			return 0, err
		}
		v, err := g.alloc(shape)
		if err != nil {
			return 0, err
		}
		g.emit("dup", vreg(v-vecBase, shape.arr()), reg(r, elem))
		g.release(r)
		return v, nil
	case "load":
		if arr, k, ok := g.vecArrayOperand(args[0], args[1], shape, false); ok {
			v, err := g.alloc(shape)
			if err != nil {
				return 0, err
			}
			g.emit("ldr", qreg(v-vecBase), g.memOf(arr.loc().plus(k)))
			return v, nil
		}
		sp, err := g.spanOperand(args[0])
		if err != nil {
			return 0, err
		}
		if sp.elem.name != shape.laneName() {
			return 0, unsupported("simd.%s over a view of %s", member, sp.elem.name)
		}
		if shape.laneBits != 8 {
			// A q load indexes by bytes or by sixteens, never by a lane
			// size in between; wider lanes wait for the scaled-index idiom.
			return 0, unsupported("simd.%s (a vector load over %s lanes needs a scaled index)", member, shape.laneName())
		}
		idx, err := g.vecGuardedIndex(sp, args[1], shape)
		if err != nil {
			return 0, err
		}
		v, err := g.alloc(shape)
		if err != nil {
			return 0, err
		}
		g.emit("ldr", qreg(v-vecBase), g.vecAddress(sp, idx, shape))
		g.release(idx)
		return v, nil
	case "store":
		if arr, k, ok := g.vecArrayOperand(args[0], args[1], shape, true); ok {
			v, err := g.expr(args[2], &shape)
			if err != nil {
				return 0, err
			}
			g.emit("str", qreg(v-vecBase), g.memOf(arr.loc().plus(k)))
			g.release(v)
			return -1, nil
		}
		sp, err := g.spanOperand(args[0])
		if err != nil {
			return 0, err
		}
		if !sp.writable {
			return 0, unsupported("simd.%s through a read-only view", member)
		}
		if sp.elem.name != shape.laneName() {
			return 0, unsupported("simd.%s over a span of %s", member, sp.elem.name)
		}
		if shape.laneBits != 8 {
			return 0, unsupported("simd.%s (a vector store over %s lanes needs a scaled index)", member, shape.laneName())
		}
		v, err := g.expr(args[2], &shape)
		if err != nil {
			return 0, err
		}
		idx, err := g.vecGuardedIndex(sp, args[1], shape)
		if err != nil {
			return 0, err
		}
		g.emit("str", qreg(v-vecBase), g.vecAddress(sp, idx, shape))
		g.release(idx)
		g.release(v)
		return -1, nil
	case "add", "sub", "and", "or", "xor", "min", "max", "eq", "subs":
		mnemonic := map[string]string{"add": "add", "sub": "sub", "and": "and", "or": "orr", "xor": "eor", "min": "umin", "max": "umax", "eq": "cmeq", "subs": "uqsub"}[op]
		if (op == "min" || op == "max") && shape.laneBits == 64 {
			return 0, unsupported("simd.%s (NEON has no 64-bit lane form)", member)
		}
		a, err := g.expr(args[0], &shape)
		if err != nil {
			return 0, err
		}
		b, err := g.expr(args[1], &shape)
		if err != nil {
			return 0, err
		}
		arr := shape.arr()
		if op == "and" || op == "or" || op == "xor" {
			arr = "16b"
		}
		g.emit(mnemonic, vreg(a-vecBase, arr), vreg(a-vecBase, arr), vreg(b-vecBase, arr))
		g.release(b)
		return a, nil
	case "shr":
		count, isConst := constantValue(args[1])
		if !isConst {
			return 0, unsupported("simd.%s by a count that is not a literal", member)
		}
		if count < 0 || count >= int64(shape.laneBits) {
			return 0, unsupported("simd.%s by %d (the count reaches the lane width and traps)", member, count)
		}
		a, err := g.expr(args[0], &shape)
		if err != nil {
			return 0, err
		}
		if count > 0 {
			g.emit("ushr", vreg(a-vecBase, shape.arr()), vreg(a-vecBase, shape.arr()), imm(count))
		}
		return a, nil
	case "any", "all":
		a, err := g.expr(args[0], &shape)
		if err != nil {
			return 0, err
		}
		if op == "all" {
			// every lane nonzero <=> no lane equal to zero
			g.emit("cmeq", vreg(a-vecBase, shape.arr()), vreg(a-vecBase, shape.arr()), imm(0))
		}
		// umaxv over the bytes: nonzero iff some byte, so some lane, is nonzero
		g.emit("umaxv", breg(a-vecBase), vreg(a-vecBase, "16b"))
		r, err := g.alloc(scalars["Bool"])
		if err != nil {
			return 0, err
		}
		g.emit("umov", wr(r), laneB0(a-vecBase))
		g.emit("cmp", wr(r), imm(0))
		if op == "all" {
			g.emit("cset", wr(r), asm.Condition{Code: "eq"})
		} else {
			g.emit("cset", wr(r), asm.Condition{Code: "ne"})
		}
		g.release(a)
		return r, nil
	case "tbl":
		t, err := g.expr(args[0], &shape)
		if err != nil {
			return 0, err
		}
		i, err := g.expr(args[1], &shape)
		if err != nil {
			return 0, err
		}
		g.emit("tbl", vreg(t-vecBase, "16b"), asm.RegisterList{Regs: []asm.Register{vreg(t-vecBase, "16b")}}, vreg(i-vecBase, "16b"))
		g.release(i)
		return t, nil
	case "prev":
		n, isConst := constantValue(args[2])
		if !isConst {
			return 0, unsupported("simd.%s by a count that is not a literal", member)
		}
		if n < 0 || n > 16 {
			return 0, unsupported("simd.%s by %d (above sixteen traps)", member, n)
		}
		prev, err := g.expr(args[0], &shape)
		if err != nil {
			return 0, err
		}
		cur, err := g.expr(args[1], &shape)
		if err != nil {
			return 0, err
		}
		switch n {
		case 0:
			g.release(prev)
			return cur, nil
		case 16:
			g.release(cur)
			return prev, nil
		}
		// the sixteen bytes ending n before the end of prev ++ cur
		g.emit("ext", vreg(prev-vecBase, "16b"), vreg(prev-vecBase, "16b"), vreg(cur-vecBase, "16b"), imm(16-n))
		g.release(cur)
		return prev, nil
	case "movemask":
		return g.simdMovemask(shape, args[0])
	}
	return 0, unsupported("the simd operation %s", member)
}

// vecArrayOperand recognizes `view(&arr)` / `span(&arr)` over an owned
// array local with a literal element index whose sixteen bytes lie inside
// the array: the access is a frame slot at a constant offset, checked
// here, so it needs no run-time guard.
func (g *generator) vecArrayOperand(operand, index ast.Expression, shape scalar, writable bool) (*arrayLocal, int64, bool) {
	arr, err := g.arrayArgument(operand, span{elem: scalars[shape.laneName()], writable: writable})
	if err != nil || arr == nil {
		return nil, 0, false
	}
	k, isConst := constantValue(index)
	if !isConst || k < 0 || k+int64(shape.lanes) > arr.length {
		return nil, 0, false
	}
	return arr, k * int64(shape.laneBits/8), true
}

// laneName is the lane's scalar type name.
func (s scalar) laneName() string { return "u" + strconv.Itoa(s.laneBits) }

// vecGuardedIndex evaluates the element index of a vector access and emits
// the check that the L lanes lie within the length: `len >= L` and
// `index <= len - L`, each a compare and a branch to the trap.
func (g *generator) vecGuardedIndex(sp span, index ast.Expression, shape scalar) (int, error) {
	r, err := g.indexValue(index)
	if err != nil {
		return 0, err
	}
	limit, err := g.alloc(scalars["u32"])
	if err != nil {
		return 0, err
	}
	g.usedTrap = true
	g.emit("cmp", wr(sp.lenReg), imm(int64(shape.lanes)))
	g.branch("lo", g.trap)
	g.emit("sub", wr(limit), wr(sp.lenReg), imm(int64(shape.lanes)))
	g.emit("cmp", wr(r), wr(limit))
	g.branch("hi", g.trap)
	g.release(limit)
	return r, nil
}

// vecAddress is [base, wIdx, uxtw #s]: the element index scaled by the
// lane size, sixteen bytes from there.
func (g *generator) vecAddress(sp span, idx int, shape scalar) asm.Memory {
	w := wr(idx)
	return asm.Memory{Base: xr(sp.baseReg), Index: &w, Shift: log2Bytes(shape.laneBits / 8), Extend: "uxtw"}
}

// simdMovemask: one bit per lane, bit i the top bit of lane i. Bytes: the
// arithmetic shift by seven makes each lane 0x00 or 0xFF, an AND with the
// lane bits 1, 2, 4, ..., 128 per half keeps one bit per lane, and a sum
// across each half packs them; the halves are combined as low and high
// byte. Wider lanes are left to the C backend.
func (g *generator) simdMovemask(shape scalar, arg ast.Expression) (int, error) {
	if shape.laneBits != 8 {
		return 0, unsupported("simd.movemask over %s lanes", shape.laneName())
	}
	a, err := g.expr(arg, &shape)
	if err != nil {
		return 0, err
	}
	bits, err := g.alloc(scalars["u64"])
	if err != nil {
		return 0, err
	}
	g.constant(bits, 0x8040201008040201, scalars["u64"])
	table, err := g.alloc(shape)
	if err != nil {
		return 0, err
	}
	g.emit("dup", vreg(table-vecBase, "2d"), xr(bits))
	g.release(bits)
	g.emit("sshr", vreg(a-vecBase, "16b"), vreg(a-vecBase, "16b"), imm(7))
	g.emit("and", vreg(a-vecBase, "16b"), vreg(a-vecBase, "16b"), vreg(table-vecBase, "16b"))
	// high half into table's low half, then sum each half's eight bytes
	g.emit("ext", vreg(table-vecBase, "16b"), vreg(a-vecBase, "16b"), vreg(a-vecBase, "16b"), imm(8))
	g.emit("addv", breg(a-vecBase), vreg(a-vecBase, "8b"))
	g.emit("addv", breg(table-vecBase), vreg(table-vecBase, "8b"))
	low, err := g.alloc(scalars["u32"])
	if err != nil {
		return 0, err
	}
	high, err := g.alloc(scalars["u32"])
	if err != nil {
		return 0, err
	}
	g.emit("umov", wr(low), laneB0(a-vecBase))
	g.emit("umov", wr(high), laneB0(table-vecBase))
	g.emit("lsl", wr(high), wr(high), imm(8))
	g.emit("orr", wr(low), wr(low), wr(high))
	g.release(high)
	g.release(table)
	g.release(a)
	return low, nil
}

// simdCtz: trailing zeros as the bit-reversed leading zeros; ctz(0) is the
// width, which clz of zero gives.
func (g *generator) simdCtz(member string, args []ast.Expression) (int, error) {
	if len(args) != 1 {
		return 0, unsupported("simd.%s with %d operands", member, len(args))
	}
	typ := scalars["u32"]
	if member == "ctz_u64" {
		typ = scalars["u64"]
	}
	r, err := g.expr(args[0], &typ)
	if err != nil {
		return 0, err
	}
	g.emit("rbit", reg(r, typ), reg(r, typ))
	g.emit("clz", reg(r, typ), reg(r, typ))
	return r, nil
}

// simdPopcount: the value into a vector register's low lanes, bytes
// counted lane-wise, summed across.
func (g *generator) simdPopcount(member string, args []ast.Expression) (int, error) {
	if len(args) != 1 {
		return 0, unsupported("simd.%s with %d operands", member, len(args))
	}
	typ := scalars["u32"]
	if member == "popcount_u64" {
		typ = scalars["u64"]
	}
	r, err := g.expr(args[0], &typ)
	if err != nil {
		return 0, err
	}
	v, err := g.alloc(vecShapes["U8x16"])
	if err != nil {
		return 0, err
	}
	n := v - vecBase
	if typ.wide() {
		g.emit("fmov", dr(n), xr(r))
	} else {
		g.emit("fmov", asm.Register{Text: "s" + strconv.Itoa(n), Class: asm.ClassV, Num: n, Vec: "s", Lane: -1}, wr(r))
	}
	g.emit("cnt", vreg(n, "8b"), vreg(n, "8b"))
	g.emit("addv", breg(n), vreg(n, "8b"))
	g.emit("umov", wr(r), laneB0(n))
	g.release(v)
	return r, nil
}

// VectorContractSuffix marks the native symbol of a function whose
// signature carries a fixed vector: such a function follows the vector
// register contract (v0–v7, the checker's contractClass), which the C
// backend's lane-array struct does not, so the C emitter defines the Oak
// name as a converting shim over the suffixed native entry
// (codegen/codegen.go emitVectorShim). Identifiers never end in it.
const VectorContractSuffix = "_neon_abi"

// VectorContract reports a function whose parameters or result include a
// fixed vector type.
func VectorContract(fn *ast.FunctionStatement) bool {
	if fn == nil {
		return false
	}
	for _, p := range fn.Parameters {
		if s, ok := scalarOf(p.Type); ok && s.isVec {
			return true
		}
	}
	if fn.ReturnType != nil {
		if s, ok := scalarOf(fn.ReturnType); ok && s.isVec {
			return true
		}
	}
	return false
}

// NativeSymbol is the Oak-level name the native lowering of fn is encoded
// under: the function's own name, suffixed under the vector contract.
func NativeSymbol(fn *ast.FunctionStatement) string {
	if VectorContract(fn) {
		return fn.Name.Value + VectorContractSuffix
	}
	return fn.Name.Value
}

// VectorCallees lists the functions fn calls whose signatures carry a
// vector: a native fn reaches them through their suffixed native entries,
// so every one must be lowered natively too (compiler/native_bodies.go).
func VectorCallees(fn *ast.FunctionStatement, functions map[string]*ast.FunctionStatement) []string {
	seen := map[string]bool{}
	var out []string
	walk(fn.Body, func(n ast.Node) {
		call, ok := n.(*ast.InvocationExpression)
		if !ok {
			return
		}
		ident, isIdent := call.Function.(*ast.Identifier)
		if !isIdent || seen[ident.Value] {
			return
		}
		if callee, declared := functions[ident.Value]; declared && VectorContract(callee) {
			seen[ident.Value] = true
			out = append(out, ident.Value)
		}
	})
	return out
}

var _ = fmt.Sprintf
