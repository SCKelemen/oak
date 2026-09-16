package nativegen

import (
	"fmt"
	"strconv"
	"strings"

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
// The floating-point vectors simd.F32x4 and F64x2 (section 1.2a) lower the
// same way: `fadd`/`fsub`/`fmul`/`fdiv`, `fmla` for the one-rounding
// `fma`, `fmin`/`fmax` (NEON's are IEEE 754-2019 minimum/maximum: a NaN
// operand yields NaN, -0.0 orders below +0.0), `fsqrt`/`fneg`/`fabs`,
// `mov` to and from a literal lane for `extract`/`insert`, and the
// pairwise `faddp` tree for `reduce_add` — `(l0 + l1) + (l2 + l3)`, the
// grouping the specification fixes (Oak.Simd.pairwise_reduce). Whatever
// this file does not lower (vectors inside records or arrays, a shift by
// a non-literal count, a non-literal lane index) is reported Unsupported
// and the function stays on the C backend.

// vecShapes are the fixed vector types by their qualified spelling.
var vecShapes = map[string]scalar{
	"U8x16": {name: "simd.U8x16", bits: 128, isVec: true, lanes: 16, laneBits: 8},
	"U16x8": {name: "simd.U16x8", bits: 128, isVec: true, lanes: 8, laneBits: 16},
	"U32x4": {name: "simd.U32x4", bits: 128, isVec: true, lanes: 4, laneBits: 32},
	"U64x2": {name: "simd.U64x2", bits: 128, isVec: true, lanes: 2, laneBits: 64},
	"F32x4": {name: "simd.F32x4", bits: 128, isVec: true, lanes: 4, laneBits: 32, laneFloat: true},
	"F64x2": {name: "simd.F64x2", bits: 128, isVec: true, lanes: 2, laneBits: 64, laneFloat: true},
}

// The vector types join the scalar table under their qualified spelling,
// which is how a `simd.U8x16` annotation reads (one identifier).
func init() {
	for _, s := range vecShapes {
		scalars[s.name] = s
	}
}

// vecShapeBySuffix: the op suffix ("u8x16", "f32x4") to its type.
func vecShapeBySuffix(suffix string) (scalar, bool) {
	for name, s := range vecShapes {
		if strings.ToLower(name) == suffix {
			return s, true
		}
	}
	return scalar{}, false
}

// laneReg spells lane k of vector register n in the view of its lanes
// ("v3.s[1]"): the source of a lane extract or splat, the destination of
// a lane insert.
func laneReg(n int, view string, k int64) asm.Register {
	return asm.Register{Text: "v" + strconv.Itoa(n) + "." + view + "[" + strconv.FormatInt(k, 10) + "]", Class: asm.ClassV, Num: n, Vec: view, Lane: int(k)}
}

// laneView is the scalar view letter of a vector type's lanes.
func (s scalar) laneView() string {
	switch s.laneBits {
	case 8:
		return "b"
	case 16:
		return "h"
	case 32:
		return "s"
	}
	return "d"
}

// floatVecOps and intVecOps are the operations each family of shapes
// admits (docs/spec/93-simd.md sections 1.2 and 1.2a); the typechecker
// refuses the rest, so a mismatch here is a defect, reported Unsupported.
var floatVecOps = map[string]bool{"splat": true, "load": true, "store": true, "add": true, "sub": true, "mul": true, "div": true, "fma": true, "min": true, "max": true, "sqrt": true, "neg": true, "abs": true, "extract": true, "insert": true, "reduce_add": true}
var intVecOps = map[string]bool{"splat": true, "load": true, "store": true, "add": true, "sub": true, "and": true, "or": true, "xor": true, "min": true, "max": true, "eq": true, "subs": true, "shr": true, "any": true, "all": true, "tbl": true, "prev": true, "movemask": true}

// admitsOp reports the operation belongs to the shape's family.
func (s scalar) admitsOp(op string) bool {
	if s.laneFloat {
		return floatVecOps[op]
	}
	return intVecOps[op]
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

// vecOperand is a vector operand where it lies: a vector variable in its
// own register is read in place (fixed: the caller must not write it or
// release it), anything else is evaluated into a scratch. The counterpart
// of operand for the vector file: before it, every vector variable read
// was an orr copy into a scratch and every result an orr copy back, so
// `or(or(a, b), or(c, d))` cost eight instructions where the machine
// needs three (the UTF-8 validator's loop, benchmarks/native/README.md).
func (g *generator) vecOperand(arg ast.Expression, shape scalar) (int, bool, error) {
	if ident, isIdent := arg.(*ast.Identifier); isIdent {
		if v, inReg := g.regs[ident.Value]; inReg && v >= vecBase {
			if t, ok := g.types[ident.Value]; ok && t == shape {
				return v, true, nil
			}
		}
	}
	r, err := g.expr(arg, &shape)
	return r, false, err
}

// vecDest is the register an operation writes: the operand's own scratch
// when it was one, a fresh scratch when the operand is a variable's home.
func (g *generator) vecDest(a int, fixed bool, shape scalar) (int, error) {
	if !fixed {
		return a, nil
	}
	return g.alloc(shape)
}

// vecRelease releases an operand vecOperand evaluated into a scratch.
func (g *generator) vecRelease(r int, fixed bool) {
	if !fixed {
		g.release(r)
	}
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
	if !shape.admitsOp(op) {
		return scalar{}, unsupported("the simd operation %s", member)
	}
	switch op {
	case "any", "all":
		return scalars["Bool"], nil
	case "movemask":
		return scalars["u32"], nil
	case "extract", "reduce_add":
		return scalars[shape.laneName()], nil
	case "store":
		return scalar{}, unsupported("simd.%s in value position", member)
	case "splat", "load", "add", "sub", "and", "or", "xor", "min", "max", "eq", "subs", "shr", "tbl", "prev", "mul", "div", "fma", "sqrt", "neg", "abs", "insert":
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
	arity := map[string]int{"splat": 1, "load": 2, "store": 3, "add": 2, "sub": 2, "and": 2, "or": 2, "xor": 2, "min": 2, "max": 2, "eq": 2, "subs": 2, "shr": 2, "any": 1, "all": 1, "tbl": 2, "prev": 3, "movemask": 1,
		"mul": 2, "div": 2, "fma": 3, "sqrt": 1, "neg": 1, "abs": 1, "extract": 2, "insert": 3, "reduce_add": 1}
	want, known := arity[op]
	if !known || !shape.admitsOp(op) {
		return 0, unsupported("the simd operation %s", member)
	}
	if len(args) != want {
		return 0, unsupported("simd.%s with %d operands", member, len(args))
	}
	switch op {
	case "splat":
		elem := scalars[shape.laneName()]
		if k, isConst := g.constantOperand(args[0], elem); isConst && !shape.laneFloat && (k == 0 || (shape.laneBits == 8 && k <= 255)) {
			// A literal lane value the vector immediate move spells: zero
			// in any arrangement, a byte in every byte lane — instead of a
			// scalar movz, a mask, and a dup through a general register.
			v, err := g.alloc(shape)
			if err != nil {
				return 0, err
			}
			g.emit("movi", vreg(v-vecBase, "16b"), imm(int64(k)))
			return v, nil
		}
		r, err := g.expr(args[0], &elem)
		if err != nil {
			return 0, err
		}
		v, err := g.alloc(shape)
		if err != nil {
			return 0, err
		}
		if shape.laneFloat {
			// A float scalar lives in lane 0 of its register: the element
			// form of dup broadcasts it.
			g.emit("dup", vreg(v-vecBase, shape.arr()), laneReg(r-vecBase, shape.laneView(), 0))
		} else {
			g.emit("dup", vreg(v-vecBase, shape.arr()), reg(r, elem))
		}
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
		idx, err := g.vecGuardedIndex(sp, args[0], args[1], shape)
		if err != nil {
			return 0, err
		}
		v, err := g.alloc(shape)
		if err != nil {
			return 0, err
		}
		addr, addrReg, err := g.vecAddress(sp, idx, shape)
		if err != nil {
			return 0, err
		}
		g.emit("ldr", qreg(v-vecBase), addr)
		g.release(idx)
		g.releaseAddr(addrReg)
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
		v, vfixed, err := g.vecOperand(args[2], shape)
		if err != nil {
			return 0, err
		}
		idx, err := g.vecGuardedIndex(sp, args[0], args[1], shape)
		if err != nil {
			return 0, err
		}
		addr, addrReg, err := g.vecAddress(sp, idx, shape)
		if err != nil {
			return 0, err
		}
		g.emit("str", qreg(v-vecBase), addr)
		g.release(idx)
		g.releaseAddr(addrReg)
		g.vecRelease(v, vfixed)
		return -1, nil
	case "add", "sub", "and", "or", "xor", "min", "max", "eq", "subs", "mul", "div":
		mnemonic := map[string]string{"add": "add", "sub": "sub", "and": "and", "or": "orr", "xor": "eor", "min": "umin", "max": "umax", "eq": "cmeq", "subs": "uqsub"}[op]
		if shape.laneFloat {
			// Lane-wise IEEE arithmetic, one rounding each; fmin/fmax are
			// the 754-2019 minimum/maximum the catalog specifies.
			mnemonic = map[string]string{"add": "fadd", "sub": "fsub", "mul": "fmul", "div": "fdiv", "min": "fmin", "max": "fmax"}[op]
		}
		if (op == "min" || op == "max") && shape.laneBits == 64 && !shape.laneFloat {
			return 0, unsupported("simd.%s (NEON has no 64-bit lane form)", member)
		}
		a, afixed, err := g.vecOperand(args[0], shape)
		if err != nil {
			return 0, err
		}
		b, bfixed, err := g.vecOperand(args[1], shape)
		if err != nil {
			return 0, err
		}
		out, err := g.vecDest(a, afixed, shape)
		if err != nil {
			return 0, err
		}
		arr := shape.arr()
		if op == "and" || op == "or" || op == "xor" {
			arr = "16b"
		}
		g.emit(mnemonic, vreg(out-vecBase, arr), vreg(a-vecBase, arr), vreg(b-vecBase, arr))
		g.vecRelease(b, bfixed)
		return out, nil
	case "fma":
		// fma(a, b, c) = a*b + c in one rounding: fmla accumulates into
		// its destination, so c's register receives the result.
		a, afixed, err := g.vecOperand(args[0], shape)
		if err != nil {
			return 0, err
		}
		b, bfixed, err := g.vecOperand(args[1], shape)
		if err != nil {
			return 0, err
		}
		c, cfixed, err := g.vecOperand(args[2], shape)
		if err != nil {
			return 0, err
		}
		out, err := g.vecDest(c, cfixed, shape)
		if err != nil {
			return 0, err
		}
		if cfixed {
			g.vmove(out-vecBase, c-vecBase) // fmla accumulates into its destination
		}
		g.emit("fmla", vreg(out-vecBase, shape.arr()), vreg(a-vecBase, shape.arr()), vreg(b-vecBase, shape.arr()))
		g.vecRelease(a, afixed)
		g.vecRelease(b, bfixed)
		return out, nil
	case "sqrt", "neg", "abs":
		a, afixed, err := g.vecOperand(args[0], shape)
		if err != nil {
			return 0, err
		}
		out, err := g.vecDest(a, afixed, shape)
		if err != nil {
			return 0, err
		}
		mnemonic := map[string]string{"sqrt": "fsqrt", "neg": "fneg", "abs": "fabs"}[op]
		g.emit(mnemonic, vreg(out-vecBase, shape.arr()), vreg(a-vecBase, shape.arr()))
		return out, nil
	case "extract":
		// A literal lane index is checked here against the lane count; a
		// non-literal one needs the C backend's run-time check.
		k, isConst := constantValue(args[1])
		if !isConst {
			return 0, unsupported("simd.%s with a lane index that is not a literal", member)
		}
		if k < 0 || k >= int64(shape.lanes) {
			return 0, unsupported("simd.%s at lane %d (the index reaches the lane count and traps)", member, k)
		}
		a, afixed, err := g.vecOperand(args[0], shape)
		if err != nil {
			return 0, err
		}
		elem := scalars[shape.laneName()]
		r, err := g.alloc(elem)
		if err != nil {
			return 0, err
		}
		g.emit("mov", reg(r, elem), laneReg(a-vecBase, shape.laneView(), k))
		g.vecRelease(a, afixed)
		return r, nil
	case "insert":
		k, isConst := constantValue(args[1])
		if !isConst {
			return 0, unsupported("simd.%s with a lane index that is not a literal", member)
		}
		if k < 0 || k >= int64(shape.lanes) {
			return 0, unsupported("simd.%s at lane %d (the index reaches the lane count and traps)", member, k)
		}
		a, afixed, err := g.vecOperand(args[0], shape)
		if err != nil {
			return 0, err
		}
		out, err := g.vecDest(a, afixed, shape)
		if err != nil {
			return 0, err
		}
		if afixed {
			g.vmove(out-vecBase, a-vecBase) // the lane insert writes into the whole
		}
		elem := scalars[shape.laneName()]
		x, err := g.expr(args[2], &elem)
		if err != nil {
			return 0, err
		}
		g.emit("mov", laneReg(out-vecBase, shape.laneView(), k), laneReg(x-vecBase, shape.laneView(), 0))
		g.release(x)
		return out, nil
	case "reduce_add":
		// The pairwise tree of docs/spec/93-simd.md section 1.2a: faddp
		// over the four lanes leaves (l0+l1, l2+l3, l0+l1, l2+l3), and
		// the scalar faddp over the low pair adds them — exactly
		// (l0 + l1) + (l2 + l3) (Oak.Simd.pairwise_reduce); two lanes are
		// one scalar faddp.
		a, afixed, err := g.vecOperand(args[0], shape)
		if err != nil {
			return 0, err
		}
		elem := scalars[shape.laneName()]
		r, err := g.alloc(elem)
		if err != nil {
			return 0, err
		}
		n := a - vecBase
		if shape.lanes == 4 {
			// The pairwise step writes a vector: a fixed operand's home is
			// read only, the pairs land in a scratch.
			t, err := g.vecDest(a, afixed, shape)
			if err != nil {
				return 0, err
			}
			g.emit("faddp", vreg(t-vecBase, "4s"), vreg(n, "4s"), vreg(n, "4s"))
			g.emit("faddp", reg(r, elem), vreg(t-vecBase, "2s"))
			g.release(t)
		} else {
			g.emit("faddp", reg(r, elem), vreg(n, "2d"))
			g.vecRelease(a, afixed)
		}
		return r, nil
	case "shr":
		count, isConst := constantValue(args[1])
		if !isConst {
			return 0, unsupported("simd.%s by a count that is not a literal", member)
		}
		if count < 0 || count >= int64(shape.laneBits) {
			return 0, unsupported("simd.%s by %d (the count reaches the lane width and traps)", member, count)
		}
		a, afixed, err := g.vecOperand(args[0], shape)
		if err != nil {
			return 0, err
		}
		out, err := g.vecDest(a, afixed, shape)
		if err != nil {
			return 0, err
		}
		if count > 0 {
			g.emit("ushr", vreg(out-vecBase, shape.arr()), vreg(a-vecBase, shape.arr()), imm(count))
		} else if afixed {
			g.vmove(out-vecBase, a-vecBase)
		}
		return out, nil
	case "any", "all":
		a, afixed, err := g.vecOperand(args[0], shape)
		if err != nil {
			return 0, err
		}
		// The reduction writes a vector register: a fixed operand's home
		// is read only, the compare and the maximum land in a scratch.
		t, err := g.vecDest(a, afixed, shape)
		if err != nil {
			return 0, err
		}
		src := a
		if op == "all" {
			// every lane nonzero <=> no lane equal to zero
			g.emit("cmeq", vreg(t-vecBase, shape.arr()), vreg(a-vecBase, shape.arr()), imm(0))
			src = t
		}
		// umaxv over the bytes: nonzero iff some byte, so some lane, is nonzero
		g.emit("umaxv", breg(t-vecBase), vreg(src-vecBase, "16b"))
		r, err := g.alloc(scalars["Bool"])
		if err != nil {
			return 0, err
		}
		g.emit("umov", wr(r), laneB0(t-vecBase))
		g.emit("cmp", wr(r), imm(0))
		if op == "all" {
			g.emit("cset", wr(r), asm.Condition{Code: "eq"})
		} else {
			g.emit("cset", wr(r), asm.Condition{Code: "ne"})
		}
		g.release(t)
		return r, nil
	case "tbl":
		t, tfixed, err := g.vecOperand(args[0], shape)
		if err != nil {
			return 0, err
		}
		i, ifixed, err := g.vecOperand(args[1], shape)
		if err != nil {
			return 0, err
		}
		out, err := g.vecDest(t, tfixed, shape)
		if err != nil {
			return 0, err
		}
		g.emit("tbl", vreg(out-vecBase, "16b"), asm.RegisterList{Regs: []asm.Register{vreg(t-vecBase, "16b")}}, vreg(i-vecBase, "16b"))
		g.vecRelease(i, ifixed)
		return out, nil
	case "prev":
		n, isConst := constantValue(args[2])
		if !isConst {
			return 0, unsupported("simd.%s by a count that is not a literal", member)
		}
		if n < 0 || n > 16 {
			return 0, unsupported("simd.%s by %d (above sixteen traps)", member, n)
		}
		prev, prevfixed, err := g.vecOperand(args[0], shape)
		if err != nil {
			return 0, err
		}
		cur, curfixed, err := g.vecOperand(args[1], shape)
		if err != nil {
			return 0, err
		}
		switch n {
		case 0:
			g.vecRelease(prev, prevfixed)
			out, err := g.vecDest(cur, curfixed, shape)
			if err != nil {
				return 0, err
			}
			if curfixed {
				g.vmove(out-vecBase, cur-vecBase)
			}
			return out, nil
		case 16:
			g.vecRelease(cur, curfixed)
			out, err := g.vecDest(prev, prevfixed, shape)
			if err != nil {
				return 0, err
			}
			if prevfixed {
				g.vmove(out-vecBase, prev-vecBase)
			}
			return out, nil
		}
		out, err := g.vecDest(prev, prevfixed, shape)
		if err != nil {
			return 0, err
		}
		// the sixteen bytes ending n before the end of prev ++ cur
		g.emit("ext", vreg(out-vecBase, "16b"), vreg(prev-vecBase, "16b"), vreg(cur-vecBase, "16b"), imm(16-n))
		g.vecRelease(cur, curfixed)
		return out, nil
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
func (s scalar) laneName() string {
	if s.laneFloat {
		return "f" + strconv.Itoa(s.laneBits)
	}
	return "u" + strconv.Itoa(s.laneBits)
}

// loopFact: an enclosing `while len(span) >= u32(N) && index <= len(span)
// - u32(N)` proves index + N <= len(span) in its body until index is
// assigned (slack 0 afterwards).
type loopFact struct {
	span, index string
	slack       int64
}

// loopFactsOf reads the facts a while condition proves: for each pair of
// conjuncts `len(v) >= u32(N)` and `i <= len(v) - u32(N)` over one view
// and one index variable, the fact (v, i, N).
func loopFactsOf(cond ast.Expression) []loopFact {
	var conjuncts []ast.Expression
	var flatten func(e ast.Expression)
	flatten = func(e ast.Expression) {
		if infix, ok := e.(*ast.InfixExpression); ok && infix.Operator == "&&" {
			flatten(infix.Left)
			flatten(infix.Right)
			return
		}
		conjuncts = append(conjuncts, e)
	}
	flatten(cond)
	lenOf := func(e ast.Expression) (string, bool) {
		call, ok := e.(*ast.InvocationExpression)
		if !ok || len(call.Arguments) != 1 {
			return "", false
		}
		fn, isIdent := call.Function.(*ast.Identifier)
		arg, argIdent := call.Arguments[0].(*ast.Identifier)
		if !isIdent || fn.Value != "len" || !argIdent {
			return "", false
		}
		return arg.Value, true
	}
	mins := map[string]int64{} // view -> N from len(v) >= N
	for _, c := range conjuncts {
		infix, ok := c.(*ast.InfixExpression)
		if !ok {
			continue
		}
		if infix.Operator == ">=" {
			if v, isLen := lenOf(infix.Left); isLen {
				if n, isConst := constantValue(infix.Right); isConst && n > 0 {
					mins[v] = n
				}
			}
		}
	}
	var out []loopFact
	for _, c := range conjuncts {
		infix, ok := c.(*ast.InfixExpression)
		if !ok || infix.Operator != "<=" {
			continue
		}
		index, isIdent := infix.Left.(*ast.Identifier)
		diff, isDiff := infix.Right.(*ast.InfixExpression)
		if !isIdent || !isDiff || diff.Operator != "-" {
			continue
		}
		v, isLen := lenOf(diff.Left)
		n, isConst := constantValue(diff.Right)
		if !isLen || !isConst || mins[v] != n {
			continue
		}
		out = append(out, loopFact{span: v, index: index.Value, slack: n})
	}
	return out
}

// killLoopFacts forgets what the loop conditions proved about an index
// variable once it is assigned.
func (g *generator) killLoopFacts(name string) {
	for i := range g.loopFacts {
		if g.loopFacts[i].index == name {
			g.loopFacts[i].slack = 0
		}
	}
}

// provenLanes is how many elements past the index expression the loop
// conditions prove inside the span: the fact's slack for the index
// variable itself, less a literal offset added to it; zero when nothing
// is proven. A fact over a span the enclosing conditionals prove to have
// this span's length (equalLens) is this span's fact.
func (g *generator) provenLanes(spanName string, index ast.Expression) int64 {
	name, offset := "", int64(0)
	switch e := index.(type) {
	case *ast.Identifier:
		name = e.Value
	case *ast.InfixExpression:
		ident, isIdent := e.Left.(*ast.Identifier)
		k, isConst := constantValue(e.Right)
		if e.Operator != "+" || !isIdent || !isConst || k < 0 {
			return 0
		}
		name, offset = ident.Value, k
	default:
		return 0
	}
	for _, fact := range g.loopFacts {
		if g.equalLens.same(fact.span, spanName) && fact.index == name && fact.slack > offset {
			return fact.slack - offset
		}
	}
	return 0
}

// vecGuardedIndex evaluates the element index of a vector access and emits
// the check that the L lanes lie within the length: `len >= L` and
// `index <= len - L`, each a compare and a branch to the trap — unless an
// enclosing loop condition already proves it (provenLanes), in which case
// the checker reads the proof off the condition's own compares.
func (g *generator) vecGuardedIndex(sp span, operand, index ast.Expression, shape scalar) (int, error) {
	r, err := g.indexValue(index)
	if err != nil {
		return 0, err
	}
	if ident, isIdent := operand.(*ast.Identifier); isIdent && g.provenLanes(ident.Value, index) >= int64(shape.lanes) {
		return r, nil
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

// vecAddress is the address of the sixteen bytes at element index wIdx.
// Over byte lanes it is `[base, wIdx, uxtw]` (a q load indexes by bytes
// or by sixteens, never by a lane size between); over wider lanes the
// element address is formed first, `add xE, xB, wIdx, uxtw #s`, which the
// checker records as the region of the guard's lanes (the slack guard
// `wIdx + lanes <= len` proves every byte inside the span,
// Oak.Assembler.index_access_lanes), and the access is `[xE]`. The second
// result is the address register to release, or -1.
func (g *generator) vecAddress(sp span, idx int, shape scalar) (asm.Memory, int, error) {
	w := wr(idx)
	if shape.laneBits == 8 {
		return asm.Memory{Base: xr(sp.baseReg), Index: &w, Shift: 0, Extend: "uxtw"}, -1, nil
	}
	element, err := g.alloc(scalars["u64"])
	if err != nil {
		return asm.Memory{}, -1, err
	}
	g.emit("add", xr(element), xr(sp.baseReg), asm.Extended{Reg: w, Kind: "uxtw", Amount: int64(log2Bytes(shape.laneBits / 8))})
	return asm.Memory{Base: xr(element)}, element, nil
}

// releaseAddr releases the address register vecAddress allocated, if any.
func (g *generator) releaseAddr(r int) {
	if r >= 0 {
		g.release(r)
	}
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
const VectorContractSuffix = "_neon_abi" // asm.VectorEntrySuffix(asm.ArchArm64)

// RVVContractSuffix is the RV64 lane's counterpart (docs/spec/94-assembler.md
// §9, "vectors across the call boundary"): the native entry takes its
// vectors in the RVV psABI's argument registers v8–v23 and returns one in
// v8, where the C backend's lane-array struct crosses in the integer
// registers, so the C emitter defines the Oak name as a converting shim
// over the suffixed entry (codegen/codegen.go emitVectorShim).
const RVVContractSuffix = "_rvv_abi" // asm.VectorEntrySuffix(asm.ArchRV64)

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
// under on the AArch64 lane: the function's own name, suffixed under the
// vector contract.
func NativeSymbol(fn *ast.FunctionStatement) string {
	return NativeSymbolFor(asm.ArchArm64, fn)
}

// NativeSymbolFor is NativeSymbol on the given lane: the vector contract's
// suffix is the lane's (`_neon_abi`, `_rvv_abi`).
func NativeSymbolFor(arch string, fn *ast.FunctionStatement) string {
	if VectorContract(fn) {
		return fn.Name.Value + asm.VectorEntrySuffix(arch)
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
