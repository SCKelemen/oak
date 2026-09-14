package nativegen

import (
	"strconv"
	"strings"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// Portable SIMD on the RV64 lane (docs/spec/93-simd.md section 1.4 "The
// native backend", 94-assembler.md section 9): the fixed 128-bit vectors
// simd.U8x16, U16x8, U32x4, and U64x2 are values of the vector register
// file under a configuration the lowering sets itself — `vsetivli zero,
// <lanes>, e<bits>, m1, ta, ma` before every vector instruction group, the
// configuration being straight-line checker state that labels and calls
// forget (RVV 1.0 section 6; the psABI preserves neither vl nor vtype).
// VLEN >= 128 on every processor with V, so a fixed vector is one LMUL=1
// register whatever the VLEN, and the same lowering runs at 128, 256, ...
//
// Registers: v8–v15 are the operand stack (all vector registers are
// caller-saved under the psABI, so a vector local lives in a sixteen-byte
// frame slot and a live scratch is spilled to one around a call); v0 is
// the mask, v1 and v2 are the helpers the multi-instruction operations
// use; t6 addresses frame slots (excluded from the integer scratch pool
// in a function that mentions vectors). Every operation is its RVV
// instruction: `splat` -> vmv.v.x; `load`/`store` -> vle/vse of the lane
// width under the slack guard (`bltu len, k; sub t, len, k; bltu t, idx` —
// Oak.RiscV.slack_guard, slack_access_in_bounds) or at a frame address;
// `add`/`sub`/`and`/`or`/`xor`/`min`/`max`/`subs` -> vadd/vsub/vand/vor/
// vxor/vminu/vmaxu/vssubu .vv; `eq` -> vmseq.vv into v0 then vmerge.vvm of
// all-ones over zero; `shr` by a literal -> vsrl.vx; `any`/`all` ->
// vmsne.vx against zero then vcpop.m; `movemask` -> vmslt.vx against zero
// (the top bit is the sign) then the mask register's low bits through
// vmv.x.s at e32; `tbl` -> vrgather.vv under the index-below-16 mask
// (vmsltu.vx), as the C realization does; `prev` by a literal ->
// vslidedown.vi then vslideup.vi. The float vectors simd.F32x4/F64x2
// (docs/spec/93-simd.md section 1.2a) lower the same way under an e32/e64
// configuration: `splat` -> vfmv.v.f; `add`/`sub`/`mul`/`div` -> vfadd/
// vfsub/vfmul/vfdiv .vv; `fma` -> vfmacc.vv into the addend's register
// (one rounding); `sqrt` -> vfsqrt.v; `neg`/`abs` -> vfsgnjn/vfsgnjx .vv of
// a value with itself; `min`/`max` -> vfmin/vfmax .vv (IEEE minimumNumber/
// maximumNumber: -0.0 below +0.0, a NaN operand suppressed) then the
// catalog's NaN propagation restored lane by lane — `vmfne.vv v0, x, x`
// marks x's NaN lanes and `vmerge.vvm` puts x back there, for each
// operand (Oak.Simd.rvvMinMax); `extract` at a literal lane ->
// vslidedown.vi then vfmv.f.s; `insert` at a literal lane -> vid.v,
// vmseq.vx against the lane, vfmerge.vfm; `reduce_add` -> the
// specification's pairwise tree (l0 + l1) + (l2 + l3), two slide-and-add
// steps (Oak.Simd.rvv_reduce4: t = x + slide(x, 1); (t + slide(t, 2))[0]),
// one step for two lanes, never vfredosum's sequential fold. What this
// lane leaves to the C backend, reported as such: vectors in signatures
// (the LP64 struct contract), records or arrays of vectors, a shift,
// `prev`, `extract`, or `insert` count that is not a literal, and the
// ctz/popcount helpers (no Zbb).

// rvVBase offsets the vector register file in the generator's numbering:
// register rvVBase+n is vN.
const rvVBase = 300

// rvVScratch is the vector operand stack: v8–v15.
var rvVScratch = []int{8, 9, 10, 11, 12, 13, 14, 15}

// rvVAddr is t6 (x31), the frame-address register of the vector spills and
// locals; rvVMask, rvVHelp1, rvVHelp2 are v0, v1, v2. rvVArg0 and rvVArgs
// are the RVV psABI's vector argument registers v8–v23 (a vector result
// returns in v8), the contract of a function whose signature carries a
// fixed vector (docs/spec/94-assembler.md §9, Oak.RiscV.lp64dBinding).
const (
	rvVAddr  = 31
	rvVMask  = 0
	rvVHelp1 = 1
	rvVHelp2 = 2
	rvVCount = 16 // v0–v15 are the registers a vector function clobbers
	rvVArg0  = 8
	rvVArgs  = 16
)

func rvVReg(n int) asm.Register {
	return asm.Register{Text: "v" + strconv.Itoa(n), Class: asm.ClassRV64V, Num: n, Lane: -1}
}

// vsr spells vector scratch register r (rvVBase + n).
func vsr(r int) asm.Register { return rvVReg(r - rvVBase) }

func vopt(name string) asm.Option { return asm.Option{Name: name} }

// vmem is the `(base)` memory operand of a vector load or store.
func vmem(base int) asm.Memory {
	return asm.Memory{Base: rvReg(base), Offset: 0, Mode: asm.MemOffset}
}

// vconf sets the configuration of a shape: its lane count as the AVL and
// its lane width as the SEW, one register (m1), tail and mask agnostic.
func (g *rvGenerator) vconf(shape scalar) {
	g.vconfAt(int64(shape.lanes), shape.laneBits)
}

func (g *rvGenerator) vconfAt(lanes int64, bits int) {
	g.usedVector = true
	g.emit("vsetivli", rvReg(rvZero), imm(lanes), vopt("e"+strconv.Itoa(bits)), vopt("m1"), vopt("ta"), vopt("ma"))
}

// vconfBytes is the whole-register configuration (sixteen bytes) a copy,
// a spill, or a local's store uses whatever the value's shape.
func (g *rvGenerator) vconfBytes() { g.vconfAt(16, 8) }

// rvVectorLoad and rvVectorStore are the unit-stride memory instructions
// of a lane width.
func rvVectorLoad(bits int) string  { return "vle" + strconv.Itoa(bits) + ".v" }
func rvVectorStore(bits int) string { return "vse" + strconv.Itoa(bits) + ".v" }

// mentionsVector reports a function that names a fixed vector type or calls
// a simd operation: it needs the vector extension.
func mentionsVector(fn *ast.FunctionStatement) bool {
	isVec := func(expr ast.Expression) bool {
		s, ok := scalarOf(expr)
		return ok && s.isVec
	}
	for _, p := range fn.Parameters {
		if isVec(p.Type) {
			return true
		}
	}
	if fn.ReturnType != nil && isVec(fn.ReturnType) {
		return true
	}
	found := false
	walk(fn.Body, func(n ast.Node) {
		switch e := n.(type) {
		case *ast.VariableDeclaration:
			if e.Type != nil && isVec(e.Type) {
				found = true
			}
		case *ast.InvocationExpression:
			if _, isSimd := simdCallee(e.Function); isSimd {
				found = true
			}
		}
	})
	return found
}

// rvMentionsFloat is mentionsFloat for a lane whose vector file is not the
// floating-point file: the fixed vectors do not count.
func rvMentionsFloat(fn *ast.FunctionStatement) bool {
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
	// A float vector's lanes cross through the floating-point file (splat,
	// extract, insert, reduce_add), so it counts too.
	isFloatVec := func(expr ast.Expression) bool {
		s, ok := scalarOf(expr)
		return ok && s.isVec && s.laneFloat
	}
	found := false
	walk(fn.Body, func(n ast.Node) {
		switch e := n.(type) {
		case *ast.FloatLiteral:
			found = true
		case *ast.VariableDeclaration:
			if e.Type != nil && (isFloatType(e.Type) || isFloatVec(e.Type)) {
				found = true
			}
		case *ast.InvocationExpression:
			if ident, ok := e.Function.(*ast.Identifier); ok && (strings.Contains(ident.Value, "f32") || strings.Contains(ident.Value, "f64") || typechecker.FloatIntrinsicName(ident.Value)) {
				found = true
			}
			if member, isSimd := simdCallee(e.Function); isSimd && (strings.HasSuffix(member, "_f32x4") || strings.HasSuffix(member, "_f64x2")) {
				found = true
			}
		}
	})
	return found
}

// vecSlotStore writes vector scratch r into the sixteen-byte frame slot at
// offset; vecSlotLoad reads it back. The slot's address goes through t6
// (`addi t6, sp, off`: a frame address the checker admits a fixed vector
// through, Oak.RiscV.frame_vector_in_bounds).
func (g *rvGenerator) vecSlotStore(r int, offset int64) {
	g.emit("addi", rvReg(rvVAddr), rvSP(), imm(g.slotMem(offset).Offset))
	g.vconfBytes()
	g.emit("vse8.v", vsr(r), vmem(rvVAddr))
}

// vecSlotStoreItems is vecSlotStore as prologue items (a vector parameter
// stored to its slot before the body).
func (g *rvGenerator) vecSlotStoreItems(r int, offset int64) []asm.Item {
	g.usedVector = true
	return []asm.Item{
		g.ins("addi", rvReg(rvVAddr), rvSP(), imm(g.slotMem(offset).Offset)),
		g.ins("vsetivli", rvReg(rvZero), imm(16), vopt("e8"), vopt("m1"), vopt("ta"), vopt("ma")),
		g.ins("vse8.v", vsr(r), vmem(rvVAddr)),
	}
}

func (g *rvGenerator) vecSlotLoad(r int, offset int64) {
	g.emit("addi", rvReg(rvVAddr), rvSP(), imm(g.slotMem(offset).Offset))
	g.vconfBytes()
	g.emit("vle8.v", vsr(r), vmem(rvVAddr))
}

// storeVec and loadVec move a vector between a scratch register and a
// variable's slot (every vector local lives in the frame).
func (g *rvGenerator) storeVec(name string, r int) { g.vecSlotStore(r, g.slots[name]) }
func (g *rvGenerator) loadVec(name string, r int)  { g.vecSlotLoad(r, g.slots[name]) }

// moveVec copies a vector register: `vor.vv dst, src, src` over the whole
// register.
func (g *rvGenerator) moveVec(dst, src int) {
	if dst == src {
		return
	}
	g.vconfBytes()
	g.emit("vor.vv", vsr(dst), vsr(src), vsr(src))
}

// rvSimdOp lowers one simd call on the rv64 lane; the result register is a
// vector scratch for a vector result, a general scratch for Bool/u32, -1
// for store.
func (g *rvGenerator) rvSimdOp(member string, args []ast.Expression) (int, error) {
	switch member {
	case "ctz_u32", "ctz_u64", "popcount_u32", "popcount_u64":
		return 0, unsupported("simd.%s (the rv64 lane assumes no bit-manipulation extension)", member)
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
	g.usedVector = true
	lanes := int64(shape.lanes)
	switch op {
	case "splat":
		elem := scalars[shape.laneName()]
		r, err := g.exprAs(args[0], elem)
		if err != nil {
			return 0, err
		}
		v, err := g.alloc(shape)
		if err != nil {
			return 0, err
		}
		g.vconf(shape)
		if shape.laneFloat {
			g.emit("vfmv.v.f", vsr(v), rvReg(r))
		} else {
			g.emit("vmv.v.x", vsr(v), rvReg(r))
		}
		g.release(r)
		return v, nil
	case "load":
		return g.rvSimdLoad(member, shape, args[0], args[1])
	case "store":
		return g.rvSimdStore(member, shape, args[0], args[1], args[2])
	case "add", "sub", "and", "or", "xor", "min", "max", "subs", "mul", "div":
		if shape.laneFloat {
			return g.rvSimdFloatBinary(op, shape, args[0], args[1])
		}
		mnemonic := map[string]string{"add": "vadd.vv", "sub": "vsub.vv", "and": "vand.vv", "or": "vor.vv", "xor": "vxor.vv", "min": "vminu.vv", "max": "vmaxu.vv", "subs": "vssubu.vv"}[op]
		a, err := g.expr(args[0], &shape)
		if err != nil {
			return 0, err
		}
		b, err := g.expr(args[1], &shape)
		if err != nil {
			return 0, err
		}
		g.vconf(shape)
		g.emit(mnemonic, vsr(a), vsr(a), vsr(b))
		g.release(b)
		return a, nil
	case "fma":
		// vfmacc.vv vd, vs1, vs2: vd = vs1 * vs2 + vd in one rounding; the
		// addend's register is the destination.
		a, err := g.expr(args[0], &shape)
		if err != nil {
			return 0, err
		}
		b, err := g.expr(args[1], &shape)
		if err != nil {
			return 0, err
		}
		c, err := g.expr(args[2], &shape)
		if err != nil {
			return 0, err
		}
		g.vconf(shape)
		g.emit("vfmacc.vv", vsr(c), vsr(a), vsr(b))
		g.release(b)
		g.release(a)
		return c, nil
	case "sqrt", "neg", "abs":
		a, err := g.expr(args[0], &shape)
		if err != nil {
			return 0, err
		}
		g.vconf(shape)
		switch op {
		case "sqrt":
			g.emit("vfsqrt.v", vsr(a), vsr(a))
		case "neg":
			g.emit("vfsgnjn.vv", vsr(a), vsr(a), vsr(a)) // the sign negated: -x
		default:
			g.emit("vfsgnjx.vv", vsr(a), vsr(a), vsr(a)) // the sign xored with itself: |x|
		}
		return a, nil
	case "extract":
		// Lane k: slid down to element 0 (k > 0), then out through vfmv.f.s.
		k, isConst := constantValue(args[1])
		if !isConst {
			return 0, unsupported("simd.%s at a lane that is not a literal", member)
		}
		if k < 0 || k >= lanes {
			return 0, unsupported("simd.%s at lane %d (past the lanes; traps)", member, k)
		}
		a, err := g.expr(args[0], &shape)
		if err != nil {
			return 0, err
		}
		r, err := g.alloc(scalars[shape.laneName()])
		if err != nil {
			return 0, err
		}
		g.vconf(shape)
		src := vsr(a)
		if k > 0 {
			g.emit("vslidedown.vi", rvVReg(rvVHelp1), vsr(a), imm(k))
			src = rvVReg(rvVHelp1)
		}
		g.emit("vfmv.f.s", rvReg(r), src)
		g.release(a)
		return r, nil
	case "insert":
		// The vector with lane k replaced: the lane indices (vid.v) compared
		// with k give the one-lane mask, and vfmerge.vfm puts the scalar
		// there and keeps the rest.
		k, isConst := constantValue(args[1])
		if !isConst {
			return 0, unsupported("simd.%s at a lane that is not a literal", member)
		}
		if k < 0 || k >= lanes {
			return 0, unsupported("simd.%s at lane %d (past the lanes; traps)", member, k)
		}
		a, err := g.expr(args[0], &shape)
		if err != nil {
			return 0, err
		}
		f, err := g.exprAs(args[2], scalars[shape.laneName()])
		if err != nil {
			return 0, err
		}
		g.vconf(shape)
		g.emit("vid.v", rvVReg(rvVHelp1))
		g.emit("li", rvReg(rvVAddr), imm(k))
		g.emit("vmseq.vx", rvVReg(rvVMask), rvVReg(rvVHelp1), rvReg(rvVAddr))
		g.emit("vfmerge.vfm", vsr(a), vsr(a), rvReg(f), rvVReg(rvVMask))
		g.release(f)
		return a, nil
	case "reduce_add":
		// The pairwise tree (l0 + l1) + (l2 + l3) (docs/spec/93-simd.md
		// section 1.2a; Oak.Simd.rvv_reduce4): t = x + slide(x, 1) holds
		// l0+l1 at lane 0 and l2+l3 at lane 2; t + slide(t, 2) holds the
		// tree at lane 0. Two lanes: one step. The slides read the tail
		// past vl into the lanes the result never reads.
		a, err := g.expr(args[0], &shape)
		if err != nil {
			return 0, err
		}
		r, err := g.alloc(scalars[shape.laneName()])
		if err != nil {
			return 0, err
		}
		g.vconf(shape)
		g.emit("vslidedown.vi", rvVReg(rvVHelp1), vsr(a), imm(1))
		g.emit("vfadd.vv", vsr(a), vsr(a), rvVReg(rvVHelp1))
		if lanes == 4 {
			g.emit("vslidedown.vi", rvVReg(rvVHelp1), vsr(a), imm(2))
			g.emit("vfadd.vv", vsr(a), vsr(a), rvVReg(rvVHelp1))
		}
		g.emit("vfmv.f.s", rvReg(r), vsr(a))
		g.release(a)
		return r, nil
	case "eq":
		// The equal lanes as a mask in v0, then all-ones where the mask
		// holds over zero elsewhere (vmerge.vvm vd, vs2, vs1, v0: vs1 where
		// v0 is set) — the catalog's all-ones/zero lane result.
		a, err := g.expr(args[0], &shape)
		if err != nil {
			return 0, err
		}
		b, err := g.expr(args[1], &shape)
		if err != nil {
			return 0, err
		}
		g.vconf(shape)
		g.emit("vmseq.vv", rvVReg(rvVMask), vsr(a), vsr(b))
		g.emit("vmv.v.x", rvVReg(rvVHelp1), rvReg(rvZero))
		g.emit("li", rvReg(rvVAddr), imm(-1))
		g.emit("vmv.v.x", rvVReg(rvVHelp2), rvReg(rvVAddr))
		g.emit("vmerge.vvm", vsr(a), rvVReg(rvVHelp1), rvVReg(rvVHelp2), rvVReg(rvVMask))
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
			g.emit("li", rvReg(rvVAddr), imm(count))
			g.vconf(shape)
			g.emit("vsrl.vx", vsr(a), vsr(a), rvReg(rvVAddr))
		}
		return a, nil
	case "any", "all":
		a, err := g.expr(args[0], &shape)
		if err != nil {
			return 0, err
		}
		r, err := g.alloc(scalars["Bool"])
		if err != nil {
			return 0, err
		}
		g.vconf(shape)
		// The nonzero lanes as a mask; their count decides.
		g.emit("vmsne.vx", rvVReg(rvVMask), vsr(a), rvReg(rvZero))
		g.emit("vcpop.m", rvReg(r), rvVReg(rvVMask))
		if op == "any" {
			g.emit("sltu", rvReg(r), rvReg(rvZero), rvReg(r)) // count != 0
		} else {
			g.emit("addi", rvReg(r), rvReg(r), imm(-lanes))
			g.emit("sltiu", rvReg(r), rvReg(r), imm(1)) // count == lanes
		}
		g.release(a)
		return r, nil
	case "movemask":
		// Bit i is the top bit of lane i (Oak.Simd.movemask): the lanes
		// whose signed value is negative, as a mask in v0, whose low
		// `lanes` bits are the result — read through element 0 at e32
		// (the mask register's tail bits are agnostic, so they are cleared).
		a, err := g.expr(args[0], &shape)
		if err != nil {
			return 0, err
		}
		r, err := g.alloc(scalars["u32"])
		if err != nil {
			return 0, err
		}
		g.vconf(shape)
		g.emit("vmslt.vx", rvVReg(rvVMask), vsr(a), rvReg(rvZero))
		g.vconfAt(1, 32)
		g.emit("vmv.x.s", rvReg(r), rvVReg(rvVMask))
		if lanes == 16 {
			g.emit("slli", rvReg(r), rvReg(r), imm(48))
			g.emit("srli", rvReg(r), rvReg(r), imm(48))
		} else {
			g.emit("andi", rvReg(r), rvReg(r), imm((int64(1)<<uint(lanes))-1))
		}
		g.release(a)
		return r, nil
	case "tbl":
		// vrgather reads lane idx[i] of the table for idx[i] below VLMAX
		// and gives zero above it; VLMAX depends on VLEN, so the index-
		// below-16 rule is applied explicitly (the C realization's rule)
		// and the result is the same on every VLEN. The gather's
		// destination is disjoint from its sources (RVV 1.0 section 16.4).
		t, err := g.expr(args[0], &shape)
		if err != nil {
			return 0, err
		}
		i, err := g.expr(args[1], &shape)
		if err != nil {
			return 0, err
		}
		g.emit("li", rvReg(rvVAddr), imm(16))
		g.vconf(shape)
		g.emit("vmsltu.vx", rvVReg(rvVMask), vsr(i), rvReg(rvVAddr))
		g.emit("vrgather.vv", rvVReg(rvVHelp1), vsr(t), vsr(i))
		g.emit("vmv.v.x", rvVReg(rvVHelp2), rvReg(rvZero))
		g.emit("vmerge.vvm", vsr(t), rvVReg(rvVHelp2), rvVReg(rvVHelp1), rvVReg(rvVMask))
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
		// Lane i is prev[16-n+i] below n and cur[i-n] from n on: slide
		// prev down by 16-n into the helper, copy it back, then slide cur
		// up by n over it (vslideup leaves the lanes below n unchanged).
		g.vconf(shape)
		g.emit("vslidedown.vi", rvVReg(rvVHelp1), vsr(prev), imm(16-n))
		g.emit("vor.vv", vsr(prev), rvVReg(rvVHelp1), rvVReg(rvVHelp1))
		g.emit("vslideup.vi", vsr(prev), vsr(cur), imm(n))
		g.release(cur)
		return prev, nil
	}
	return 0, unsupported("the simd operation %s", member)
}

// rvSimdFloatBinary lowers the lane-wise float arithmetic and the catalog's
// min/max (docs/spec/93-simd.md section 1.2a): add/sub/mul/div are one
// instruction; min/max are IEEE 754-2019 minimum/maximum — RVV's vfmin/
// vfmax are minimumNumber/maximumNumber (-0.0 below +0.0 as required, but a
// quiet NaN operand suppressed), so each operand's NaN lanes, found by
// comparing it with itself (vmfne.vv), are merged back over the result
// (Oak.Simd.rvvMinMax: a NaN operand yields that NaN, the rest is the
// number-preferring minimum, which agrees with the catalog on numbers).
func (g *rvGenerator) rvSimdFloatBinary(op string, shape scalar, left, right ast.Expression) (int, error) {
	a, err := g.expr(left, &shape)
	if err != nil {
		return 0, err
	}
	b, err := g.expr(right, &shape)
	if err != nil {
		return 0, err
	}
	g.vconf(shape)
	switch op {
	case "add", "sub", "mul", "div":
		mnemonic := map[string]string{"add": "vfadd.vv", "sub": "vfsub.vv", "mul": "vfmul.vv", "div": "vfdiv.vv"}[op]
		g.emit(mnemonic, vsr(a), vsr(a), vsr(b))
	case "min", "max":
		mnemonic := map[string]string{"min": "vfmin.vv", "max": "vfmax.vv"}[op]
		g.emit(mnemonic, rvVReg(rvVHelp1), vsr(a), vsr(b))
		g.emit("vmfne.vv", rvVReg(rvVMask), vsr(a), vsr(a))
		g.emit("vmerge.vvm", rvVReg(rvVHelp1), rvVReg(rvVHelp1), vsr(a), rvVReg(rvVMask))
		g.emit("vmfne.vv", rvVReg(rvVMask), vsr(b), vsr(b))
		g.emit("vmerge.vvm", vsr(a), rvVReg(rvVHelp1), vsr(b), rvVReg(rvVMask))
	default:
		return 0, unsupported("the simd operation %s over float lanes", op)
	}
	g.release(b)
	return a, nil
}

// rvSimdLoad lowers `simd.load_*(v, i)`: a literal index into an owned array
// local is a frame slot (a frame address, checked here to lie inside the
// array); an index into a span goes through the slack guard.
func (g *rvGenerator) rvSimdLoad(member string, shape scalar, operand, index ast.Expression) (int, error) {
	if arr, k, ok := g.vecArrayOperand(operand, index, shape, false); ok {
		v, err := g.alloc(shape)
		if err != nil {
			return 0, err
		}
		g.emit("addi", rvReg(rvVAddr), rvSP(), imm(g.slotMem(arr.offset+k).Offset))
		g.vconf(shape)
		g.emit(rvVectorLoad(shape.laneBits), vsr(v), vmem(rvVAddr))
		return v, nil
	}
	sp, err := g.spanOperand(operand)
	if err != nil {
		return 0, err
	}
	if sp.elem.name != shape.laneName() {
		return 0, unsupported("simd.%s over a view of %s", member, sp.elem.name)
	}
	address, err := g.rvVecGuardedAddress(sp, index, shape)
	if err != nil {
		return 0, err
	}
	v, err := g.alloc(shape)
	if err != nil {
		return 0, err
	}
	g.vconf(shape)
	g.emit(rvVectorLoad(shape.laneBits), vsr(v), vmem(address))
	g.release(address)
	return v, nil
}

// rvSimdStore lowers `simd.store_*(s, i, x)` through a writable span or an
// owned array local.
func (g *rvGenerator) rvSimdStore(member string, shape scalar, operand, index, value ast.Expression) (int, error) {
	if arr, k, ok := g.vecArrayOperand(operand, index, shape, true); ok {
		v, err := g.expr(value, &shape)
		if err != nil {
			return 0, err
		}
		g.emit("addi", rvReg(rvVAddr), rvSP(), imm(g.slotMem(arr.offset+k).Offset))
		g.vconf(shape)
		g.emit(rvVectorStore(shape.laneBits), vsr(v), vmem(rvVAddr))
		g.release(v)
		return -1, nil
	}
	sp, err := g.spanOperand(operand)
	if err != nil {
		return 0, err
	}
	if !sp.writable {
		return 0, unsupported("simd.%s through a read-only view", member)
	}
	if sp.elem.name != shape.laneName() {
		return 0, unsupported("simd.%s over a span of %s", member, sp.elem.name)
	}
	v, err := g.expr(value, &shape)
	if err != nil {
		return 0, err
	}
	address, err := g.rvVecGuardedAddress(sp, index, shape)
	if err != nil {
		return 0, err
	}
	g.vconf(shape)
	g.emit(rvVectorStore(shape.laneBits), vsr(v), vmem(address))
	g.release(address)
	g.release(v)
	return -1, nil
}

// rvVecGuardedAddress evaluates the element index of a K-lane vector
// access and emits the slack guard the checker reads (docs/spec/
// 94-assembler.md section 9, Oak.RiscV.slack_guard): `li k, K; bltu len,
// k, trap` (len >= K), `sub t, len, k` (t = len - K), `bltu t, idx, trap`
// (idx <= len - K), so idx + K <= len on the fall-through — then the
// element address `base + (idx << s)`, whose region the checker marks K
// lanes deep (Oak.RiscV.slack_access_in_bounds). The index register is
// spent: it holds the address.
func (g *rvGenerator) rvVecGuardedAddress(sp span, index ast.Expression, shape scalar) (int, error) {
	idxType, err := g.typeOf(index, nil)
	if err != nil {
		return 0, err
	}
	if idxType.isBool || idxType.isFloat || idxType.isVec || (idxType.signed && idxType.bits != 32) {
		return 0, unsupported("an element index of type %s (indices are unsigned or i32)", idxType.name)
	}
	r, err := g.expr(index, &idxType)
	if err != nil {
		return 0, err
	}
	R := rvReg(r)
	if idxType.bits < 64 && !idxType.signed {
		g.emit("slli", R, R, imm(32))
		g.emit("srli", R, R, imm(32))
	}
	k, err := g.alloc(scalars["u64"])
	if err != nil {
		return 0, err
	}
	t, err := g.alloc(scalars["u64"])
	if err != nil {
		return 0, err
	}
	g.usedTrap = true
	g.emit("li", rvReg(k), imm(int64(shape.lanes)))
	g.emit("bltu", rvReg(sp.norm), rvReg(k), asm.Symbol{Name: g.trap})
	g.emit("sub", rvReg(t), rvReg(sp.norm), rvReg(k))
	g.emit("bltu", rvReg(t), R, asm.Symbol{Name: g.trap})
	g.release(t)
	g.release(k)
	if shift := log2Bytes(shape.laneBits / 8); shift > 0 {
		g.emit("slli", R, R, imm(int64(shift)))
	}
	g.emit("add", R, rvReg(sp.baseReg), R)
	return r, nil
}
