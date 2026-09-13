package codegen

// C backend lowering for the portable simd library and the arm64 vector
// instruction functions (docs/spec/93-simd.md). One struct ABI per vector
// type serves both lowerings; each used operation gets one static inline
// helper — NEON when the AArch64 target enables it, the portable C99 lane
// loop otherwise. All emitted names come from the fixed compiler catalog;
// no user-controlled strings reach the generated C.

import (
	"fmt"
	"github.com/SCKelemen/oak/semir"
	"reflect"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// simdBinaryOps are the lane-wise binary operations and their portable C
// lane expressions (over element values x and y).
var simdBinaryOps = map[string]string{
	"add":  "(%[1]s)(x + y)",
	"sub":  "(%[1]s)(x - y)",
	"subs": "(x > y ? (%[1]s)(x - y) : (%[1]s)0)",
	"and":  "(%[1]s)(x & y)",
	"or":   "(%[1]s)(x | y)",
	"xor":  "(%[1]s)(x ^ y)",
	"min":  "(x < y ? x : y)",
	"max":  "(x > y ? x : y)",
	"eq":   "(%[1]s)(x == y ? (%[1]s)~(%[1]s)0 : (%[1]s)0)",
}

// neonBinary maps binary ops to their NEON intrinsic name stems. 64-bit
// lane min/max have no NEON instruction and use compare-and-select; they
// are handled specially.
var neonBinary = map[string]string{
	"add": "vaddq", "sub": "vsubq", "subs": "vqsubq", "and": "vandq", "or": "vorrq",
	"xor": "veorq", "min": "vminq", "max": "vmaxq", "eq": "vceqq",
}

// simdOpSplit destructures a simd catalog member ("load_u8x16") into its
// op name and vector shape.
func simdOpSplit(member string) (op string, shape typechecker.SimdShape, ok bool) {
	splitAt := strings.LastIndex(member, "_")
	if splitAt <= 0 {
		return "", shape, false
	}
	op = member[:splitAt]
	shape, known := typechecker.SimdShapeBySuffix(member[splitAt+1:])
	if !known {
		return "", shape, false
	}
	if shape.Float {
		switch op {
		case "splat", "load", "store", "fma", "extract", "insert", "reduce_add":
			return op, shape, true
		}
		for _, name := range typechecker.SimdFloatBinaryOps {
			if name == op {
				return op, shape, true
			}
		}
		for _, name := range typechecker.SimdFloatUnaryOps {
			if name == op {
				return op, shape, true
			}
		}
		return "", shape, false
	}
	switch op {
	case "splat", "load", "store", "any", "all", "shr", "movemask":
		return op, shape, true
	case "tbl", "prev":
		return op, shape, shape.Suffix == "u8x16"
	default:
		_, isBinary := simdBinaryOps[op]
		return op, shape, isBinary
	}
}

// simdScalarOps are the scalar mask operations of the catalog
// (docs/spec/93-simd.md section 1.2): trailing zeros with ctz(0) the width
// and population count, over the two mask widths. They have no vector
// shape, so they bypass simdOpSplit; the map is the closed set the call
// lowering accepts.
var simdScalarOps = map[string]bool{
	"ctz_u32": true, "ctz_u64": true, "popcount_u32": true, "popcount_u64": true,
}

// simdKnownMember reports whether member is any simd catalog operation the
// backend can lower: a shaped operation or a scalar mask operation.
func simdKnownMember(member string) bool {
	if simdScalarOps[member] || scalableMember(member) {
		return true
	}
	_, _, ok := simdOpSplit(member)
	return ok
}

// simdScalarHelperSource emits the helper for one scalar mask operation.
// AArch64 uses the instructions themselves (RBIT then CLZ for ctz; CNT
// and ADDV through NEON for popcount); elsewhere the C builtins, guarded
// so the zero word is total.
func simdScalarHelperSource(member string) string {
	elem := "u32"
	width, bits, builtin, reg := 32, 32, "", "%w"
	if strings.HasSuffix(member, "_u64") {
		elem, width, bits, reg = "u64", 64, 64, "%"
	}
	var b strings.Builder
	switch {
	case strings.HasPrefix(member, "ctz_"):
		if width == 32 {
			builtin = "__builtin_ctz"
		} else {
			builtin = "__builtin_ctzll"
		}
		fmt.Fprintf(&b, "static inline %s oak_simd_%s( %s x ) {\n", elem, member, elem)
		fmt.Fprintf(&b, "#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)\n")
		fmt.Fprintf(&b, "  %s r;\n  __asm__(\"rbit %s0, %s1\\n\\tclz %s0, %s0\" : \"=r\"(r) : \"r\"(x));\n  return r;\n", elem, reg, reg, reg, reg)
		fmt.Fprintf(&b, "#else\n  return x == 0u ? %du : (%s)%s(x);\n#endif\n}\n", bits, elem, builtin)
	case strings.HasPrefix(member, "popcount_"):
		if width == 32 {
			builtin = "__builtin_popcount"
		} else {
			builtin = "__builtin_popcountll"
		}
		fmt.Fprintf(&b, "static inline %s oak_simd_%s( %s x ) {\n", elem, member, elem)
		fmt.Fprintf(&b, "%s\n", neonGuard)
		if width == 32 {
			fmt.Fprintf(&b, "  return (u32)vaddv_u8(vcnt_u8(vcreate_u8((uint64_t)x)));\n")
		} else {
			fmt.Fprintf(&b, "  return (u64)vaddv_u8(vcnt_u8(vcreate_u8((uint64_t)x)));\n")
		}
		fmt.Fprintf(&b, "#else\n  return (%s)%s(x);\n#endif\n}\n", elem, builtin)
	default:
		return "OAK_UNSUPPORTED_SIMD_OP\n"
	}
	return b.String()
}

// simdQualifiedTypeSpelling resolves "simd.U8x16" to its C typedef name.
func simdQualifiedTypeSpelling(name string) (string, bool) {
	if !strings.HasPrefix(name, "simd.") {
		return "", false
	}
	member := strings.TrimPrefix(name, "simd.")
	for _, shape := range typechecker.SimdShapes {
		if shape.TypeName == member {
			return shape.Suffix, true
		}
	}
	switch member {
	case "Active":
		return "oak_active", true
	case "ScalableU8":
		return "oak_scalable_u8", true
	case "ScalableU32":
		return "oak_scalable_u32", true
	}
	return "OAK_UNSUPPORTED_SIMD_TYPE", true
}

// collectSimdUsage scans the program for simd operations, arm64 vector
// instruction functions, and simd type mentions, using the same walker as
// the scalar intrinsics. Missing coverage fails closed at the cc gate.
func (cg *CodeGenerator) collectSimdUsage(program *ast.Program) (ops []string, arm64Vector []string, typesMentioned bool) {
	opSet := map[string]bool{}
	vecSet := map[string]bool{}

	mentionsSimd := func(typeExpr ast.Expression) bool {
		ident, isIdent := typeExpr.(*ast.Identifier)
		return isIdent && strings.HasPrefix(ident.Value, "simd.")
	}
	for _, stmt := range program.Statements {
		if fn, isFn := stmt.(*ast.FunctionStatement); isFn {
			if fn.ReturnType != nil && mentionsSimd(fn.ReturnType) {
				typesMentioned = true
			}
			for _, param := range fn.Parameters {
				if mentionsSimd(param.Type) {
					typesMentioned = true
				}
			}
		}
	}

	scanCalls(program, func(library, member string) {
		switch library {
		case "simd":
			if simdKnownMember(member) {
				opSet[member] = true
			}
		case "arm64":
			if arm64VectorIntrinsicSources[member] != "" {
				vecSet[member] = true
			}
		}
	})

	for op := range opSet {
		ops = append(ops, op)
	}
	for vec := range vecSet {
		arm64Vector = append(arm64Vector, vec)
	}
	sort.Strings(ops)
	sort.Strings(arm64Vector)
	return ops, arm64Vector, typesMentioned
}

// emitSimdSupport emits the vector typedefs and one helper per used simd
// operation and arm64 vector instruction. Local declarations of vector
// types (with or without operations) also require the typedefs, so any
// simd usage at all emits them.
func (cg *CodeGenerator) emitSimdSupport(program *ast.Program) {
	ops, arm64Vector, typesMentioned := cg.collectSimdUsage(program)
	if len(ops) == 0 && len(arm64Vector) == 0 && !typesMentioned && !cg.programMentionsSimdLocals(program) {
		return
	}

	// Explicit architecture-vector calls must not silently become scalar on
	// an AArch64 target that disables NEON. Portable simd calls may fall back.
	if len(arm64Vector) != 0 {
		cg.write("#if defined(__aarch64__) && (!defined(__ARM_NEON) || defined(OAK_SCALAR_SIMD)) && !defined(OAK_PORTABLE_INTRINSICS)\n")
		cg.write("#error \"arm64 vector intrinsics require NEON\"\n")
		cg.write("#endif\n")
	}
	cg.write("/* portable SIMD vectors: docs/spec/93-simd.md */\n")
	cg.write("#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)\n")
	cg.write("#include <arm_neon.h>\n")
	cg.write("#endif\n")
	// The RISC-V Vector realization (docs/spec/93-simd.md section 1.4):
	// LMUL=1 intrinsics with the vector length fixed to the lane count, so
	// the fixed 128-bit vectors run unchanged on every VLEN >= 128.
	cg.write(rvvGuard + "\n#include <riscv_vector.h>\n#endif\n")
	// The SVE realization of the scalable API (docs/spec/93-simd.md
	// section 4): sizeless block-local values under a predicate derived from
	// the extent; the fixed 128-bit vectors stay with NEON.
	cg.write(sveGuard + "\n#include <arm_sve.h>\n#endif\n")
	for _, shape := range typechecker.SimdShapes {
		cg.write(fmt.Sprintf("typedef struct oak_%s { %s lanes[%d]; } %s;\n",
			shape.Suffix, shape.ElemName, shape.Lanes, shape.Suffix))
	}
	cg.write("\n")
	if len(cg.dispatchSlots) > 0 {
		cg.writeRaw(cg.dispatchProbeSource())
	}
	scalable := programUsesScalable(ops) || cg.programMentionsScalableLocals(program)
	if scalable {
		cg.writeRaw(scalableTypedefs)
		for _, mode := range cg.sortedDispatchModes() {
			cg.writeRaw(cg.dispatchModeTypedefs(mode))
		}
	}

	for _, member := range ops {
		if simdScalarOps[member] {
			cg.writeRaw(simdScalarHelperSource(member))
			cg.write("\n")
			continue
		}
		if scalableMember(member) {
			// Loads and stores go through the view and span structs; their
			// typedefs must precede the helper.
			elem := "u8"
			if strings.HasSuffix(member, "_u32") {
				elem = "u32"
			}
			if strings.HasPrefix(member, "load_") {
				cg.emitViewType(elem)
			}
			if strings.HasPrefix(member, "store_") {
				cg.emitSpanType(elem)
			}
			cg.writeRaw(scalableHelperSource(member))
			cg.write("\n")
			for _, mode := range cg.sortedDispatchModes() {
				// The mode's copy of the helper for the realizations
				// dispatched to it; where the baseline already is the
				// mode, or the target has no such feature, the copy is
				// the baseline helper under the mode's name.
				cg.writeRaw(fmt.Sprintf("#if %s\n%s#else\n#define oak_simd_%s%s oak_simd_%s\n#endif\n\n", cg.dispatchModeGate(mode), scalableHelperFor(member, mode), member, modeSuffix(mode), member))
			}
			continue
		}
		op, shape, ok := simdOpSplit(member)
		if !ok {
			continue
		}
		// Loads and stores go through the same view/span structs as scalar
		// element access; ensure their typedefs precede the helper.
		if op == "load" {
			cg.emitViewType(shape.ElemName)
		}
		if op == "store" {
			cg.emitSpanType(shape.ElemName)
		}
		var helper string
		if shape.Float {
			helper = simdFloatHelperSource(op, shape.Suffix, shape.ElemName, shape.Lanes)
		} else {
			helper = simdHelperSource(op, shape.Suffix, shape.ElemName, shape.Lanes)
		}
		cg.writeRaw(withRVV(helper, op, shape.ElemName, shape.Lanes, shape.Float))
		cg.write("\n")
	}
	for _, member := range arm64Vector {
		cg.writeRaw(arm64VectorIntrinsicSources[member])
		cg.write("\n")
	}
}

// programMentionsSimdLocals reports whether any local declaration names a
// simd type, which requires the typedefs even without operations.
func (cg *CodeGenerator) programMentionsSimdLocals(program *ast.Program) bool {
	found := false
	var scanStmt func(stmt ast.Statement)
	scanStmt = func(stmt ast.Statement) {
		switch s := stmt.(type) {
		case *ast.VariableDeclaration:
			if ident, isIdent := s.Type.(*ast.Identifier); isIdent && strings.HasPrefix(ident.Value, "simd.") {
				found = true
			}
		case *ast.FunctionStatement:
			if block, isBlock := s.Body.(*ast.BlockExpression); isBlock && block.Block != nil {
				for _, inner := range block.Block.Statements {
					scanStmt(inner)
				}
			}
		case *ast.WhileStatement:
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					scanStmt(inner)
				}
			}
		case *ast.IfStatement:
			if s.Consequence != nil {
				scanStmt(s.Consequence)
			}
			if s.Alternative != nil {
				scanStmt(s.Alternative)
			}
		case *ast.BlockStatement:
			for _, inner := range s.Statements {
				scanStmt(inner)
			}
		case *ast.UnsafeBlock:
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					scanStmt(inner)
				}
			}
		}
	}
	for _, stmt := range program.Statements {
		scanStmt(stmt)
	}
	return found
}

const neonGuard = "#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)"

// simdHelperSource builds the helper for one operation of one vector shape.
// Inputs come only from the fixed catalogs above.
func simdHelperSource(op, vec, elem string, lanes int) string {
	neon := elem // NEON intrinsic suffix matches the element name
	var b strings.Builder
	switch op {
	case "splat":
		fmt.Fprintf(&b, "static inline %s oak_simd_splat_%s( %s x ) {\n", vec, vec, elem)
		fmt.Fprintf(&b, "  %s r;\n%s\n", vec, neonGuard)
		fmt.Fprintf(&b, "  vst1q_%s(r.lanes, vdupq_n_%s(x));\n#else\n", neon, neon)
		fmt.Fprintf(&b, "  for (int i = 0; i < %d; i++) { r.lanes[i] = x; }\n#endif\n  return r;\n}\n", lanes)

	case "load":
		// The checked helper traps past the end; the `_proven` twin is emitted
		// only where the checker proved `off + L <= len` (Oak.Extents
		// vector_under_*), so it carries no check.
		for _, variant := range []string{"", "_proven"} {
			fmt.Fprintf(&b, "static inline %s oak_simd_load_%s%s( oak_view_%s v, u32 off ) {\n", vec, vec, variant, elem)
			if variant == "" {
				fmt.Fprintf(&b, "  if ((u64)off + %du > (u64)v.len) { __builtin_trap(); }\n", lanes)
			}
			fmt.Fprintf(&b, "  %s r;\n%s\n", vec, neonGuard)
			fmt.Fprintf(&b, "  vst1q_%s(r.lanes, vld1q_%s(v.base + off));\n#else\n", neon, neon)
			fmt.Fprintf(&b, "  for (int i = 0; i < %d; i++) { r.lanes[i] = v.base[off + (u32)i]; }\n#endif\n  return r;\n}\n", lanes)
		}

	case "store":
		for _, variant := range []string{"", "_proven"} {
			fmt.Fprintf(&b, "static inline void oak_simd_store_%s%s( oak_span_%s s, u32 off, %s val ) {\n", vec, variant, elem, vec)
			if variant == "" {
				fmt.Fprintf(&b, "  if ((u64)off + %du > (u64)s.len) { __builtin_trap(); }\n", lanes)
			}
			fmt.Fprintf(&b, "%s\n  vst1q_%s(s.base + off, vld1q_%s(val.lanes));\n#else\n", neonGuard, neon, neon)
			fmt.Fprintf(&b, "  for (int i = 0; i < %d; i++) { s.base[off + (u32)i] = val.lanes[i]; }\n#endif\n}\n", lanes)
		}

	case "shr":
		// Lane-wise logical shift right; a count reaching the lane width
		// traps (the scalar shift rule, docs/spec/10-syntax.md section 3b).
		// NEON's vshlq with a negative per-lane count shifts right; a
		// constant count folds to the immediate form.
		signed := map[string]string{"u8": "s8", "u16": "s16", "u32": "s32", "u64": "s64"}[elem]
		fmt.Fprintf(&b, "static inline %s oak_simd_shr_%s( %s v, u32 n ) {\n", vec, vec, vec)
		fmt.Fprintf(&b, "  if (n >= %du) { __builtin_trap(); }\n", laneBits(elem))
		fmt.Fprintf(&b, "  %s r;\n%s\n", vec, neonGuard)
		fmt.Fprintf(&b, "  vst1q_%s(r.lanes, vshlq_%s(vld1q_%s(v.lanes), vdupq_n_%s(-(int%d_t)n)));\n#else\n", neon, neon, neon, signed, laneBits(elem))
		fmt.Fprintf(&b, "  for (int i = 0; i < %d; i++) { r.lanes[i] = (%s)(v.lanes[i] >> n); }\n#endif\n  return r;\n}\n", lanes, elem)

	case "tbl":
		// Byte-table lookup: lane i is table[idx[i]] when idx[i] < 16, else
		// 0 — exactly NEON's vqtbl1q_u8 (and pshufb's high-bit rule).
		fmt.Fprintf(&b, "static inline %s oak_simd_tbl_%s( %s table, %s idx ) {\n", vec, vec, vec, vec)
		fmt.Fprintf(&b, "  %s r;\n%s\n", vec, neonGuard)
		fmt.Fprintf(&b, "  vst1q_u8(r.lanes, vqtbl1q_u8(vld1q_u8(table.lanes), vld1q_u8(idx.lanes)));\n#else\n")
		fmt.Fprintf(&b, "  for (int i = 0; i < 16; i++) { r.lanes[i] = idx.lanes[i] < 16 ? table.lanes[idx.lanes[i]] : (u8)0; }\n#endif\n  return r;\n}\n")

	case "prev":
		// Cross-block byte shift: the 16 bytes ending n before the end of
		// prev ++ cur, i.e. lane i is prev[16-n+i] for i < n and cur[i-n]
		// otherwise; n above 16 traps. NEON's vextq_u8 wants an immediate,
		// so the count selects among the seventeen forms; a constant count
		// leaves one.
		fmt.Fprintf(&b, "static inline %s oak_simd_prev_%s( %s prev, %s cur, u32 n ) {\n", vec, vec, vec, vec)
		fmt.Fprintf(&b, "  if (n > 16u) { __builtin_trap(); }\n")
		fmt.Fprintf(&b, "  %s r;\n%s\n", vec, neonGuard)
		fmt.Fprintf(&b, "  uint8x16_t p = vld1q_u8(prev.lanes), c = vld1q_u8(cur.lanes);\n  switch (n) {\n")
		for n := 0; n <= 16; n++ {
			if n == 0 {
				fmt.Fprintf(&b, "    case 0: vst1q_u8(r.lanes, c); break;\n")
			} else if n == 16 {
				fmt.Fprintf(&b, "    case 16: vst1q_u8(r.lanes, p); break;\n")
			} else {
				fmt.Fprintf(&b, "    case %d: vst1q_u8(r.lanes, vextq_u8(p, c, %d)); break;\n", n, 16-n)
			}
		}
		fmt.Fprintf(&b, "    default: __builtin_trap();\n  }\n#else\n")
		fmt.Fprintf(&b, "  for (int i = 0; i < 16; i++) { r.lanes[i] = (u32)i < n ? prev.lanes[16u - n + (u32)i] : cur.lanes[(u32)i - n]; }\n#endif\n  return r;\n}\n")

	case "movemask":
		// One bit per lane: bit i is the top bit of lane i (Oak.Simd.movemask).
		// NEON has no movemask: a test against the top bit gives all-ones
		// lanes, an and with a bit table gives each lane its bit, and the
		// lanes are summed — pairwise for sixteen bytes (two bytes of
		// result), horizontally for eight and four lanes, by extraction for
		// two. The cost is stated in docs/spec/93-simd.md section 1.2.
		fmt.Fprintf(&b, "static inline u32 oak_simd_movemask_%s( %s v ) {\n", vec, vec)
		fmt.Fprintf(&b, "%s\n", neonGuard)
		switch neon {
		case "u8":
			fmt.Fprintf(&b, "  static const uint8_t bits[16] = {1,2,4,8,16,32,64,128,1,2,4,8,16,32,64,128};\n")
			fmt.Fprintf(&b, "  uint8x16_t top = vtstq_u8(vld1q_u8(v.lanes), vdupq_n_u8(0x80));\n")
			fmt.Fprintf(&b, "  uint8x16_t m = vandq_u8(top, vld1q_u8(bits));\n")
			fmt.Fprintf(&b, "  m = vpaddq_u8(m, m); m = vpaddq_u8(m, m); m = vpaddq_u8(m, m);\n")
			fmt.Fprintf(&b, "  return (u32)vgetq_lane_u16(vreinterpretq_u16_u8(m), 0);\n")
		case "u16":
			fmt.Fprintf(&b, "  static const uint16_t bits[8] = {1,2,4,8,16,32,64,128};\n")
			fmt.Fprintf(&b, "  uint16x8_t top = vtstq_u16(vld1q_u16(v.lanes), vdupq_n_u16(0x8000));\n")
			fmt.Fprintf(&b, "  return (u32)vaddvq_u16(vandq_u16(top, vld1q_u16(bits)));\n")
		case "u32":
			fmt.Fprintf(&b, "  static const uint32_t bits[4] = {1,2,4,8};\n")
			fmt.Fprintf(&b, "  uint32x4_t top = vtstq_u32(vld1q_u32(v.lanes), vdupq_n_u32(0x80000000u));\n")
			fmt.Fprintf(&b, "  return (u32)vaddvq_u32(vandq_u32(top, vld1q_u32(bits)));\n")
		default:
			fmt.Fprintf(&b, "  uint64x2_t lv = vld1q_u64(v.lanes);\n")
			fmt.Fprintf(&b, "  return (u32)((vgetq_lane_u64(lv, 0) >> 63) | ((vgetq_lane_u64(lv, 1) >> 63) << 1));\n")
		}
		fmt.Fprintf(&b, "#else\n  u32 m = 0u;\n")
		fmt.Fprintf(&b, "  for (int i = 0; i < %d; i++) { if ((v.lanes[i] >> %d) & 1u) { m |= (1u << i); } }\n", lanes, laneBits(elem)-1)
		fmt.Fprintf(&b, "  return m;\n#endif\n}\n")

	case "any", "all":
		fmt.Fprintf(&b, "static inline Bool oak_simd_%s_%s( %s v ) {\n", op, vec, vec)
		fmt.Fprintf(&b, "%s\n", neonGuard)
		b.WriteString(neonReduction(op, vec, neon))
		fmt.Fprintf(&b, "#else\n")
		if op == "any" {
			fmt.Fprintf(&b, "  for (int i = 0; i < %d; i++) { if (v.lanes[i] != 0) { return oak_Bool_True; } }\n  return oak_Bool_False;\n", lanes)
		} else {
			fmt.Fprintf(&b, "  for (int i = 0; i < %d; i++) { if (v.lanes[i] == 0) { return oak_Bool_False; } }\n  return oak_Bool_True;\n", lanes)
		}
		fmt.Fprintf(&b, "#endif\n}\n")

	default: // binary lane-wise ops
		laneExpr, isBinary := simdBinaryOps[op]
		if !isBinary {
			return "OAK_UNSUPPORTED_SIMD_OP\n"
		}
		fmt.Fprintf(&b, "static inline %s oak_simd_%s_%s( %s a, %s b ) {\n", vec, op, vec, vec, vec)
		fmt.Fprintf(&b, "  %s r;\n%s\n", vec, neonGuard)
		b.WriteString(neonBinaryBody(op, neon))
		laneCode := laneExpr
		if strings.Contains(laneCode, "%") {
			laneCode = fmt.Sprintf(laneExpr, elem)
		}
		fmt.Fprintf(&b, "#else\n  for (int i = 0; i < %d; i++) {\n", lanes)
		fmt.Fprintf(&b, "    %s x = a.lanes[i]; %s y = b.lanes[i];\n", elem, elem)
		fmt.Fprintf(&b, "    r.lanes[i] = %s;\n  }\n#endif\n  return r;\n}\n", laneCode)
	}
	return b.String()
}

// neonBinaryBody emits the NEON branch of a binary op; 64-bit lane min/max
// have no instruction and lower to compare-and-select (docs/spec/93-simd.md
// section 1.4).
func neonBinaryBody(op, neon string) string {
	if neon == "u64" && (op == "min" || op == "max") {
		// Where a > b: min takes b, max takes a.
		onGreater, otherwise := "b", "a"
		if op == "max" {
			onGreater, otherwise = "a", "b"
		}
		return fmt.Sprintf("  vst1q_u64(r.lanes, vbslq_u64(vcgtq_u64(vld1q_u64(a.lanes), vld1q_u64(b.lanes)), vld1q_u64(%s.lanes), vld1q_u64(%s.lanes)));\n",
			onGreater, otherwise)
	}
	return fmt.Sprintf("  vst1q_%s(r.lanes, %s_%s(vld1q_%s(a.lanes), vld1q_%s(b.lanes)));\n",
		neon, neonBinary[op], neon, neon, neon)
}

// neonReduction emits the NEON branch of any/all. 64-bit lanes have no
// across-vector reduction instruction: any reinterprets to 32-bit lanes
// (some 64-bit lane nonzero iff some bit set), all extracts both lanes.
func neonReduction(op, vec, neon string) string {
	if neon == "u64" {
		if op == "any" {
			return "  return vmaxvq_u32(vreinterpretq_u32_u64(vld1q_u64(v.lanes))) != 0u ? oak_Bool_True : oak_Bool_False;\n"
		}
		return "  { uint64x2_t lv = vld1q_u64(v.lanes);\n    return (vgetq_lane_u64(lv, 0) != 0u && vgetq_lane_u64(lv, 1) != 0u) ? oak_Bool_True : oak_Bool_False; }\n"
	}
	if op == "any" {
		return fmt.Sprintf("  return vmaxvq_%s(vld1q_%s(v.lanes)) != 0u ? oak_Bool_True : oak_Bool_False;\n", neon, neon)
	}
	return fmt.Sprintf("  return vminvq_%s(vld1q_%s(v.lanes)) != 0u ? oak_Bool_True : oak_Bool_False;\n", neon, neon)
}

// arm64VectorIntrinsicSources are the horizontal vector instruction
// helpers (docs/spec/93-simd.md section 2).
var arm64VectorIntrinsicSources = map[string]string{
	"uaddlv_u8x16": `static inline u32 oak_arm64_uaddlv_u8x16( u8x16 x ) {
#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)
  return (u32)vaddlvq_u8(vld1q_u8(x.lanes));
#else
  u32 sum = 0;
  for (int i = 0; i < 16; i++) { sum += x.lanes[i]; }
  return sum;
#endif
}
`,
	"umaxv_u8x16": `static inline u8 oak_arm64_umaxv_u8x16( u8x16 x ) {
#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)
  return vmaxvq_u8(vld1q_u8(x.lanes));
#else
  u8 best = 0;
  for (int i = 0; i < 16; i++) { if (x.lanes[i] > best) { best = x.lanes[i]; } }
  return best;
#endif
}
`,
	"uminv_u8x16": `static inline u8 oak_arm64_uminv_u8x16( u8x16 x ) {
#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)
  return vminvq_u8(vld1q_u8(x.lanes));
#else
  u8 best = 255;
  for (int i = 0; i < 16; i++) { if (x.lanes[i] < best) { best = x.lanes[i]; } }
  return best;
#endif
}
`,
	"cnt_u8x16": `static inline u8x16 oak_arm64_cnt_u8x16( u8x16 x ) {
  u8x16 r;
#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)
  vst1q_u8(r.lanes, vcntq_u8(vld1q_u8(x.lanes)));
#else
  for (int i = 0; i < 16; i++) {
    u8 b = x.lanes[i];
    b = (u8)((b & 0x55u) + ((b >> 1) & 0x55u));
    b = (u8)((b & 0x33u) + ((b >> 2) & 0x33u));
    b = (u8)((b & 0x0Fu) + ((b >> 4) & 0x0Fu));
    r.lanes[i] = b;
  }
#endif
  return r;
}
`,
}

// simdFloatHelperSource builds the helper for one operation of a
// floating-point vector shape (docs/spec/20-types.md section 11.3.7). Every
// lane obeys the scalar rules: NEON vminq/vmaxq have the IEEE 754-2019
// minimum/maximum semantics (a NaN operand yields NaN, -0.0 below +0.0), the
// portable branch uses the float preamble's helpers; fma is one rounding
// per lane (vfmaq / fma); reduce_add is the explicit pairwise tree in both
// branches, so the grouping is identical on every target; lane indices of
// extract/insert are range-checked before any access.
func simdFloatHelperSource(op, vec, elem string, lanes int) string {
	neon := elem
	suffix := ""
	if elem == "f32" {
		suffix = "f"
	}
	var b strings.Builder
	switch op {
	case "splat":
		fmt.Fprintf(&b, "static inline %s oak_simd_splat_%s( %s x ) {\n", vec, vec, elem)
		fmt.Fprintf(&b, "  %s r;\n%s\n", vec, neonGuard)
		fmt.Fprintf(&b, "  vst1q_%s(r.lanes, vdupq_n_%s(x));\n#else\n", neon, neon)
		fmt.Fprintf(&b, "  for (int i = 0; i < %d; i++) { r.lanes[i] = x; }\n#endif\n  return r;\n}\n", lanes)
	case "load":
		// The checked helper traps past the end; the `_proven` twin is emitted
		// only where the checker proved `off + L <= len` (Oak.Extents
		// vector_under_*), so it carries no check.
		for _, variant := range []string{"", "_proven"} {
			fmt.Fprintf(&b, "static inline %s oak_simd_load_%s%s( oak_view_%s v, u32 off ) {\n", vec, vec, variant, elem)
			if variant == "" {
				fmt.Fprintf(&b, "  if ((u64)off + %du > (u64)v.len) { __builtin_trap(); }\n", lanes)
			}
			fmt.Fprintf(&b, "  %s r;\n%s\n", vec, neonGuard)
			fmt.Fprintf(&b, "  vst1q_%s(r.lanes, vld1q_%s(v.base + off));\n#else\n", neon, neon)
			fmt.Fprintf(&b, "  for (int i = 0; i < %d; i++) { r.lanes[i] = v.base[off + (u32)i]; }\n#endif\n  return r;\n}\n", lanes)
		}
	case "store":
		for _, variant := range []string{"", "_proven"} {
			fmt.Fprintf(&b, "static inline void oak_simd_store_%s%s( oak_span_%s s, u32 off, %s val ) {\n", vec, variant, elem, vec)
			if variant == "" {
				fmt.Fprintf(&b, "  if ((u64)off + %du > (u64)s.len) { __builtin_trap(); }\n", lanes)
			}
			fmt.Fprintf(&b, "%s\n  vst1q_%s(s.base + off, vld1q_%s(val.lanes));\n#else\n", neonGuard, neon, neon)
			fmt.Fprintf(&b, "  for (int i = 0; i < %d; i++) { s.base[off + (u32)i] = val.lanes[i]; }\n#endif\n}\n", lanes)
		}
	case "add", "sub", "mul", "div", "min", "max":
		neonName := map[string]string{"add": "vaddq", "sub": "vsubq", "mul": "vmulq", "div": "vdivq", "min": "vminq", "max": "vmaxq"}[op]
		lane := map[string]string{"add": "x + y", "sub": "x - y", "mul": "x * y", "div": "x / y",
			"min": "oak_fmin_" + elem + "(x, y)", "max": "oak_fmax_" + elem + "(x, y)"}[op]
		fmt.Fprintf(&b, "static inline %s oak_simd_%s_%s( %s a, %s b ) {\n", vec, op, vec, vec, vec)
		fmt.Fprintf(&b, "  %s r;\n%s\n", vec, neonGuard)
		fmt.Fprintf(&b, "  vst1q_%s(r.lanes, %s_%s(vld1q_%s(a.lanes), vld1q_%s(b.lanes)));\n#else\n", neon, neonName, neon, neon, neon)
		fmt.Fprintf(&b, "  for (int i = 0; i < %d; i++) { %s x = a.lanes[i]; %s y = b.lanes[i]; r.lanes[i] = %s; }\n#endif\n  return r;\n}\n", lanes, elem, elem, lane)
	case "sqrt", "neg", "abs":
		neonName := map[string]string{"sqrt": "vsqrtq", "neg": "vnegq", "abs": "vabsq"}[op]
		lane := map[string]string{"sqrt": "sqrt" + suffix + "(x)", "neg": "-x", "abs": "fabs" + suffix + "(x)"}[op]
		fmt.Fprintf(&b, "static inline %s oak_simd_%s_%s( %s a ) {\n", vec, op, vec, vec)
		fmt.Fprintf(&b, "  %s r;\n%s\n", vec, neonGuard)
		fmt.Fprintf(&b, "  vst1q_%s(r.lanes, %s_%s(vld1q_%s(a.lanes)));\n#else\n", neon, neonName, neon, neon)
		fmt.Fprintf(&b, "  for (int i = 0; i < %d; i++) { %s x = a.lanes[i]; r.lanes[i] = %s; }\n#endif\n  return r;\n}\n", lanes, elem, lane)
	case "fma":
		// vfmaq(c, a, b) is c + a*b in one rounding; the portable branch is
		// the correctly rounded C99 fma.
		fmt.Fprintf(&b, "static inline %s oak_simd_fma_%s( %s a, %s b, %s c ) {\n", vec, vec, vec, vec, vec)
		fmt.Fprintf(&b, "  %s r;\n%s\n", vec, neonGuard)
		fmt.Fprintf(&b, "  vst1q_%s(r.lanes, vfmaq_%s(vld1q_%s(c.lanes), vld1q_%s(a.lanes), vld1q_%s(b.lanes)));\n#else\n", neon, neon, neon, neon, neon)
		fmt.Fprintf(&b, "  for (int i = 0; i < %d; i++) { r.lanes[i] = fma%s(a.lanes[i], b.lanes[i], c.lanes[i]); }\n#endif\n  return r;\n}\n", lanes, suffix)
	case "extract":
		fmt.Fprintf(&b, "static inline %s oak_simd_extract_%s( %s v, u32 lane ) {\n", elem, vec, vec)
		fmt.Fprintf(&b, "  if (lane >= %du) { __builtin_trap(); }\n  return v.lanes[lane];\n}\n", lanes)
	case "insert":
		fmt.Fprintf(&b, "static inline %s oak_simd_insert_%s( %s v, u32 lane, %s x ) {\n", vec, vec, vec, elem)
		fmt.Fprintf(&b, "  if (lane >= %du) { __builtin_trap(); }\n  v.lanes[lane] = x;\n  return v;\n}\n", lanes)
	case "reduce_add":
		// The pairwise tree is the semantics (docs/spec/20-types.md section
		// 11.3.7, 55-parallelism.md section 4): identical on every target.
		fmt.Fprintf(&b, "static inline %s oak_simd_reduce_add_%s( %s v ) {\n", elem, vec, vec)
		if lanes == 4 {
			fmt.Fprintf(&b, "  return (v.lanes[0] + v.lanes[1]) + (v.lanes[2] + v.lanes[3]);\n}\n")
		} else {
			fmt.Fprintf(&b, "  return v.lanes[0] + v.lanes[1];\n}\n")
		}
	default:
		return "OAK_UNSUPPORTED_SIMD_OP\n"
	}
	return b.String()
}

// laneBits is the lane width in bits of an integer element type name.
func laneBits(elem string) int {
	switch elem {
	case "u8":
		return 8
	case "u16":
		return 16
	case "u32":
		return 32
	}
	return 64
}

// rvvGuard selects the RISC-V Vector realization: a RISC-V target whose
// processor has the V extension (`-cpu generic_rv64+v`), unless the
// portable lowering is forced. It is the third realization beside NEON and
// the portable lane loop; the choice is the preprocessor's, at build time.
const rvvGuard = "#if defined(__riscv) && defined(__riscv_vector) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)"

// scalableCompareOps are the comparisons of the scalable API that yield a
// two-valued mask (docs/spec/93-simd.md section 4.1): the portable lane
// expression, the RVV mask-producing compare, and the SVE predicate compare.
// Lanes are unsigned, so lt/gt are the unsigned orders.
var scalableCompareOps = map[string]struct{ lane, rvv, sve string }{
	"eq": {"(%[1]s)(x == y ? (%[1]s)~(%[1]s)0 : (%[1]s)0)", "vmseq", "svcmpeq"},
	"ne": {"(%[1]s)(x != y ? (%[1]s)~(%[1]s)0 : (%[1]s)0)", "vmsne", "svcmpne"},
	"lt": {"(%[1]s)(x < y ? (%[1]s)~(%[1]s)0 : (%[1]s)0)", "vmsltu", "svcmplt"},
	"gt": {"(%[1]s)(x > y ? (%[1]s)~(%[1]s)0 : (%[1]s)0)", "vmsgtu", "svcmpgt"},
}

// sveGuard selects the SVE realization of the scalable API: an AArch64
// target whose processor has SVE (`-cpu generic+sve`, `neoverse_v2`, …),
// unless the portable lowering is forced.
const sveGuard = "#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)"

// sveElifGuard is sveGuard as the second branch of a realization chain.
const sveElifGuard = "#elif defined(__aarch64__) && defined(__ARM_FEATURE_SVE) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)"

// withRVV splices the RISC-V Vector branch into a generated helper: the
// helper's `#else` (its portable branch) becomes `#elif <rvv> ... #else`.
// Operations without an RVV body — the reductions any/all/movemask/
// reduce_add, whose pairwise order is the specification, and the lane
// accessors — keep the portable code on every target.
func withRVV(helper, op, elem string, lanes int, float bool) string {
	body, ok := rvvBody(op, elem, lanes, float)
	if !ok {
		return helper
	}
	elif := strings.Replace(rvvGuard, "#if", "#elif", 1)
	return strings.ReplaceAll(helper, "\n#else\n", "\n"+elif+"\n"+body+"#else\n")
}

// rvvType and rvvSuffix spell the LMUL=1 vector type and intrinsic suffix
// of an element type: u8 -> vuint8m1_t / u8m1, f32 -> vfloat32m1_t / f32m1.
func rvvType(elem string) string {
	switch elem {
	case "f32":
		return "vfloat32m1_t"
	case "f64":
		return "vfloat64m1_t"
	}
	return "vuint" + elem[1:] + "m1_t"
}

func rvvSuffix(elem string) string { return elem + "m1" }

func rvvBits(elem string) string { return elem[1:] }

// rvvBody is the RVV branch of one helper, over the same lane-array
// variables the NEON branch uses (a, b, c, v, val, r, s, off, n, prev, cur,
// table, idx).
func rvvBody(op, elem string, lanes int, float bool) (string, bool) {
	t, sfx, bits := rvvType(elem), rvvSuffix(elem), rvvBits(elem)
	vl := fmt.Sprintf("%d", lanes)
	load := func(ptr string) string { return fmt.Sprintf("__riscv_vle%s_v_%s(%s, %s)", bits, sfx, ptr, vl) }
	store := func(ptr, value string) string {
		return fmt.Sprintf("  __riscv_vse%s_v_%s(%s, %s, %s);\n", bits, sfx, ptr, value, vl)
	}
	splat := func(x string) string {
		if float {
			return fmt.Sprintf("__riscv_vfmv_v_f_%s(%s, %s)", sfx, x, vl)
		}
		return fmt.Sprintf("__riscv_vmv_v_x_%s(%s, %s)", sfx, x, vl)
	}
	switch op {
	case "splat":
		return store("r.lanes", splat("x")), true
	case "load":
		return store("r.lanes", load("v.base + off")), true
	case "store":
		return store("s.base + off", load("val.lanes")), true
	case "shr":
		if float {
			return "", false
		}
		return store("r.lanes", fmt.Sprintf("__riscv_vsrl_vx_%s(%s, (size_t)n, %s)", sfx, load("v.lanes"), vl)), true
	case "tbl":
		// vrgather reads lane idx[i] of the table for idx[i] below VLMAX and
		// gives zero above it; VLMAX depends on VLEN, so the index < 16 rule
		// is applied explicitly and the result is the same on every VLEN.
		return fmt.Sprintf("  %s ix = %s;\n  vbool8_t in = __riscv_vmsltu_vx_u8m1_b8(ix, 16, %s);\n  %s g = __riscv_vrgather_vv_u8m1(%s, ix, %s);\n", t, load("idx.lanes"), vl, t, load("table.lanes"), vl) +
			store("r.lanes", fmt.Sprintf("__riscv_vmerge_vvm_u8m1(%s, g, in, %s)", splat("0"), vl)), true
	case "prev":
		// Lane i is prev[16-n+i] below n and cur[i-n] from n on: slide prev
		// down by 16-n, then slide cur up by n over it (undisturbed lanes
		// below n keep the slid prev).
		return fmt.Sprintf("  %s p = __riscv_vslidedown_vx_u8m1(%s, (size_t)(16u - n), %s);\n", t, load("prev.lanes"), vl) +
			store("r.lanes", fmt.Sprintf("__riscv_vslideup_vx_u8m1(p, %s, (size_t)n, %s)", load("cur.lanes"), vl)), true
	case "fma":
		// vfmacc(c, a, b) is c + a*b in one rounding, as vfmaq and fma().
		return store("r.lanes", fmt.Sprintf("__riscv_vfmacc_vv_%s(%s, %s, %s, %s)", sfx, load("c.lanes"), load("a.lanes"), load("b.lanes"), vl)), true
	case "sqrt", "neg", "abs":
		name := map[string]string{"sqrt": "vfsqrt_v", "neg": "vfneg_v", "abs": "vfabs_v"}[op]
		return store("r.lanes", fmt.Sprintf("__riscv_%s_%s(%s, %s)", name, sfx, load("a.lanes"), vl)), true
	case "eq":
		if float {
			return "", false
		}
		return fmt.Sprintf("  vbool%s_t m = __riscv_vmseq_vv_%s_b%s(%s, %s, %s);\n", bits, sfx, bits, load("a.lanes"), load("b.lanes"), vl) +
			store("r.lanes", fmt.Sprintf("__riscv_vmerge_vxm_%s(%s, (%s)~(%s)0, m, %s)", sfx, splat("0"), elem, elem, vl)), true
	}
	binary := map[string]string{"add": "vadd_vv", "sub": "vsub_vv", "subs": "vssubu_vv", "and": "vand_vv", "or": "vor_vv", "xor": "vxor_vv", "min": "vminu_vv", "max": "vmaxu_vv"}
	if float {
		// No RVV min/max: vfmin/vfmax are IEEE minimumNumber/maximumNumber
		// (a NaN operand is suppressed, -0.0 and +0.0 are equal), while the
		// catalog's min/max are IEEE 754-2019 minimum/maximum; the portable
		// lane loop stays the realization there.
		binary = map[string]string{"add": "vfadd_vv", "sub": "vfsub_vv", "mul": "vfmul_vv", "div": "vfdiv_vv"}
	}
	name, isBinary := binary[op]
	if !isBinary {
		return "", false
	}
	return store("r.lanes", fmt.Sprintf("__riscv_%s_%s(%s, %s, %s)", name, sfx, load("a.lanes"), load("b.lanes"), vl)), true
}

// ---- The scalable API (docs/spec/93-simd.md section 4) ----
//
// An active extent is chosen by the realization, never above the remaining
// count nor its capacity; every operation touches the active lanes only.
// Portable (and NEON) realization: one 16-byte vector as a struct and a
// u32 extent; RVV: the sizeless LMUL=1 vector types as block-local C
// values (the checker's locality rule, OAK-S0401, is what makes them
// sound) and a size_t extent from vsetvl.

func scalableMember(member string) bool {
	return member == "count" || strings.HasPrefix(member, "active_") || strings.Contains(member, "_active_")
}

func programUsesScalable(ops []string) bool {
	for _, member := range ops {
		if scalableMember(member) {
			return true
		}
	}
	return false
}

// programMentionsScalableLocals reports a local of a scalable type, which
// needs the typedefs even without operations.
func (cg *CodeGenerator) programMentionsScalableLocals(program *ast.Program) bool {
	found := false
	var visit func(value reflect.Value)
	visit = func(value reflect.Value) {
		if found || !value.IsValid() {
			return
		}
		switch value.Kind() {
		case reflect.Ptr, reflect.Interface:
			if value.IsNil() {
				return
			}
			if decl, ok := value.Interface().(*ast.VariableDeclaration); ok && decl.Type != nil {
				text := decl.Type.String()
				if strings.Contains(text, "simd.Active") || strings.Contains(text, "simd.Scalable") {
					found = true
					return
				}
			}
			if value.Kind() == reflect.Ptr {
				visit(value.Elem())
			} else {
				visit(reflect.ValueOf(value.Interface()))
			}
		case reflect.Struct:
			for i := 0; i < value.NumField(); i++ {
				if value.Type().Field(i).IsExported() {
					visit(value.Field(i))
				}
			}
		case reflect.Slice:
			for i := 0; i < value.Len(); i++ {
				visit(value.Index(i))
			}
		}
	}
	visit(reflect.ValueOf(program))
	return found
}

const scalableTypedefs = `/* scalable vectors (docs/spec/93-simd.md section 4): block-local values whose
   lanes outside the active extent are not Oak values */
` + rvvGuard + `
typedef size_t oak_active;
typedef vuint8m1_t oak_scalable_u8;
typedef vuint32m1_t oak_scalable_u32;
#define OAK_SCALABLE_CAP_U8(remaining) __riscv_vsetvl_e8m1((size_t)(remaining))
#define OAK_SCALABLE_CAP_U32(remaining) __riscv_vsetvl_e32m1((size_t)(remaining))
` + sveElifGuard + `
typedef uint32_t oak_active;
typedef svuint8_t oak_scalable_u8;
typedef svuint32_t oak_scalable_u32;
#define OAK_SCALABLE_CAP_U8(remaining) ((uint64_t)(remaining) < svcntb() ? (uint32_t)(remaining) : (uint32_t)svcntb())
#define OAK_SCALABLE_CAP_U32(remaining) ((uint64_t)(remaining) < svcntw() ? (uint32_t)(remaining) : (uint32_t)svcntw())
#define OAK_SVE_PG_U8(a) svwhilelt_b8((uint32_t)0, (uint32_t)(a))
#define OAK_SVE_PG_U32(a) svwhilelt_b32((uint32_t)0, (uint32_t)(a))
#else
typedef u32 oak_active;
typedef struct oak_scalable_u8 { u8 lanes[16]; } oak_scalable_u8;
typedef struct oak_scalable_u32 { u32 lanes[4]; } oak_scalable_u32;
#define OAK_SCALABLE_CAP_U8(remaining) ((remaining) < 16u ? (remaining) : 16u)
#define OAK_SCALABLE_CAP_U32(remaining) ((remaining) < 4u ? (remaining) : 4u)
#endif

`

// scalableHelperSource emits one scalable operation's helper: the portable
// lane loop over the extent, and the RVV intrinsic under the guard.
func scalableHelperSource(member string) string { return scalableHelperFor(member, "") }

// modeSuffix is the spelling a lowering mode appends to the scalable
// types and helpers of a realization emitted beside the baseline
// (docs/spec/93-simd.md section 6, one translation unit, two lowerings).
func modeSuffix(mode string) string {
	if mode == "" {
		return ""
	}
	return "__" + mode
}

// scalableHelperFor emits the helper in one lowering mode: "" is the
// baseline chain (RVV, SVE, portable under the preprocessor guards); "sve"
// or "rvv" is that realization's body alone, under the mode's names, for
// a dispatched program whose baseline lacks the feature.
func scalableHelperFor(member, mode string) string {
	text := scalableHelperChain(member, mode)
	if mode == "" {
		return text
	}
	// Cut the portable tail the chain left after the mode's branch.
	for {
		i := strings.Index(text, modeCut)
		if i < 0 {
			break
		}
		j := strings.Index(text[i:], "#endif\n")
		if j < 0 {
			break
		}
		text = text[:i] + text[i+j+len("#endif\n"):]
	}
	sfx := modeSuffix(mode)
	text = strings.ReplaceAll(text, "oak_simd_"+member+"(", "oak_simd_"+member+sfx+"(")
	text = strings.ReplaceAll(text, "oak_scalable_u8 ", "oak_scalable_u8"+sfx+" ")
	text = strings.ReplaceAll(text, "oak_scalable_u32 ", "oak_scalable_u32"+sfx+" ")
	text = strings.ReplaceAll(text, "OAK_SCALABLE_CAP_U8(", "OAK_SCALABLE_CAP_U8"+sfx+"(")
	text = strings.ReplaceAll(text, "OAK_SCALABLE_CAP_U32(", "OAK_SCALABLE_CAP_U32"+sfx+"(")
	attribute := ""
	for _, feature := range semir.CPUFeatures() {
		if feature.Mode == mode {
			attribute = feature.Attribute + " "
			break
		}
	}
	return strings.ReplaceAll(text, "static inline ", attribute+"static inline ")
}

// modeCut marks where a mode-only helper's text ends and the chain's
// portable tail begins.
const modeCut = "/*OAK_MODE_CUT*/"

func scalableHelperChain(member, mode string) string {
	var b strings.Builder
	if member == "count" {
		b.WriteString("static inline u32 oak_simd_count( oak_active a ) { return (u32)a; }\n")
		return b.String()
	}
	elem, cap := "u8", "OAK_SCALABLE_CAP_U8"
	if strings.HasSuffix(member, "_u32") {
		elem, cap = "u32", "OAK_SCALABLE_CAP_U32"
	}
	vec := "oak_scalable_" + elem
	bits := elem[1:]
	sfx := elem + "m1"
	if strings.HasPrefix(member, "active_") {
		fmt.Fprintf(&b, "static inline oak_active oak_simd_%s( u32 remaining ) { return (oak_active)%s(remaining); }\n", member, cap)
		return b.String()
	}
	op := member[:strings.Index(member, "_active_")]
	// The realization branches: RVV, then SVE, then the portable loop.
	pg := "OAK_SVE_PG_U8(a)"
	if elem == "u32" {
		pg = "OAK_SVE_PG_U32(a)"
	}
	rvv := func(rvvText, sveText string) string {
		switch mode {
		case "sve":
			return sveText + modeCut
		case "rvv":
			return rvvText + modeCut
		}
		return rvvGuard + "\n" + rvvText + sveElifGuard + "\n" + sveText + "#else\n"
	}
	load := func(ptr string) string { return fmt.Sprintf("__riscv_vle%s_v_%s(%s, a)", bits, sfx, ptr) }
	switch op {
	case "splat":
		fmt.Fprintf(&b, "static inline %s oak_simd_%s( %s x, oak_active a ) {\n", vec, member, elem)
		b.WriteString(rvv(fmt.Sprintf("  return __riscv_vmv_v_x_%s(x, a);\n", sfx), fmt.Sprintf("  (void)a; return svdup_n_%s(x);\n", elem)))
		fmt.Fprintf(&b, "  %s r;\n  for (u32 i = 0; i < a; i++) { r.lanes[i] = x; }\n  return r;\n#endif\n}\n", vec)
	case "load":
		fmt.Fprintf(&b, "static inline %s oak_simd_%s( oak_view_%s v, u32 off, oak_active a ) {\n", vec, member, elem)
		b.WriteString("  if ((u64)off + (u64)a > (u64)v.len) { __builtin_trap(); }\n")
		b.WriteString(rvv(fmt.Sprintf("  return %s;\n", load("v.base + off")), fmt.Sprintf("  return svld1_%s(%s, v.base + off);\n", elem, pg)))
		fmt.Fprintf(&b, "  %s r;\n  for (u32 i = 0; i < a; i++) { r.lanes[i] = v.base[off + i]; }\n  return r;\n#endif\n}\n", vec)
	case "store":
		fmt.Fprintf(&b, "static inline void oak_simd_%s( oak_span_%s s, u32 off, %s val, oak_active a ) {\n", member, elem, vec)
		b.WriteString("  if ((u64)off + (u64)a > (u64)s.len) { __builtin_trap(); }\n")
		b.WriteString(rvv(fmt.Sprintf("  __riscv_vse%s_v_%s(s.base + off, val, a);\n", bits, sfx), fmt.Sprintf("  svst1_%s(%s, s.base + off, val);\n", elem, pg)))
		b.WriteString("  for (u32 i = 0; i < a; i++) { s.base[off + i] = val.lanes[i]; }\n#endif\n}\n")
	case "shr":
		fmt.Fprintf(&b, "static inline %s oak_simd_%s( %s v, u32 n, oak_active a ) {\n", vec, member, vec)
		fmt.Fprintf(&b, "  if (n >= %su) { __builtin_trap(); }\n", bits)
		// The count is below the lane width here, so narrowing it to the
		// lane type for SVE's per-lane shift loses nothing.
		b.WriteString(rvv(fmt.Sprintf("  return __riscv_vsrl_vx_%s(v, (size_t)n, a);\n", sfx), fmt.Sprintf("  return svlsr_%s_z(%s, v, svdup_n_%s((%s)n));\n", elem, pg, elem, elem)))
		fmt.Fprintf(&b, "  %s r;\n  for (u32 i = 0; i < a; i++) { r.lanes[i] = (%s)(v.lanes[i] >> n); }\n  return r;\n#endif\n}\n", vec, elem)
	case "any", "all":
		fmt.Fprintf(&b, "static inline Bool oak_simd_%s( %s v, oak_active a ) {\n", member, vec)
		if op == "any" {
			b.WriteString(rvv(fmt.Sprintf("  return __riscv_vcpop_m_b%s(__riscv_vmsne_vx_%s_b%s(v, 0, a), a) != 0 ? oak_Bool_True : oak_Bool_False;\n", bits, sfx, bits), fmt.Sprintf("  { svbool_t pg = %s; return svptest_any(pg, svcmpne_n_%s(pg, v, 0)) ? oak_Bool_True : oak_Bool_False; }\n", pg, elem)))
			b.WriteString("  for (u32 i = 0; i < a; i++) { if (v.lanes[i] != 0) { return oak_Bool_True; } }\n  return oak_Bool_False;\n#endif\n}\n")
		} else {
			b.WriteString(rvv(fmt.Sprintf("  return __riscv_vcpop_m_b%s(__riscv_vmseq_vx_%s_b%s(v, 0, a), a) == 0 ? oak_Bool_True : oak_Bool_False;\n", bits, sfx, bits), fmt.Sprintf("  { svbool_t pg = %s; return svptest_any(pg, svcmpeq_n_%s(pg, v, 0)) ? oak_Bool_False : oak_Bool_True; }\n", pg, elem)))
			b.WriteString("  for (u32 i = 0; i < a; i++) { if (v.lanes[i] == 0) { return oak_Bool_False; } }\n  return oak_Bool_True;\n#endif\n}\n")
		}
	case "load_masked":
		// Predicated load (docs/spec/93-simd.md section 4.1): lanes under a
		// zero mask lane are not read and come back zero; the whole extent
		// still lies within the view, so no realization can fault.
		fmt.Fprintf(&b, "static inline %s oak_simd_%s( oak_view_%s v, u32 off, %s m, oak_active a ) {\n", vec, member, elem, vec)
		b.WriteString("  if ((u64)off + (u64)a > (u64)v.len) { __builtin_trap(); }\n")
		b.WriteString(rvv(fmt.Sprintf("  return __riscv_vle%s_v_%s_mu(__riscv_vmsne_vx_%s_b%s(m, 0, a), __riscv_vmv_v_x_%s(0, a), v.base + off, a);\n", bits, sfx, sfx, bits, sfx),
			fmt.Sprintf("  { svbool_t pg = %s; return svld1_%s(svcmpne_n_%s(pg, m, 0), v.base + off); }\n", pg, elem, elem)))
		fmt.Fprintf(&b, "  %s r;\n  for (u32 i = 0; i < a; i++) { r.lanes[i] = m.lanes[i] != 0 ? v.base[off + i] : (%s)0; }\n  return r;\n#endif\n}\n", vec, elem)
	case "store_masked":
		// Predicated store: only lanes under a nonzero mask lane are
		// written; the span keeps its other values.
		fmt.Fprintf(&b, "static inline void oak_simd_%s( oak_span_%s s, u32 off, %s m, %s val, oak_active a ) {\n", member, elem, vec, vec)
		b.WriteString("  if ((u64)off + (u64)a > (u64)s.len) { __builtin_trap(); }\n")
		b.WriteString(rvv(fmt.Sprintf("  __riscv_vse%s_v_%s_m(__riscv_vmsne_vx_%s_b%s(m, 0, a), s.base + off, val, a);\n", bits, sfx, sfx, bits),
			fmt.Sprintf("  { svbool_t pg = %s; svst1_%s(svcmpne_n_%s(pg, m, 0), s.base + off, val); }\n", pg, elem, elem)))
		b.WriteString("  for (u32 i = 0; i < a; i++) { if (m.lanes[i] != 0) { s.base[off + i] = val.lanes[i]; } }\n#endif\n}\n")
	case "select":
		fmt.Fprintf(&b, "static inline %s oak_simd_%s( %s m, %s x, %s y, oak_active a ) {\n", vec, member, vec, vec, vec)
		b.WriteString(rvv(fmt.Sprintf("  return __riscv_vmerge_vvm_%s(y, x, __riscv_vmsne_vx_%s_b%s(m, 0, a), a);\n", sfx, sfx, bits),
			fmt.Sprintf("  { svbool_t pg = %s; return svsel_%s(svcmpne_n_%s(pg, m, 0), x, y); }\n", pg, elem, elem)))
		fmt.Fprintf(&b, "  %s r;\n  for (u32 i = 0; i < a; i++) { r.lanes[i] = m.lanes[i] != 0 ? x.lanes[i] : y.lanes[i]; }\n  return r;\n#endif\n}\n", vec)
	case "count_nonzero":
		fmt.Fprintf(&b, "static inline u32 oak_simd_%s( %s m, oak_active a ) {\n", member, vec)
		b.WriteString(rvv(fmt.Sprintf("  return (u32)__riscv_vcpop_m_b%s(__riscv_vmsne_vx_%s_b%s(m, 0, a), a);\n", bits, sfx, bits),
			fmt.Sprintf("  { svbool_t pg = %s; return (u32)svcntp_b%s(pg, svcmpne_n_%s(pg, m, 0)); }\n", pg, bits, elem)))
		b.WriteString("  u32 n = 0;\n  for (u32 i = 0; i < a; i++) { n += m.lanes[i] != 0 ? 1u : 0u; }\n  return n;\n#endif\n}\n")
	case "reduce_add":
		// The wrapping sum is associative and commutative, so a tree
		// reduction is the lane-order sum exactly.
		fmt.Fprintf(&b, "static inline %s oak_simd_%s( %s v, oak_active a ) {\n", elem, member, vec)
		b.WriteString(rvv(fmt.Sprintf("  return __riscv_vmv_x_s_%s_%s(__riscv_vredsum_vs_%s_%s(v, __riscv_vmv_v_x_%s(0, 1), a));\n", sfx, elem+"", sfx, sfx, sfx), fmt.Sprintf("  return (%s)svaddv_%s(%s, v);\n", elem, elem, pg)))
		fmt.Fprintf(&b, "  %s sum = 0;\n  for (u32 i = 0; i < a; i++) { sum = (%s)(sum + v.lanes[i]); }\n  return sum;\n#endif\n}\n", elem, elem)
	default:
		laneExpr, isBinary := simdBinaryOps[op]
		if compare, isCompare := scalableCompareOps[op]; isCompare {
			laneExpr, isBinary = compare.lane, true
		}
		if !isBinary {
			return "OAK_UNSUPPORTED_SIMD_OP\n"
		}
		rvvName := map[string]string{"add": "vadd_vv", "sub": "vsub_vv", "subs": "vssubu_vv", "and": "vand_vv", "or": "vor_vv", "xor": "vxor_vv", "min": "vminu_vv", "max": "vmaxu_vv"}[op]
		fmt.Fprintf(&b, "static inline %s oak_simd_%s( %s a_, %s b_, oak_active a ) {\n", vec, member, vec, vec)
		if compare, isCompare := scalableCompareOps[op]; isCompare {
			// A comparison yields the two-valued mask: all-ones lanes where
			// it holds, zero lanes elsewhere.
			b.WriteString(rvv(fmt.Sprintf("  return __riscv_vmerge_vxm_%s(__riscv_vmv_v_x_%s(0, a), (%s)~(%s)0, __riscv_%s_vv_%s_b%s(a_, b_, a), a);\n", sfx, sfx, elem, elem, compare.rvv, sfx, bits), fmt.Sprintf("  { svbool_t pg = %s; return svdup_n_%s_z(%s_%s(pg, a_, b_), (%s)~(%s)0); }\n", pg, elem, compare.sve, elem, elem, elem)))
		} else {
			sveName := map[string]string{"add": "svadd", "sub": "svsub", "subs": "svqsub", "and": "svand", "or": "svorr", "xor": "sveor", "min": "svmin", "max": "svmax"}[op]
			sveText := fmt.Sprintf("  return %s_%s_z(%s, a_, b_);\n", sveName, elem, pg)
			if op == "subs" {
				// Saturating subtract is unpredicated in SVE; inactive lanes
				// are never read, so the unpredicated form is exact.
				sveText = fmt.Sprintf("  return svqsub_%s(a_, b_);\n", elem)
			}
			b.WriteString(rvv(fmt.Sprintf("  return __riscv_%s_%s(a_, b_, a);\n", rvvName, sfx), sveText))
		}
		laneCode := laneExpr
		if strings.Contains(laneCode, "%") {
			laneCode = fmt.Sprintf(laneExpr, elem)
		}
		fmt.Fprintf(&b, "  %s r;\n  for (u32 i = 0; i < a; i++) {\n    %s x = a_.lanes[i]; %s y = b_.lanes[i];\n    r.lanes[i] = %s;\n  }\n  return r;\n#endif\n}\n", vec, elem, elem, laneCode)
	}
	return b.String()
}
