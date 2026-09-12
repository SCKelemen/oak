package codegen

// C backend lowering for the portable simd library and the arm64 vector
// instruction functions (docs/spec/93-simd.md). One struct ABI per vector
// type serves both lowerings; each used operation gets one static inline
// helper — NEON when the AArch64 target enables it, the portable C99 lane
// loop otherwise. All emitted names come from the fixed compiler catalog;
// no user-controlled strings reach the generated C.

import (
	"fmt"
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
	if simdScalarOps[member] {
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
	for _, shape := range typechecker.SimdShapes {
		cg.write(fmt.Sprintf("typedef struct oak_%s { %s lanes[%d]; } %s;\n",
			shape.Suffix, shape.ElemName, shape.Lanes, shape.Suffix))
	}
	cg.write("\n")

	for _, member := range ops {
		if simdScalarOps[member] {
			cg.writeRaw(simdScalarHelperSource(member))
			cg.write("\n")
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
		if shape.Float {
			cg.writeRaw(simdFloatHelperSource(op, shape.Suffix, shape.ElemName, shape.Lanes))
		} else {
			cg.writeRaw(simdHelperSource(op, shape.Suffix, shape.ElemName, shape.Lanes))
		}
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
		fmt.Fprintf(&b, "static inline %s oak_simd_load_%s( oak_view_%s v, u32 off ) {\n", vec, vec, elem)
		fmt.Fprintf(&b, "  if ((u64)off + %du > (u64)v.len) { __builtin_trap(); }\n", lanes)
		fmt.Fprintf(&b, "  %s r;\n%s\n", vec, neonGuard)
		fmt.Fprintf(&b, "  vst1q_%s(r.lanes, vld1q_%s(v.base + off));\n#else\n", neon, neon)
		fmt.Fprintf(&b, "  for (int i = 0; i < %d; i++) { r.lanes[i] = v.base[off + (u32)i]; }\n#endif\n  return r;\n}\n", lanes)

	case "store":
		fmt.Fprintf(&b, "static inline void oak_simd_store_%s( oak_span_%s s, u32 off, %s val ) {\n", vec, elem, vec)
		fmt.Fprintf(&b, "  if ((u64)off + %du > (u64)s.len) { __builtin_trap(); }\n", lanes)
		fmt.Fprintf(&b, "%s\n  vst1q_%s(s.base + off, vld1q_%s(val.lanes));\n#else\n", neonGuard, neon, neon)
		fmt.Fprintf(&b, "  for (int i = 0; i < %d; i++) { s.base[off + (u32)i] = val.lanes[i]; }\n#endif\n}\n", lanes)

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
		fmt.Fprintf(&b, "static inline %s oak_simd_load_%s( oak_view_%s v, u32 off ) {\n", vec, vec, elem)
		fmt.Fprintf(&b, "  if ((u64)off + %du > (u64)v.len) { __builtin_trap(); }\n", lanes)
		fmt.Fprintf(&b, "  %s r;\n%s\n", vec, neonGuard)
		fmt.Fprintf(&b, "  vst1q_%s(r.lanes, vld1q_%s(v.base + off));\n#else\n", neon, neon)
		fmt.Fprintf(&b, "  for (int i = 0; i < %d; i++) { r.lanes[i] = v.base[off + (u32)i]; }\n#endif\n  return r;\n}\n", lanes)
	case "store":
		fmt.Fprintf(&b, "static inline void oak_simd_store_%s( oak_span_%s s, u32 off, %s val ) {\n", vec, elem, vec)
		fmt.Fprintf(&b, "  if ((u64)off + %du > (u64)s.len) { __builtin_trap(); }\n", lanes)
		fmt.Fprintf(&b, "%s\n  vst1q_%s(s.base + off, vld1q_%s(val.lanes));\n#else\n", neonGuard, neon, neon)
		fmt.Fprintf(&b, "  for (int i = 0; i < %d; i++) { s.base[off + (u32)i] = val.lanes[i]; }\n#endif\n}\n", lanes)
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
