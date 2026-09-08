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
	"add": "(%[1]s)(x + y)",
	"sub": "(%[1]s)(x - y)",
	"and": "(%[1]s)(x & y)",
	"or":  "(%[1]s)(x | y)",
	"xor": "(%[1]s)(x ^ y)",
	"min": "(x < y ? x : y)",
	"max": "(x > y ? x : y)",
	"eq":  "(%[1]s)(x == y ? (%[1]s)~(%[1]s)0 : (%[1]s)0)",
}

// neonBinary maps binary ops to their NEON intrinsic name stems. 64-bit
// lane min/max have no NEON instruction and use compare-and-select; they
// are handled specially.
var neonBinary = map[string]string{
	"add": "vaddq", "sub": "vsubq", "and": "vandq", "or": "vorrq",
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
	switch op {
	case "splat", "load", "store", "any", "all":
		return op, shape, true
	default:
		_, isBinary := simdBinaryOps[op]
		return op, shape, isBinary
	}
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
			if _, _, ok := simdOpSplit(member); ok {
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
		cg.write("#if defined(__aarch64__) && !defined(__ARM_NEON) && !defined(OAK_PORTABLE_INTRINSICS)\n")
		cg.write("#error \"arm64 vector intrinsics require NEON\"\n")
		cg.write("#endif\n")
	}
	cg.write("/* portable SIMD vectors: docs/spec/93-simd.md */\n")
	cg.write("#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_PORTABLE_INTRINSICS)\n")
	cg.write("#include <arm_neon.h>\n")
	cg.write("#endif\n")
	for _, shape := range typechecker.SimdShapes {
		cg.write(fmt.Sprintf("typedef struct oak_%s { %s lanes[%d]; } %s;\n",
			shape.Suffix, shape.ElemName, shape.Lanes, shape.Suffix))
	}
	cg.write("\n")

	for _, member := range ops {
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
		cg.writeRaw(simdHelperSource(op, shape.Suffix, shape.ElemName, shape.Lanes))
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

const neonGuard = "#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_PORTABLE_INTRINSICS)"

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
#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_PORTABLE_INTRINSICS)
  return (u32)vaddlvq_u8(vld1q_u8(x.lanes));
#else
  u32 sum = 0;
  for (int i = 0; i < 16; i++) { sum += x.lanes[i]; }
  return sum;
#endif
}
`,
	"umaxv_u8x16": `static inline u8 oak_arm64_umaxv_u8x16( u8x16 x ) {
#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_PORTABLE_INTRINSICS)
  return vmaxvq_u8(vld1q_u8(x.lanes));
#else
  u8 best = 0;
  for (int i = 0; i < 16; i++) { if (x.lanes[i] > best) { best = x.lanes[i]; } }
  return best;
#endif
}
`,
	"uminv_u8x16": `static inline u8 oak_arm64_uminv_u8x16( u8x16 x ) {
#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_PORTABLE_INTRINSICS)
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
#if defined(__aarch64__) && defined(__ARM_NEON) && !defined(OAK_PORTABLE_INTRINSICS)
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
