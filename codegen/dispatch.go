package codegen

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/semir"
)

// Processor-feature dispatch (docs/spec/93-simd.md section 6;
// docs/notes/cpu-dispatch-design-2026-09.md). A dispatched function
// selects a realization once per process: the probe runs before main into
// one word, and every call is a branch on that word — no function pointer,
// no per-call decision. A feature the build baseline guarantees selects
// its realization outright (the static rule).

// dispatchArchCondition is the preprocessor test for a feature's
// architecture: the emitted C is the same for every target, so a slot for
// another architecture is inert under the preprocessor.
func dispatchArchCondition(arch string) string {
	switch arch {
	case "riscv64":
		return "defined(__riscv) && (__riscv_xlen == 64)"
	default:
		return "defined(__aarch64__)"
	}
}

// dispatchMacro is the C macro that is 1 when the program can dispatch to
// the feature at run time: its architecture, the baseline lacks it, and the
// toolchain can compile its realization.
func dispatchMacro(feature semir.CPUFeature) string {
	return "OAK_DISPATCH_" + strings.ToUpper(feature.Name)
}

// dispatchProbeSource emits the availability macros, the feature word, the
// probe for each target, and oak_cpu_init.
func (cg *CodeGenerator) dispatchProbeSource() string {
	var b strings.Builder
	b.WriteString("/* processor-feature dispatch (docs/spec/93-simd.md section 6): one probe before\n   main into one word; a feature the baseline guarantees is selected statically */\n")
	for _, feature := range semir.CPUFeatures() {
		fmt.Fprintf(&b, "#define %s (1ull << %d)\n", feature.Macro(), feature.Bit)
		fmt.Fprintf(&b, "#if (%s) && defined(%s)\n#define %s 0 /* the baseline guarantees %s */\n", dispatchArchCondition(feature.Arch), feature.BaselineMacro, dispatchMacro(feature), feature.Name)
		fmt.Fprintf(&b, "#elif (%s) && !defined(OAK_SCALAR_SIMD) && !defined(OAK_PORTABLE_INTRINSICS)\n#define %s 1\n#else\n#define %s 0\n#endif\n", dispatchArchCondition(feature.Arch), dispatchMacro(feature), dispatchMacro(feature))
	}
	b.WriteString(`static u64 oak_cpu_features = 0;
#if defined(__aarch64__) && defined(__linux__)
#include <sys/auxv.h>
/* AT_HWCAP 16: HWCAP_SVE bit 22; AT_HWCAP2 26: HWCAP2_SVE2 bit 1 */
static u64 oak_cpu_probe(void) {
  unsigned long hwcap = getauxval(16), hwcap2 = getauxval(26);
  u64 f = 0;
  if (hwcap & (1ul << 22)) { f |= OAK_CPU_SVE; }
  if (hwcap2 & (1ul << 1)) { f |= OAK_CPU_SVE2; }
  if (hwcap & (1ul << 7)) { f |= OAK_CPU_CRC; }   /* HWCAP_CRC32 */
  if (hwcap & (1ul << 6)) { f |= OAK_CPU_SHA2; }  /* HWCAP_SHA2 */
  return f;
}
#elif defined(__aarch64__) && defined(__APPLE__)
/* declared here rather than through <sys/sysctl.h>, which a strict -std=c11
   SDK may hide behind _DARWIN_C_SOURCE (the dbs pilot's B9) */
extern int sysctlbyname(const char *name, void *oldp, size_t *oldlenp, void *newp, size_t newlen);
static u64 oak_cpu_probe(void) {
  int v = 0; size_t n = sizeof v; u64 f = 0;
  if (sysctlbyname("hw.optional.arm.FEAT_SVE", &v, &n, 0, 0) == 0 && v != 0) { f |= OAK_CPU_SVE; }
  v = 0; n = sizeof v;
  if (sysctlbyname("hw.optional.arm.FEAT_SVE2", &v, &n, 0, 0) == 0 && v != 0) { f |= OAK_CPU_SVE2; }
  v = 0; n = sizeof v;
  if (sysctlbyname("hw.optional.armv8_crc32", &v, &n, 0, 0) == 0 && v != 0) { f |= OAK_CPU_CRC; }
  v = 0; n = sizeof v;
  if (sysctlbyname("hw.optional.arm.FEAT_SHA256", &v, &n, 0, 0) == 0 && v != 0) { f |= OAK_CPU_SHA2; }
  return f;
}
#elif defined(__aarch64__)
/* freestanding: ID_AA64PFR0_EL1.SVE [35:32], ID_AA64ZFR0_EL1.SVEver [3:0] (S3_0_C0_C4_4),
   ID_AA64ISAR0_EL1.CRC32 [19:16] and .SHA2 [15:12]; EL1 or higher */
static u64 oak_cpu_probe(void) {
  u64 pfr0, isar0, f = 0;
  __asm__ volatile("mrs %0, ID_AA64ISAR0_EL1" : "=r"(isar0));
  if ((isar0 >> 16) & 0xfu) { f |= OAK_CPU_CRC; }
  if ((isar0 >> 12) & 0xfu) { f |= OAK_CPU_SHA2; }
  __asm__ volatile("mrs %0, ID_AA64PFR0_EL1" : "=r"(pfr0));
  if ((pfr0 >> 32) & 0xfu) {
    u64 zfr0;
    f |= OAK_CPU_SVE;
    __asm__ volatile("mrs %0, S3_0_C0_C4_4" : "=r"(zfr0));
    if (zfr0 & 0xfu) { f |= OAK_CPU_SVE2; }
  }
  return f;
}
#elif defined(__riscv) && defined(__linux__)
#include <unistd.h>
#include <sys/syscall.h>
/* riscv_hwprobe (syscall 258): key RISCV_HWPROBE_KEY_IMA_EXT_0 (4), bit RISCV_HWPROBE_IMA_V (1 << 2) */
struct oak_riscv_hwprobe { long long key; unsigned long long value; };
static u64 oak_cpu_probe(void) {
  struct oak_riscv_hwprobe pair = { 4, 0 };
  u64 f = 0;
  if (syscall(258, &pair, (size_t)1, (size_t)0, (void *)0, 0u) == 0 && (pair.value & 4u)) { f |= OAK_CPU_RVV; }
  return f;
}
#else
static u64 oak_cpu_probe(void) { return 0; }
#endif
/* exported: a C host without an Oak main calls it once before any dispatched call */
void oak_cpu_init(void) { oak_cpu_features = oak_cpu_probe(); }
#ifdef OAK_CHECK_DISPATCH
/* under oak test a checkable realization's result is compared with the meaning's
   (docs/spec/93-simd.md section 6.2); the harness records dispatch:<function>:<feature> */
extern void oak_test_host_dispatch_divergence(const char *function, const char *feature);
#define oak_dispatch_divergence(f, x) oak_test_host_dispatch_divergence((f), (x))
#endif
#if __STDC_HOSTED__ && !defined(OAK_FREESTANDING)
__attribute__((constructor)) static void oak_cpu_init_constructor(void) { oak_cpu_init(); }
#endif

`)
	return b.String()
}

// sortedDispatchModes lists the lowering modes the program's realizations
// need, in a fixed order.
func (cg *CodeGenerator) sortedDispatchModes() []string {
	modes := make([]string, 0, len(cg.dispatchModes))
	for mode := range cg.dispatchModes {
		modes = append(modes, mode)
	}
	sort.Strings(modes)
	return modes
}

// dispatchModeGate is the preprocessor expression under which a mode's
// helper copies are the feature's own lowering: some feature of the mode
// is dispatchable at run time.
func (cg *CodeGenerator) dispatchModeGate(mode string) string {
	terms := []string{}
	for _, feature := range semir.CPUFeatures() {
		if feature.Mode == mode {
			terms = append(terms, dispatchMacro(feature))
		}
	}
	if len(terms) == 0 {
		return "0"
	}
	return strings.Join(terms, " || ")
}

// dispatchModeTypedefs emits a mode's scalable types and capacity macros
// beside the baseline's (docs/spec/93-simd.md section 6, one translation
// unit, two lowerings). Where the mode is dispatchable, they are the
// feature's sizeless types under the feature header; elsewhere — the
// baseline already is the mode, or the target lacks the feature — they
// alias the baseline's, and a missing header turns the mode off.
func (cg *CodeGenerator) dispatchModeTypedefs(mode string) string {
	gate := cg.dispatchModeGate(mode)
	sfx := modeSuffix(mode)
	var b strings.Builder
	fmt.Fprintf(&b, "/* the %s lowering beside the baseline, for the realizations dispatched to it */\n#if %s\n", mode, gate)
	switch mode {
	case "sve":
		b.WriteString("#if defined(__has_include)\n#if __has_include(<arm_sve.h>)\n#include <arm_sve.h>\n#define OAK_DISPATCH_MODE_SVE 1\n#endif\n#endif\n")
		b.WriteString("#ifdef OAK_DISPATCH_MODE_SVE\n")
		fmt.Fprintf(&b, "typedef svuint8_t oak_scalable_u8%s;\ntypedef svuint32_t oak_scalable_u32%s;\n", sfx, sfx)
		fmt.Fprintf(&b, "#define OAK_SCALABLE_CAP_U8%s(remaining) ((uint64_t)(remaining) < svcntb() ? (uint32_t)(remaining) : (uint32_t)svcntb())\n", sfx)
		fmt.Fprintf(&b, "#define OAK_SCALABLE_CAP_U32%s(remaining) ((uint64_t)(remaining) < svcntw() ? (uint32_t)(remaining) : (uint32_t)svcntw())\n", sfx)
		b.WriteString("#ifndef OAK_SVE_PG_U8\n#define OAK_SVE_PG_U8(a) svwhilelt_b8((uint32_t)0, (uint32_t)(a))\n#define OAK_SVE_PG_U32(a) svwhilelt_b32((uint32_t)0, (uint32_t)(a))\n#endif\n")
		b.WriteString("#else\n/* no <arm_sve.h>: the sve slots are inert */\n#undef OAK_DISPATCH_SVE\n#define OAK_DISPATCH_SVE 0\n#undef OAK_DISPATCH_SVE2\n#define OAK_DISPATCH_SVE2 0\n")
		fmt.Fprintf(&b, "typedef oak_scalable_u8 oak_scalable_u8%s;\ntypedef oak_scalable_u32 oak_scalable_u32%s;\n#define OAK_SCALABLE_CAP_U8%s OAK_SCALABLE_CAP_U8\n#define OAK_SCALABLE_CAP_U32%s OAK_SCALABLE_CAP_U32\n#endif\n", sfx, sfx, sfx, sfx)
	case "rvv":
		b.WriteString("#if defined(__has_include)\n#if __has_include(<riscv_vector.h>)\n#include <riscv_vector.h>\n#define OAK_DISPATCH_MODE_RVV 1\n#endif\n#endif\n")
		b.WriteString("#ifdef OAK_DISPATCH_MODE_RVV\n")
		fmt.Fprintf(&b, "typedef vuint8m1_t oak_scalable_u8%s;\ntypedef vuint32m1_t oak_scalable_u32%s;\n", sfx, sfx)
		fmt.Fprintf(&b, "#define OAK_SCALABLE_CAP_U8%s(remaining) ((u32)__riscv_vsetvl_e8m1((size_t)(remaining)))\n#define OAK_SCALABLE_CAP_U32%s(remaining) ((u32)__riscv_vsetvl_e32m1((size_t)(remaining)))\n", sfx, sfx)
		b.WriteString("#else\n/* no <riscv_vector.h>: the rvv slots are inert */\n#undef OAK_DISPATCH_RVV\n#define OAK_DISPATCH_RVV 0\n")
		fmt.Fprintf(&b, "typedef oak_scalable_u8 oak_scalable_u8%s;\ntypedef oak_scalable_u32 oak_scalable_u32%s;\n#define OAK_SCALABLE_CAP_U8%s OAK_SCALABLE_CAP_U8\n#define OAK_SCALABLE_CAP_U32%s OAK_SCALABLE_CAP_U32\n#endif\n", sfx, sfx, sfx, sfx)
	}
	fmt.Fprintf(&b, "#else\ntypedef oak_scalable_u8 oak_scalable_u8%s;\ntypedef oak_scalable_u32 oak_scalable_u32%s;\n#define OAK_SCALABLE_CAP_U8%s OAK_SCALABLE_CAP_U8\n#define OAK_SCALABLE_CAP_U32%s OAK_SCALABLE_CAP_U32\n#endif\n\n", sfx, sfx, sfx, sfx)
	return b.String()
}

// dispatchParameterList spells a function's C parameter list and argument
// list as the function emitter does.
func (cg *CodeGenerator) dispatchParameterList(fn *ast.FunctionStatement) (params string, args string, spans bool) {
	parts, names := []string{}, []string{}
	for _, param := range fn.Parameters {
		if param.Variadic {
			parts = append(parts, cg.emitViewType(cg.parseTypeExpression(param.Type))+" "+cIdent(param.Name.Value))
		} else {
			parts = append(parts, cg.cParameter(param.Type, param.Name.Value))
		}
		if strings.HasPrefix(cg.parseTypeExpression(param.Type), "oak_span_") {
			spans = true
		}
		names = append(names, cIdent(param.Name.Value))
	}
	params = strings.Join(parts, ", ")
	if params == "" {
		params = "void"
	}
	return params, strings.Join(names, ", "), spans
}

// dispatchCheckable reports whether a dispatched function's claim is
// checked under oak test (docs/spec/93-simd.md section 6.2): a pure shape
// — a fixed-width integer or Bool result and no span parameter — so the
// realization and the meaning can both run on the same arguments and be
// compared.
func dispatchCheckable(returnType string, spans bool) bool {
	if spans {
		return false
	}
	switch returnType {
	case "u8", "u16", "u32", "u64", "u128", "i8", "i16", "i32", "i64", "Bool", "int", "uint":
		return true
	}
	return false
}

// emitDispatchWrapper emits the public function of a dispatched
// declaration after its meaning (docs/spec/93-simd.md section 6.1): per
// slot, in clause order, the realization outright where the baseline
// guarantees the feature (the static rule), else under one branch on the
// probed word; then the meaning. Under oak test (OAK_CHECK_DISPATCH) a
// checkable function runs both and reports a disagreement as the
// correctness failure `dispatch:<function>:<feature>` (section 6.2).
func (cg *CodeGenerator) emitDispatchWrapper(fn *ast.FunctionStatement, slots []*ast.DispatchSlot, publicName, meaningName string) {
	returnType := "void"
	if fn.ReturnType != nil {
		returnType = cg.parseTypeExpression(fn.ReturnType)
	}
	params, args, spans := cg.dispatchParameterList(fn)
	checkable := dispatchCheckable(returnType, spans)
	cg.write(fmt.Sprintf("%s%s %s( %s ) {\n", cg.linkage(fn.Name.Value), returnType, publicName, params))
	meaning := fmt.Sprintf("%s( %s )", meaningName, args)
	for _, slot := range slots {
		feature, known := semir.LookupCPUFeature(slot.Feature)
		if !known {
			continue
		}
		call := fmt.Sprintf("%s( %s )", cg.cFunctionName(slot.Realization), args)
		var transfer string
		if returnType == "void" {
			transfer = fmt.Sprintf("%s; return;", call)
		} else if checkable {
			transfer = fmt.Sprintf("\n#ifdef OAK_CHECK_DISPATCH\n    { %s oak_claimed = %s; %s oak_meant = %s; if (!( oak_claimed == oak_meant )) { oak_dispatch_divergence( %q, %q ); } return oak_claimed; }\n#else\n    return %s;\n#endif\n  ",
				returnType, call, returnType, meaning, fn.Name.Value, feature.Name, call)
		} else {
			transfer = fmt.Sprintf("return %s;", call)
		}
		arch := dispatchArchCondition(feature.Arch)
		// Under the portable lowering (-DOAK_PORTABLE_INTRINSICS) nothing
		// dispatches: the realizations are not compiled, the meaning runs.
		cg.write(fmt.Sprintf("#if (%s) && defined(%s) && !defined(OAK_PORTABLE_INTRINSICS) && !defined(OAK_SCALAR_SIMD)\n", arch, feature.BaselineMacro))
		cg.write(fmt.Sprintf("  { %s } /* the baseline guarantees %s */\n", transfer, feature.Name))
		cg.write(fmt.Sprintf("#elif (%s) && %s\n", arch, dispatchMacro(feature)))
		cg.write(fmt.Sprintf("  if (oak_cpu_features & %s) { %s }\n", feature.Macro(), transfer))
		cg.write("#endif\n")
	}
	if returnType == "void" {
		cg.write(fmt.Sprintf("  %s;\n", meaning))
	} else {
		cg.write(fmt.Sprintf("  return %s;\n", meaning))
	}
	cg.write("}\n\n")
}
