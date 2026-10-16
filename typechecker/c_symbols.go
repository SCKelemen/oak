package typechecker

import (
	"strconv"
	"strings"

	"github.com/SCKelemen/oak/modules"
)

// CFunctionSymbol is shared by C declarations, calls, native relocations,
// headers and implicit-export validation. Preserve the established ABI unless
// its spelling belongs to a runtime/generated family. Escapes encode the
// package and name separately, so e.g. root add_u32 and package add's u32
// cannot alias. Empty/main are the same root package, as in the legacy ABI.
//
// The zero-prefixed family cannot be a source identifier or the nonzero
// receiver-length prefix of a method. Reserving it below also protects it
// from explicit ABI names and compiler-internal input spellings.
func CFunctionSymbol(packageName, name string) string {
	if packageName == "main" {
		packageName = ""
	}
	legacy := "oak_" + name
	if packageName != "" {
		legacy = "oak_" + packageName + "_" + name
	}
	if !ReservedCRuntimeSymbol(legacy) && ValidCSymbol(legacy) {
		return legacy
	}
	pkg := modules.Escape(packageName)
	return "oak_0f_p" + strconv.Itoa(len(pkg)) + "_" + pkg + "_n" + modules.Escape(name)
}

// SetCPackageName supplies the compilation option to ABI validation. A package
// declaration in the checked program overrides it, just as it does in codegen.
func (tc *TypeChecker) SetCPackageName(name string) { tc.cPackageName = name }

// ReservedCRuntimeSymbol describes the C emitter's fixed runtime names and
// generated helper/type families. Reserve a whole parameterized family rather
// than listing only the carriers emitted by one program. New runtime families
// must be added here before they are introduced in the emitter.
func ReservedCRuntimeSymbol(symbol string) bool {
	switch symbol {
	case "oak_active", "oak_assert", "oak_bounds_trap", "oak_fn_at",
		"oak_index", "oak_is_valid_utf8", "oak_lv_idx", "oak_never",
		"oak_overflow_trap", "oak_report", "oak_store", "oak_string",
		"oak_Bool", "oak_Comparison":
		return true
	}
	for _, prefix := range []string{
		"oak_0f_", "oak_0g_", "oak__", "oak_id_",
		"oak_add_", "oak_sub_", "oak_neg_", "oak_mul_", "oak_div_", "oak_rem_",
		"oak_pun_", "oak_shl_", "oak_shr_", "oak_arith_", "oak_conv_",
		"oak_arm64_", "oak_simd_", "oak_scalable_", "oak_atomic_lock_free_",
		"oak_arr_", "oak_view_", "oak_span_", "oak_eq_", "oak_refine_",
		"oak_assert_eq_", "oak_assert_ne_", "oak_Bool_", "oak_Comparison_",
		"oak_argv_", "oak_cstr_", "oak_str_", "oak_byte_pack_",
		"oak_f16_", "oak_bf16_", "oak_f8e4m3_", "oak_f8e5m2_", "oak_widen_",
		"oak_fmin_", "oak_fmax_", "oak_total_key_", "oak_total_order_",
		"oak_cpu_", "oak_riscv_", "oak_dispatch_", "oak_host_", "oak_test_host_",
		"oak_measured_", "oak_const_", "oak_extern_", "oak_field_", "oak_tramp_",
		"oak_layout_", "oak_union_layout_", "oak_static_assert_",
	} {
		if strings.HasPrefix(symbol, prefix) {
			return true
		}
	}
	// Native addressed globals carry their package prefix before this tag.
	return strings.HasPrefix(symbol, "oak_") && strings.Contains(symbol, "_0g_")
}

// ReservedCABI protects explicit exports as well as the non-oak_ runtime
// preprocessor/internal families. Explicit ABI names are never renamed.
func ReservedCABI(symbol string) bool {
	return ReservedCRuntimeSymbol(symbol) || strings.HasPrefix(symbol, "__oak_") ||
		strings.HasPrefix(symbol, "OAK_") || symbol == "core_slice"
}

// ReservedCExternSymbol permits documented host-hook references, whose exact
// spelling is their contract. The exception is only for references: defining
// an export at the same symbol can conflict with a generated runtime body.
func ReservedCExternSymbol(symbol string) bool {
	switch symbol {
	case "oak_host_write", "oak_host_write_call", "oak_measured_value",
		"oak_test_host_launch_begin", "oak_test_host_launch_arg",
		"oak_test_host_launch_out", "oak_test_host_launch_end",
		"oak_test_host_dispatch_divergence",
		// stdlib/testing.oak imports these exact contracts. Both the native
		// test runner and fuzz harness define them; no prefix is exempted.
		"oak_test_host_fail", "oak_test_host_fail_values",
		"oak_test_host_discard", "oak_test_host_classify",
		"oak_test_host_liveness", "oak_test_host_trace",
		"oak_test_host_command", "oak_test_host_command_limit":
		return false
	}
	return ReservedCABI(symbol)
}
