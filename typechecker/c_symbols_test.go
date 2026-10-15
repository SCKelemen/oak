package typechecker

import (
	"strings"
	"testing"
)

func TestCFunctionSymbolsPreserveCompatibleABI(t *testing.T) {
	for _, test := range []struct{ pkg, name, want string }{
		{"", "main", "oak_main"}, {"main", "step", "oak_step"},
		{"ops", "step", "oak_ops_step"}, {"", "add", "oak_add"},
		{"", "claimed", "oak_claimed"}, {"", "meant", "oak_meant"},
		{"", "la1_grid", "oak_la1_grid"}, {"", "la1_a0", "oak_la1_a0"}, {"", "la1_g", "oak_la1_g"},
		{"", "6Handle_merge", "oak_6Handle_merge"},
		{"", "0lit_0", "oak_0lit_0"},
		{"", "store", "oak_0f_p0__nstore"},
		{"add", "u32", "oak_0f_p3_add_nu32"},
	} {
		if got := CFunctionSymbol(test.pkg, test.name); got != test.want {
			t.Errorf("CFunctionSymbol(%q, %q) = %q, want %q", test.pkg, test.name, got, test.want)
		}
	}
}

func TestCFunctionRuntimeEscapesAreInjective(t *testing.T) {
	seen := map[string]string{}
	for _, name := range []string{"store", "add_u32", "bounds_trap", "view_u8", "fn_at", "oak_0f_p0_nstore", "0f_p0__nstore", "add__u32", "add_u_u32", "_scrutinee_0", "eq_oak_A", "arm64_mmio_store64", "foo_0g_cell"} {
		for _, pkg := range []string{"", "ops", "add", "add_u", "with.dot", "with_dot"} {
			got := CFunctionSymbol(pkg, name)
			identity := pkg + ":" + name
			if prior, duplicate := seen[got]; duplicate {
				t.Errorf("%s and %s both map to %s", prior, identity, got)
			}
			seen[got] = identity
			if !ValidCSymbol(got) {
				t.Errorf("invalid C identifier %q", got)
			}
			if ReservedCRuntimeSymbol(got) && !strings.HasPrefix(got, "oak_0f_") {
				t.Errorf("escaped name still occupies runtime family: %q", got)
			}
			if pkg == "" && CFunctionSymbol("main", name) != got {
				t.Errorf("main and empty packages differ for %q", name)
			}
		}
	}
	// Both legacy spellings are oak_add_u32. The escape must retain the
	// package/name boundary, rather than escaping only their concatenation.
	if CFunctionSymbol("", "add_u32") == CFunctionSymbol("add", "u32") {
		t.Fatal("escaped package/name boundary aliases")
	}
}

func TestCFunctionRuntimeFamilies(t *testing.T) {
	for _, symbol := range []string{
		"oak_store", "oak_index", "oak_bounds_trap", "oak_fn_at", "oak_add_u32",
		"oak_span_store_oak_Pair", "oak_view_u8", "oak_arr_u8_3", "oak_eq_oak_Pair",
		"oak_arith_checked_add_u32", "oak_arm64_mmio_store64", "oak_simd_load_u8x16",
		"oak_scalable_u32_rvv", "oak_refine_Small", "oak_atomic_lock_free_u64",
		"oak_f16_round_f32", "oak_conv_f32_to_u32", "oak_total_order_f64",
		"oak_layout_off_Frame_x", "oak_field_oak_Frame_x", "oak_const_EOF",
		"oak_extern_clock_gettime", "oak_tramp_f", "oak_union_layout_Frame",
		"oak_cpu_probe", "oak_riscv_hwprobe", "oak_dispatch_divergence",
		"oak_measured_init", "oak_host_write_call", "oak_test_host_launch_end",
		"oak_dispatch_claimed", "oak_dispatch_meant", "oak_host_la1_grid", "oak_host_la1_a0", "oak_host_la1_g",
		"oak_0f_p0__nstore", "oak_ops_0g_cell", "oak_id_short",
	} {
		if !ReservedCRuntimeSymbol(symbol) {
			t.Errorf("runtime family not reserved: %s", symbol)
		}
		name := strings.TrimPrefix(symbol, "oak_")
		if CFunctionSymbol("", name) == symbol {
			t.Errorf("callable still aliases %s", symbol)
		}
	}
}
