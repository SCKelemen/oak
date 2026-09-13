package codegen

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// Processor-feature dispatch (docs/spec/93-simd.md section 6): the C shape
// and its AArch64 refinement. At the armv8-a baseline the SVE realization
// is compiled through its target attribute into the same translation
// unit — the predicate instructions appear in it and nowhere else — and
// the dispatched function branches on the probed word. With SVE in the
// baseline the static rule applies: the dispatched function never reads
// the word. (The body is a stand-in: this package's harness lowers a
// view without the pipeline's container facts, so it does not index; the
// executable agreement is compiler/e2e_dispatch_test.go.)
const aarch64DispatchSource = `
package main

count_sevens: (input: []u8) -> u32 dispatch { sve: count_sevens_sve } {
  n: u32 = len(input)
  n / u32(9)
}

count_sevens_sve: (input: []u8) -> u32 {
  remaining: u32 = len(input)
  offset: u32 = u32(0)
  total: u32 = u32(0)
  while remaining != u32(0) {
    active: simd.Active = simd.active_u8(remaining)
    chunk: simd.ScalableU8 = simd.load_active_u8(input, offset, active)
    mask: simd.ScalableU8 = simd.eq_active_u8(chunk, simd.splat_active_u8(u8(7), active), active)
    total = total + simd.count_nonzero_active_u8(mask, active)
    count: u32 = simd.count(active)
    offset = offset + count
    remaining = remaining - count
  }
  total
}
`

func TestAArch64DispatchShape(t *testing.T) {
	generated := generateSourceC(t, aarch64DispatchSource)
	for _, want := range []string{
		"#define OAK_CPU_SVE (1ull << 0)",
		"void oak_cpu_init(void) { oak_cpu_features = oak_cpu_probe(); }",
		"if (oak_cpu_features & OAK_CPU_SVE) { return oak_count_sevens_sve( input ); }",
		"return oak_count_sevens_sve( input ); /* the baseline guarantees sve */",
		`__attribute__((target("sve"))) u32 oak_count_sevens_sve( oak_view_u8 input )`,
		"oak_scalable_u8__sve chunk",
		"oak_simd_load_active_u8__sve( input, offset, active )",
		`__attribute__((target("sve"))) static inline oak_scalable_u8__sve oak_simd_load_active_u8__sve(`,
	} {
		if !strings.Contains(generated, want) {
			t.Errorf("generated C lacks %q:\n%s", want, generated)
		}
	}
	for _, forbidden := range []string{"(*", "malloc(", "calloc("} {
		if strings.Contains(generated, forbidden) {
			t.Errorf("dispatch lowering must not use function pointers or the heap: %q", forbidden)
		}
	}
}

func TestAArch64DispatchRefinement(t *testing.T) {
	clang := requireAArch64Clang(t)
	generated := generateSourceC(t, aarch64DispatchSource)
	dir := t.TempDir()
	cPath := filepath.Join(dir, "dispatch.c")
	if err := os.WriteFile(cPath, []byte(generated), 0o600); err != nil {
		t.Fatal(err)
	}
	compile := func(march string) string {
		sPath := filepath.Join(dir, strings.ReplaceAll(march, "+", "_")+".s")
		cmd := exec.Command(clang,
			"--target=aarch64-none-elf", "-march="+march, "-std=c11", "-O2", "-ffreestanding",
			"-Wall", "-Wextra", "-Werror", "-Wno-unused-function", "-S", cPath, "-o", sPath)
		if output, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("cross-compile dispatch at %s: %v\n%s\n--- C ---\n%s", march, err, output, generated)
		}
		bytes, err := os.ReadFile(sPath)
		if err != nil {
			t.Fatal(err)
		}
		return strings.ToLower(string(bytes))
	}
	// The baseline lacks SVE: the realization is compiled beside the body
	// through its attribute, the predicate instructions live in it alone,
	// and the dispatched function reads the probed word.
	baseline := compile("armv8-a")
	realization := aarch64FunctionBody(t, baseline, "count_sevens_sve")
	if !strings.Contains(realization, "whilelo") && !strings.Contains(realization, "whilelt") {
		t.Fatalf("the sve realization carries no predicate instruction at the armv8-a baseline:\n%s", realization)
	}
	dispatched := aarch64FunctionBody(t, baseline, "count_sevens")
	if !strings.Contains(dispatched, "oak_cpu_features") {
		t.Fatalf("the dispatched function does not read the probed word at the armv8-a baseline:\n%s", dispatched)
	}
	if strings.Contains(dispatched, "whilelo") || strings.Contains(dispatched, "whilelt") {
		t.Fatalf("predicate instructions leaked into the dispatched function's baseline path:\n%s", dispatched)
	}
	forbidInstruction(t, dispatched, "blr")
	// The probe reads the ID registers on a freestanding target.
	probe := aarch64FunctionBody(t, baseline, "cpu_init")
	if !strings.Contains(probe, "id_aa64pfr0_el1") && !strings.Contains(probe, "s3_0_c0_c4_0") {
		t.Fatalf("the freestanding probe does not read ID_AA64PFR0_EL1:\n%s", probe)
	}
	// SVE in the baseline: the static rule — no read of the word.
	static := compile("armv8-a+sve")
	dispatched = aarch64FunctionBody(t, static, "count_sevens")
	if strings.Contains(dispatched, "oak_cpu_features") {
		t.Fatalf("with SVE in the baseline the dispatched function must not consult the probed word:\n%s", dispatched)
	}
}
