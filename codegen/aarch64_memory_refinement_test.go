package codegen

import (
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

const aarch64AtomicRefinementSource = `
package main
cell: Atomic[u64]

fn load_relaxed() -> u64
  atomic_load_relaxed(cell)

fn load_acquire() -> u64
  atomic_load_acquire(cell)

fn load_seq_cst() -> u64
  atomic_load_seq_cst(cell)

fn store_relaxed(value: u64) -> ()
  atomic_store_relaxed(cell, value)

fn store_release(value: u64) -> ()
  atomic_store_release(cell, value)

fn store_seq_cst(value: u64) -> ()
  atomic_store_seq_cst(cell, value)

fn fetch_add_relaxed(value: u64) -> u64
  atomic_fetch_add_relaxed(cell, value)

fn fetch_add_acq_rel(value: u64) -> u64
  atomic_fetch_add_acq_rel(cell, value)

fn fetch_add_seq_cst(value: u64) -> u64
  atomic_fetch_add_seq_cst(cell, value)

fn cas_relaxed(expected: u64, desired: u64) -> u64
  atomic_compare_exchange_relaxed_relaxed(cell, expected, desired)

fn cas_acq_rel(expected: u64, desired: u64) -> u64
  atomic_compare_exchange_acq_rel_acquire(cell, expected, desired)

fn cas_seq_cst(expected: u64, desired: u64) -> u64
  atomic_compare_exchange_seq_cst_seq_cst(cell, expected, desired)

fn fence_acquire() -> ()
  atomic_fence_acquire()

fn fence_release() -> ()
  atomic_fence_release()

fn fence_acq_rel() -> ()
  atomic_fence_acq_rel()

fn fence_seq_cst() -> ()
  atomic_fence_seq_cst()
`

func requireAArch64Clang(t *testing.T) string {
	t.Helper()
	clang, err := exec.LookPath("clang")
	if err == nil {
		return clang
	}
	if os.Getenv("OAK_REQUIRE_AARCH64_CLANG") == "1" {
		t.Fatal("AArch64 memory refinement requires clang in CI")
	}
	t.Skip("clang is required for AArch64 memory refinement test")
	return ""
}

func compileAArch64Assembly(t *testing.T, march string) string {
	t.Helper()
	clang := requireAArch64Clang(t)
	generated := generateSourceC(t, aarch64AtomicRefinementSource)

	// Admission assertions are target/compiler facts rather than language
	// assumptions. Oak's fixed-width v1 carriers must be always lock-free on
	// the AArch64 OS profile before hard-realtime code may depend on them.
	admission := `
_Static_assert(__atomic_always_lock_free(sizeof(u8), 0), "u8 atomics must be lock-free");
_Static_assert(__atomic_always_lock_free(sizeof(u16), 0), "u16 atomics must be lock-free");
_Static_assert(__atomic_always_lock_free(sizeof(u32), 0), "u32 atomics must be lock-free");
_Static_assert(__atomic_always_lock_free(sizeof(u64), 0), "u64 atomics must be lock-free");
`

	dir := t.TempDir()
	cPath := filepath.Join(dir, "oak_atomic_aarch64.c")
	sPath := filepath.Join(dir, "oak_atomic_aarch64.s")
	if err := os.WriteFile(cPath, []byte(generated+admission), 0o600); err != nil {
		t.Fatal(err)
	}
	args := []string{
		"--target=aarch64-none-elf",
		"-march=" + march,
		"-std=c11", "-O2", "-ffreestanding",
		"-Wall", "-Wextra", "-Werror", "-Wno-unused-function",
		"-S", cPath, "-o", sPath,
	}
	cmd := exec.Command(clang, args...)
	if output, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("cross-compile Oak-generated atomics for %s: %v\n%s\n--- C ---\n%s", march, err, output, generated+admission)
	}
	assembly, err := os.ReadFile(sPath)
	if err != nil {
		t.Fatal(err)
	}
	return strings.ToLower(string(assembly))
}

func aarch64FunctionBody(t *testing.T, assembly, oakName string) string {
	t.Helper()
	label := "oak_" + oakName + ":"
	start := strings.Index(assembly, label)
	if start < 0 {
		t.Fatalf("assembly does not contain %s\n%s", label, assembly)
	}
	rest := assembly[start+len(label):]
	// Clang emits .Lfunc_endN on ELF AArch64. Fall back to the next global
	// function if that spelling changes; either boundary is structural rather
	// than tied to instruction scheduling.
	end := strings.Index(rest, ".lfunc_end")
	if end < 0 {
		if next := strings.Index(rest, "\n\t.globl\t"); next >= 0 {
			end = next
		} else {
			end = len(rest)
		}
	}
	return rest[:end]
}

func hasInstruction(body, mnemonic string) bool {
	// Match a mnemonic token at the start of an assembly instruction, allowing
	// Clang's tabs/spaces but not substrings such as ldar matching ldapr.
	re := regexp.MustCompile(`(?m)^\s*` + regexp.QuoteMeta(mnemonic) + `\s`)
	return re.FindStringIndex(body) != nil
}

func requireInstruction(t *testing.T, body string, alternatives ...string) {
	t.Helper()
	for _, mnemonic := range alternatives {
		if hasInstruction(body, mnemonic) {
			return
		}
	}
	t.Fatalf("function body lacks required instruction family %v:\n%s", alternatives, body)
}

func forbidInstruction(t *testing.T, body string, mnemonics ...string) {
	t.Helper()
	for _, mnemonic := range mnemonics {
		if hasInstruction(body, mnemonic) {
			t.Fatalf("function body unexpectedly contains %s:\n%s", mnemonic, body)
		}
	}
}

func TestAArch64BaseAtomicLoadStoreAndFenceRefinement(t *testing.T) {
	assembly := compileAArch64Assembly(t, "armv8-a")

	relaxedLoad := aarch64FunctionBody(t, assembly, "load_relaxed")
	requireInstruction(t, relaxedLoad, "ldr")
	forbidInstruction(t, relaxedLoad, "ldar", "ldapr", "dmb")

	for _, name := range []string{"load_acquire", "load_seq_cst"} {
		body := aarch64FunctionBody(t, assembly, name)
		requireInstruction(t, body, "ldar")
		// Oak's AArch64 OS profile deliberately requires RCsc acquire rather
		// than accepting LDAPR/RCpc as an interchangeable projection.
		forbidInstruction(t, body, "ldapr")
	}

	relaxedStore := aarch64FunctionBody(t, assembly, "store_relaxed")
	requireInstruction(t, relaxedStore, "str")
	forbidInstruction(t, relaxedStore, "stlr", "dmb")

	for _, name := range []string{"store_release", "store_seq_cst"} {
		body := aarch64FunctionBody(t, assembly, name)
		requireInstruction(t, body, "stlr")
	}

	acquireFence := aarch64FunctionBody(t, assembly, "fence_acquire")
	requireInstruction(t, acquireFence, "dmb")
	if !strings.Contains(acquireFence, "ishld") {
		t.Fatalf("acquire fence must use an acquire-capable DMB domain:\n%s", acquireFence)
	}

	for _, name := range []string{"fence_release", "fence_acq_rel", "fence_seq_cst"} {
		body := aarch64FunctionBody(t, assembly, name)
		requireInstruction(t, body, "dmb")
		if !strings.Contains(body, "ish") {
			t.Fatalf("%s must use inner-shareable DMB:\n%s", name, body)
		}
	}
}

func TestAArch64BaseAtomicRMWAndCASUseOrderedExclusivePairs(t *testing.T) {
	assembly := compileAArch64Assembly(t, "armv8-a")

	for _, name := range []string{"fetch_add_relaxed", "cas_relaxed"} {
		body := aarch64FunctionBody(t, assembly, name)
		requireInstruction(t, body, "ldxr")
		requireInstruction(t, body, "stxr")
		forbidInstruction(t, body, "ldaxr", "stlxr")
	}

	for _, name := range []string{"fetch_add_acq_rel", "fetch_add_seq_cst", "cas_acq_rel", "cas_seq_cst"} {
		body := aarch64FunctionBody(t, assembly, name)
		requireInstruction(t, body, "ldaxr")
		requireInstruction(t, body, "stlxr")
	}
}

func TestAArch64LSEAtomicRMWAndCASUseSingleInstructionForms(t *testing.T) {
	assembly := compileAArch64Assembly(t, "armv8.1-a+lse")

	relaxedAdd := aarch64FunctionBody(t, assembly, "fetch_add_relaxed")
	requireInstruction(t, relaxedAdd, "ldadd")
	forbidInstruction(t, relaxedAdd, "ldadda", "ldaddl", "ldaddal")

	for _, name := range []string{"fetch_add_acq_rel", "fetch_add_seq_cst"} {
		body := aarch64FunctionBody(t, assembly, name)
		requireInstruction(t, body, "ldaddal")
	}

	relaxedCAS := aarch64FunctionBody(t, assembly, "cas_relaxed")
	requireInstruction(t, relaxedCAS, "cas")
	forbidInstruction(t, relaxedCAS, "casa", "casl", "casal")

	for _, name := range []string{"cas_acq_rel", "cas_seq_cst"} {
		body := aarch64FunctionBody(t, assembly, name)
		requireInstruction(t, body, "casal")
	}
}
