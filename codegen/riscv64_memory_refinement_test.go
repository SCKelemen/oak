package codegen

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// RISC-V memory refinement (docs/spec/69-riscv-memory-refinement.md): the
// Oak-generated atomics compiled for RV64 by a clang with the riscv64
// target emit the admitted instruction families — Oak's OS-profile
// mapping, RCsc acquire included — checked per function with the same
// helpers the AArch64 layer uses. CI sets OAK_REQUIRE_RISCV64_CLANG=1.

// requireRISCV64Compiler finds a C compiler that targets riscv64 as an
// argv prefix: clang on PATH, Homebrew LLVM's clang, or zig cc.
func requireRISCV64Compiler(t *testing.T) []string {
	t.Helper()
	probe := func(argv []string) bool {
		args := append(append([]string{}, argv[1:]...), "--target=riscv64-unknown-none-elf", "-march=rv64gc", "-x", "c", "-S", "-o", os.DevNull, "-")
		cmd := exec.Command(argv[0], args...)
		cmd.Stdin = strings.NewReader("int oak_probe(void) { return 0; }\n")
		return cmd.Run() == nil
	}
	if clang, err := exec.LookPath("clang"); err == nil && probe([]string{clang}) {
		return []string{clang}
	}
	if _, err := os.Stat("/opt/homebrew/opt/llvm/bin/clang"); err == nil && probe([]string{"/opt/homebrew/opt/llvm/bin/clang"}) {
		return []string{"/opt/homebrew/opt/llvm/bin/clang"}
	}
	if zig, err := exec.LookPath("zig"); err == nil {
		return []string{zig, "cc"}
	}
	if os.Getenv("OAK_REQUIRE_RISCV64_CLANG") == "1" {
		t.Fatal("RISC-V memory refinement requires a clang with the riscv64 target in CI")
	}
	t.Skip("no C compiler with the riscv64 target")
	return nil
}

func compileRISCV64Assembly(t *testing.T) string {
	t.Helper()
	compiler := requireRISCV64Compiler(t)
	generated := generateSourceC(t, aarch64AtomicRefinementSource)
	admission := `
_Static_assert(__atomic_always_lock_free(sizeof(u8), 0), "u8 atomics must be lock-free");
_Static_assert(__atomic_always_lock_free(sizeof(u16), 0), "u16 atomics must be lock-free");
_Static_assert(__atomic_always_lock_free(sizeof(u32), 0), "u32 atomics must be lock-free");
_Static_assert(__atomic_always_lock_free(sizeof(u64), 0), "u64 atomics must be lock-free");
`
	dir := t.TempDir()
	cPath := filepath.Join(dir, "oak_atomic_riscv64.c")
	sPath := filepath.Join(dir, "oak_atomic_riscv64.s")
	if err := os.WriteFile(cPath, []byte(generated+admission), 0o600); err != nil {
		t.Fatal(err)
	}
	args := append(append([]string{}, compiler[1:]...),
		"--target=riscv64-unknown-none-elf", "-march=rv64gc",
		"-std=c11", "-O2", "-ffreestanding",
		"-Wall", "-Wextra", "-Werror", "-Wno-unused-function", "-Wno-parentheses-equality",
		"-S", cPath, "-o", sPath)
	if compiler[0] != "clang" && strings.HasSuffix(compiler[0], "zig") {
		// zig spells the target its own way.
		for i, a := range args {
			if a == "--target=riscv64-unknown-none-elf" {
				args[i] = "--target=riscv64-freestanding-none"
			}
			if a == "-march=rv64gc" {
				args[i] = "-mcpu=generic_rv64+a"
			}
		}
	}
	cmd := exec.Command(compiler[0], args...)
	if output, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("cross-compile Oak-generated atomics for riscv64: %v\n%s", err, output)
	}
	assembly, err := os.ReadFile(sPath)
	if err != nil {
		t.Fatal(err)
	}
	return strings.ToLower(string(assembly))
}

// The loads and stores: relaxed plain; Oak acquire is the RCsc seq_cst
// sequence (a full fence before the load), not C11's RCpc `ld; fence r,rw`;
// release is `fence rw,w` before the store; seq_cst store adds the trailing
// full fence.
func TestRISCV64AtomicLoadStoreAndFenceRefinement(t *testing.T) {
	assembly := compileRISCV64Assembly(t)
	relaxedLoad := aarch64FunctionBody(t, assembly, "load_relaxed")
	forbidInstruction(t, relaxedLoad, "fence", "fence.tso")
	requireInstruction(t, relaxedLoad, "ld")
	for _, name := range []string{"load_acquire", "load_seq_cst"} {
		body := aarch64FunctionBody(t, assembly, name)
		requireInstruction(t, body, "ld")
		if !strings.Contains(body, "fence\trw, rw") && !strings.Contains(body, "fence rw, rw") {
			t.Fatalf("%s lacks the full fence before the load (RCsc acquire, docs/spec/69-riscv-memory-refinement.md section 2):\n%s", name, body)
		}
		if !strings.Contains(body, "fence\tr, rw") && !strings.Contains(body, "fence r, rw") {
			t.Fatalf("%s lacks the acquire fence after the load:\n%s", name, body)
		}
	}
	relaxedStore := aarch64FunctionBody(t, assembly, "store_relaxed")
	forbidInstruction(t, relaxedStore, "fence", "fence.tso")
	for _, name := range []string{"store_release", "store_seq_cst"} {
		body := aarch64FunctionBody(t, assembly, name)
		requireInstruction(t, body, "sd")
		if !strings.Contains(body, "fence\trw, w") && !strings.Contains(body, "fence rw, w") {
			t.Fatalf("%s lacks the release fence before the store:\n%s", name, body)
		}
	}
	// The seq_cst store has two Appendix A mappings: `fence rw,w; sd` (the
	// original Table A.6, which Ubuntu's clang 18 emits) and `fence rw,w;
	// sd; fence rw,rw` (later LLVM, the mapping the chapter's table shows).
	// Oak.RiscVMemory judges both `releaseOnly` — the trailing fence adds no
	// local ordering the model needs, since seq_cst loads carry the leading
	// full fence (c11_store_seqCst_trailing_fence_optional) — so either is
	// admitted; which one the toolchain chose is logged, not required.
	if body := aarch64FunctionBody(t, assembly, "store_seq_cst"); strings.Contains(body, "fence\trw, rw") || strings.Contains(body, "fence rw, rw") {
		t.Log("store_seq_cst: trailing full fence present (the later Appendix A mapping)")
	} else {
		t.Log("store_seq_cst: no trailing fence (Table A.6 mapping); the leading fence rw,w is required and was found")
	}
	requireInstruction(t, aarch64FunctionBody(t, assembly, "fence_acquire"), "fence")
	requireInstruction(t, aarch64FunctionBody(t, assembly, "fence_release"), "fence")
	requireInstruction(t, aarch64FunctionBody(t, assembly, "fence_acq_rel"), "fence.tso", "fence")
	if body := aarch64FunctionBody(t, assembly, "fence_seq_cst"); !strings.Contains(body, "fence\trw, rw") && !strings.Contains(body, "fence rw, rw") {
		t.Fatalf("fence_seq_cst is not the full fence:\n%s", body)
	}
}

// Read-modify-writes: relaxed is the bare AMO; every acquiring order is
// `.aqrl` (RCsc), never `.aq` alone; compare-exchange pairs `lr.aqrl` with
// `sc.rl` for acquiring orders.
func TestRISCV64AtomicRMWAndCASUseRCscAnnotations(t *testing.T) {
	assembly := compileRISCV64Assembly(t)
	relaxed := aarch64FunctionBody(t, assembly, "fetch_add_relaxed")
	requireInstruction(t, relaxed, "amoadd.d")
	forbidInstruction(t, relaxed, "amoadd.d.aq", "amoadd.d.rl", "amoadd.d.aqrl", "fence")
	for _, name := range []string{"fetch_add_acq_rel", "fetch_add_seq_cst"} {
		body := aarch64FunctionBody(t, assembly, name)
		requireInstruction(t, body, "amoadd.d.aqrl")
		forbidInstruction(t, body, "amoadd.d.aq")
	}
	casRelaxed := aarch64FunctionBody(t, assembly, "cas_relaxed")
	requireInstruction(t, casRelaxed, "lr.d")
	requireInstruction(t, casRelaxed, "sc.d")
	forbidInstruction(t, casRelaxed, "lr.d.aq", "lr.d.aqrl", "sc.d.rl")
	for _, name := range []string{"cas_acq_rel", "cas_seq_cst"} {
		body := aarch64FunctionBody(t, assembly, name)
		requireInstruction(t, body, "lr.d.aqrl")
		requireInstruction(t, body, "sc.d.rl")
		forbidInstruction(t, body, "lr.d.aq")
	}
}
