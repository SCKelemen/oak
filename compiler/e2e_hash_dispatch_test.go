package compiler

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// The hash package's AArch64 kernels are dispatch realizations
// (docs/spec/93-simd.md section 6; stdlib/hash.arm64.oakasm): crc32c_step7
// dispatches to its unit on FEAT_CRC32 and sha256_block_hw to its unit on
// FEAT_SHA256, decided once by the processor probe, so an ARMv8.0 core
// without the extension runs the Oak bodies instead of faulting. The C
// shape: the branch on the probed word in the dispatched functions, the
// units present under their extension directives, no #error for the
// body-less declarations off AArch64, and a clean cross-compile at the
// armv8-a baseline (which has neither extension).
func TestE2EHashKernelsAreDispatchRealizations(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/hash_dispatch\noak 0.1.0\n",
		"main.oak": crcShaProgram,
	})
	emitted, err := New().WithPackageDir(root).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"oak_cpu_features & OAK_CPU_CRC",
		"oak_cpu_features & OAK_CPU_SHA2",
		".arch_extension crc",
		".arch_extension sha2",
		"crc32c_ustep7_uasm",
		"sha256_ublock_uasm",
		"hw.optional.armv8_crc32",
	} {
		if !strings.Contains(emitted, want) {
			t.Errorf("emitted C lacks %q", want)
		}
	}
	if strings.Contains(emitted, "#error \"asm unit") {
		t.Errorf("a body-less realization still fails closed off AArch64:\n%s", emitted[strings.Index(emitted, "#error \"asm unit")-200:strings.Index(emitted, "#error \"asm unit")+120])
	}
	clang, err := exec.LookPath("clang")
	if err != nil {
		t.Skip("clang is required for the cross-compile")
	}
	dir := t.TempDir()
	cPath := filepath.Join(dir, "hash.c")
	if err := os.WriteFile(cPath, []byte(emitted), 0o600); err != nil {
		t.Fatal(err)
	}
	// aarch64-none-elf lacks the hosted headers the program's write() extern
	// wants; compile-only with the freestanding probe is the point here.
	for _, march := range []string{"armv8-a", "armv8-a+crc+sha2"} {
		cmd := exec.Command(clang, "--target=aarch64-none-elf", "-march="+march, "-std=c11", "-O2", "-ffreestanding", "-Wno-parentheses-equality", "-c", cPath, "-o", filepath.Join(dir, "hash.o"))
		if out, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("cross-compile at %s: %v\n%s", march, err, out)
		}
	}
}
