package codegen

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

const aarch64EretSource = `
package main
fn enter() -> never
  arm64.eret()
`

func TestAArch64EretIsExactNonReturningControlTransfer(t *testing.T) {
	clang := requireAArch64Clang(t)
	generated := generateSourceC(t, aarch64EretSource)
	if strings.Contains(generated, "malloc(") || strings.Contains(generated, "calloc(") || strings.Contains(generated, "realloc(") || strings.Contains(generated, "free(") {
		t.Fatalf("ERET lowering acquired a heap dependency:\n%s", generated)
	}

	dir := t.TempDir()
	cPath := filepath.Join(dir, "eret.c")
	sPath := filepath.Join(dir, "eret.s")
	if err := os.WriteFile(cPath, []byte(generated), 0o600); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command(clang,
		"--target=aarch64-none-elf", "-march=armv8-a", "-std=c11", "-O2", "-ffreestanding",
		"-Wall", "-Wextra", "-Werror", "-Wno-unused-function", "-S", cPath, "-o", sPath)
	if output, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("cross-compile ERET: %v\n%s\n--- C ---\n%s", err, output, generated)
	}
	assemblyBytes, err := os.ReadFile(sPath)
	if err != nil {
		t.Fatal(err)
	}
	body := aarch64FunctionBody(t, strings.ToLower(string(assemblyBytes)), "enter")
	requireInstruction(t, body, "eret")
	forbidInstruction(t, body, "ret", "dmb", "dsb", "isb", "wfi", "wfe", "sev")
}
