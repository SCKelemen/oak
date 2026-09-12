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

// The register handoff (docs/spec/100-aarch64-control-transfer.md): the
// value eret_x0 carries is in x0 at the ERET — here moved from the second
// argument register — and the handoff adds no other instruction: no ret,
// no barrier the source did not write.
func TestAArch64EretX0CarriesTheValueInX0(t *testing.T) {
	clang := requireAArch64Clang(t)
	generated := generateSourceC(t, `
package main
fn enter(sp: u64, arg: u64) -> never {
  arm64.write_sp_el0(sp)
  arm64.eret_x0(arg)
}
`)
	if strings.Contains(generated, "malloc(") || strings.Contains(generated, "calloc(") {
		t.Fatalf("eret_x0 lowering acquired a heap dependency:\n%s", generated)
	}
	dir := t.TempDir()
	cPath := filepath.Join(dir, "eret_x0.c")
	sPath := filepath.Join(dir, "eret_x0.s")
	if err := os.WriteFile(cPath, []byte(generated), 0o600); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command(clang,
		"--target=aarch64-none-elf", "-march=armv8-a", "-std=c11", "-O2", "-ffreestanding",
		"-Wall", "-Wextra", "-Werror", "-Wno-unused-function", "-S", cPath, "-o", sPath)
	if output, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("cross-compile eret_x0: %v\n%s\n--- C ---\n%s", err, output, generated)
	}
	assemblyBytes, err := os.ReadFile(sPath)
	if err != nil {
		t.Fatal(err)
	}
	body := aarch64FunctionBody(t, strings.ToLower(string(assemblyBytes)), "enter")
	flat := strings.Join(strings.Fields(body), " ")
	sp := strings.Index(flat, "msr sp_el0, x0")
	mov := strings.Index(flat, "mov x0, x1")
	eret := strings.Index(flat, "eret")
	if sp < 0 || mov < 0 || eret < 0 || !(sp < mov && mov < eret) {
		t.Fatalf("expected msr sp_el0, x0; mov x0, x1; eret in order:\n%s", body)
	}
	forbidInstruction(t, body, "ret", "dmb", "dsb", "isb", "wfi", "wfe", "sev")
}
