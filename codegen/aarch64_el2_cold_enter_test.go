package codegen

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func TestAArch64EL2ColdEnterInstructionSequence(t *testing.T) {
	clang := requireAArch64Clang(t)
	sourcePath := filepath.Join("..", "examples", "hypervisor", "el2_cold_enter.oak")
	source, err := os.ReadFile(sourcePath)
	if err != nil {
		t.Fatal(err)
	}
	generated := generateSourceC(t, string(source))
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "free("} {
		if strings.Contains(generated, forbidden) {
			t.Fatalf("cold-entry path unexpectedly references heap primitive %q", forbidden)
		}
	}

	dir := t.TempDir()
	cPath := filepath.Join(dir, "el2_cold_enter.c")
	sPath := filepath.Join(dir, "el2_cold_enter.s")
	if err := os.WriteFile(cPath, []byte(generated), 0o600); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command(clang,
		"--target=aarch64-none-elf", "-march=armv8-a",
		"-std=c11", "-O2", "-ffreestanding",
		"-Wall", "-Wextra", "-Werror", "-Wno-unused-function",
		"-S", cPath, "-o", sPath,
	)
	if output, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("cross-compile cold EL2 entry: %v\n%s\n--- C ---\n%s", err, output, generated)
	}
	assemblyBytes, err := os.ReadFile(sPath)
	if err != nil {
		t.Fatal(err)
	}
	assembly := strings.ToLower(string(assemblyBytes))
	body := aarch64FunctionBody(t, assembly, "hypervisor_el2_cold_enter")
	flat := strings.Join(strings.Fields(body), " ")

	ordered := []string{
		"msr daifset, #2",
		"msr hcr_el2,",
		"msr vttbr_el2,",
		"msr vtcr_el2,",
		"msr cnthctl_el2,",
		"msr cntvoff_el2,",
		"msr sp_el1,",
		"msr elr_el2,",
		"msr spsr_el2,",
		"isb",
		"eret",
	}
	cursor := 0
	for _, want := range ordered {
		rel := strings.Index(flat[cursor:], want)
		if rel < 0 {
			t.Fatalf("cold-entry body lacks ordered instruction %q after offset %d:\n%s", want, cursor, body)
		}
		cursor += rel + len(want)
	}

	// Cold entry requires exactly visible synchronization/control transfer:
	// ISB before ERET, no invented completion barrier or wait path, and no
	// ordinary return from the non-returning function.
	forbidInstruction(t, body, "dmb", "dsb", "wfi", "wfe", "sev", "ret")
}
