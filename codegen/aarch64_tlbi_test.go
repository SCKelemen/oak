package codegen

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/semir"
)

const aarch64TLBISource = `
package main

fn maintenance_vmalls12e1is() -> ()
  arm64.tlbi_vmalls12e1is()
`

func compileTLBIAArch64Assembly(t *testing.T, source string) (generated, assembly string) {
	t.Helper()
	clang := requireAArch64Clang(t)
	generated = generateSourceC(t, source)
	dir := t.TempDir()
	cPath := filepath.Join(dir, "tlbi.c")
	sPath := filepath.Join(dir, "tlbi.s")
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
		t.Fatalf("cross-compile generated TLBI C: %v\n%s\n--- C ---\n%s", err, output, generated)
	}
	assemblyBytes, err := os.ReadFile(sPath)
	if err != nil {
		t.Fatal(err)
	}
	return generated, strings.ToLower(string(assemblyBytes))
}

func TestAArch64TLBIHelperAndInstructionAreExact(t *testing.T) {
	member := semir.Arm64TLBIMembers()[0]
	spec, ok := semir.LookupArm64TLBI(member)
	if !ok {
		t.Fatalf("catalog member %q has no TLBI specification", member)
	}
	if err := semir.ValidateArm64TLBI(spec); err != nil {
		t.Fatalf("invalid catalog member %q: %v", member, err)
	}
	helper, ok := arm64HelperSources[spec.Member]
	if !ok {
		t.Fatalf("C backend did not register catalog member %q", spec.Member)
	}
	wantAsm := `__asm__ volatile("` + spec.Instruction + `" ::: "memory");`
	if !strings.Contains(helper, wantAsm) {
		t.Fatalf("catalog-derived C helper lacks %q:\n%s", wantAsm, helper)
	}

	generated, assembly := compileTLBIAArch64Assembly(t, aarch64TLBISource)
	if count := strings.Count(generated, wantAsm); count != 1 {
		t.Fatalf("generated C has %d exact TLBI asm bodies, want 1:\n%s", count, generated)
	}
	if !strings.Contains(generated,
		`#error "arm64.tlbi_vmalls12e1is requires an AArch64 target"`) {
		t.Fatalf("generated TLBI helper does not fail closed off AArch64:\n%s", generated)
	}
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "free("} {
		if strings.Contains(generated, forbidden) {
			t.Fatalf("generated TLBI path references heap primitive %q:\n%s", forbidden, generated)
		}
	}

	plain := generateSourceC(t, "package main\nfn plain() -> u32 = u32(0)\n")
	if strings.Contains(plain, "oak_arm64_tlbi_vmalls12e1is") {
		t.Fatalf("unused TLBI helper was emitted:\n%s", plain)
	}

	body := aarch64FunctionBody(t, assembly, "maintenance_vmalls12e1is")
	requireInstruction(t, body, "tlbi")
	if !strings.Contains(body, "tlbi\tvmalls12e1is") &&
		!strings.Contains(body, "tlbi vmalls12e1is") {
		t.Fatalf("compiled function lacks exact TLBI operand:\n%s", body)
	}
	if strings.Count(body, "tlbi") != 1 {
		t.Fatalf("compiled function has hidden or duplicate TLBI instructions:\n%s", body)
	}
	for _, forbidden := range []string{"dmb", "dsb", "isb"} {
		if hasInstruction(body, forbidden) {
			t.Fatalf("compiled TLBI function unexpectedly contains %s:\n%s", forbidden, body)
		}
	}
}

func TestAArch64TLBIContextSyncSequenceOrder(t *testing.T) {
	path := filepath.Join("..", "examples", "hypervisor",
		"stage2_vmalls12e1is_context_sync.oak")
	source, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	_, assembly := compileTLBIAArch64Assembly(t, string(source))
	body := aarch64FunctionBody(t, assembly,
		"hypervisor_stage2_vmalls12e1is_context_sync")

	var systemInstructions []string
	for _, line := range strings.Split(body, "\n") {
		fields := strings.Fields(line)
		if len(fields) == 0 {
			continue
		}
		switch fields[0] {
		case "dmb", "dsb", "tlbi":
			if len(fields) < 2 {
				t.Fatalf("system instruction lacks operand: %q\n%s", line, body)
			}
			systemInstructions = append(systemInstructions, fields[0]+" "+fields[1])
		case "isb":
			systemInstructions = append(systemInstructions, fields[0])
		}
	}
	if got, want := strings.Join(systemInstructions, "|"),
		"dsb ish|tlbi vmalls12e1is|dsb ish|isb"; got != want {
		t.Fatalf("context-sync system instruction order = %q, want %q:\n%s", got, want, body)
	}
}

func TestAArch64TLBIGeneratedCFailsClosedOnHost(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("host C compiler is not available")
	}
	generated := generateSourceC(t, aarch64TLBISource)
	dir := t.TempDir()
	cPath := filepath.Join(dir, "tlbi.c")
	oPath := filepath.Join(dir, "tlbi.o")
	if err := os.WriteFile(cPath, []byte(generated), 0o600); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command(cc, "-std=c11", "-O2", "-DOAK_PORTABLE_INTRINSICS",
		"-c", cPath, "-o", oPath)
	output, err := cmd.CombinedOutput()
	if err == nil {
		t.Fatal("non-AArch64 compilation of TLBI unexpectedly succeeded")
	}
	if !strings.Contains(string(output), "arm64.tlbi_vmalls12e1is requires an AArch64 target") {
		t.Fatalf("host failure did not explain AArch64 TLBI requirement:\n%s\n--- C ---\n%s",
			output, generated)
	}
}
