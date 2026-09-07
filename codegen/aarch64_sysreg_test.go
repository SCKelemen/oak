package codegen

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

const aarch64SysRegSource = `
package main

fn sysreg_read_hcr() -> u64
  arm64.read_hcr_el2()
fn sysreg_write_hcr(value: u64) -> ()
  arm64.write_hcr_el2(value)
fn sysreg_read_esr() -> u64
  arm64.read_esr_el2()
fn sysreg_read_counter() -> u64
  arm64.read_cntvct_el0()
fn sysreg_write_vttbr(value: u64) -> ()
  arm64.write_vttbr_el2(value)
fn sysreg_write_vtcr(value: u64) -> ()
  arm64.write_vtcr_el2(value)
`

func compileSysRegAArch64Assembly(t *testing.T) (generated, assembly string) {
	t.Helper()
	clang := requireAArch64Clang(t)
	generated = generateSourceC(t, aarch64SysRegSource)
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "free("} {
		if strings.Contains(generated, forbidden) {
			t.Fatalf("generated sysreg path unexpectedly references heap primitive %q:\n%s", forbidden, generated)
		}
	}

	dir := t.TempDir()
	cPath := filepath.Join(dir, "sysreg.c")
	sPath := filepath.Join(dir, "sysreg.s")
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
		t.Fatalf("cross-compile generated system-register C: %v\n%s\n--- C ---\n%s", err, output, generated)
	}
	bytes, err := os.ReadFile(sPath)
	if err != nil {
		t.Fatal(err)
	}
	return generated, strings.ToLower(string(bytes))
}

func TestAArch64SystemRegisterInstructionRefinement(t *testing.T) {
	_, assembly := compileSysRegAArch64Assembly(t)
	cases := []struct {
		fn       string
		mnemonic string
		reg      string
	}{
		{"sysreg_read_hcr", "mrs", "hcr_el2"},
		{"sysreg_write_hcr", "msr", "hcr_el2"},
		{"sysreg_read_esr", "mrs", "esr_el2"},
		{"sysreg_read_counter", "mrs", "cntvct_el0"},
		{"sysreg_write_vttbr", "msr", "vttbr_el2"},
		{"sysreg_write_vtcr", "msr", "vtcr_el2"},
	}
	for _, tc := range cases {
		t.Run(tc.fn, func(t *testing.T) {
			body := aarch64FunctionBody(t, assembly, tc.fn)
			requireInstruction(t, body, tc.mnemonic)
			if !strings.Contains(body, tc.reg) {
				t.Fatalf("%s lacks exact system register %s:\n%s", tc.fn, tc.reg, body)
			}
			for _, barrier := range []string{"dmb", "dsb", "isb"} {
				if hasInstruction(body, barrier) {
					t.Fatalf("%s acquired hidden %s barrier:\n%s", tc.fn, barrier, body)
				}
			}
		})
	}
}

func TestAArch64SystemRegisterGeneratedCFailsClosedOnHost(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("host C compiler is not available")
	}
	generated := generateSourceC(t, `
package main
fn read() -> u64
  arm64.read_hcr_el2()
`)
	dir := t.TempDir()
	cPath := filepath.Join(dir, "sysreg.c")
	oPath := filepath.Join(dir, "sysreg.o")
	if err := os.WriteFile(cPath, []byte(generated), 0o600); err != nil {
		t.Fatal(err)
	}
	// Force the portable lowering (-DOAK_PORTABLE_INTRINSICS): on an
	// arm64 host cc compiles the real mrs/msr, so the fail-closed branch
	// must be selected explicitly — the same host-independence rule the
	// barrier and MMIO tests follow.
	cmd := exec.Command(cc, "-std=c11", "-O2", "-DOAK_PORTABLE_INTRINSICS", "-c", cPath, "-o", oPath)
	output, err := cmd.CombinedOutput()
	if err == nil {
		t.Fatal("host compilation of system-register operation unexpectedly succeeded")
	}
	if !strings.Contains(string(output), "requires an AArch64 target") {
		t.Fatalf("host failure did not explain AArch64 system-register requirement:\n%s\n--- C ---\n%s", output, generated)
	}
}
