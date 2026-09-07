package codegen

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

const aarch64BarrierSource = `
package main

fn barrier_dmb_ishld() -> ()
  arm64.dmb_ishld()

fn barrier_dmb_ish() -> ()
  arm64.dmb_ish()

fn barrier_dmb_sy() -> ()
  arm64.dmb_sy()

fn barrier_dsb_ish() -> ()
  arm64.dsb_ish()

fn barrier_dsb_sy() -> ()
  arm64.dsb_sy()

fn barrier_isb() -> ()
  arm64.isb()
`

func compileBarrierAArch64Assembly(t *testing.T) (generated, assembly string) {
	t.Helper()
	clang := requireAArch64Clang(t)
	generated = generateSourceC(t, aarch64BarrierSource)

	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "free("} {
		if strings.Contains(generated, forbidden) {
			t.Fatalf("generated barrier path unexpectedly references heap primitive %q:\n%s", forbidden, generated)
		}
	}
	if strings.Contains(generated, "OAK_PORTABLE_INTRINSICS") && !strings.Contains(generated, "#error \"arm64.") {
		t.Fatalf("barrier lowering contains portable path without fail-closed #error:\n%s", generated)
	}

	dir := t.TempDir()
	cPath := filepath.Join(dir, "barriers.c")
	sPath := filepath.Join(dir, "barriers.s")
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
		t.Fatalf("cross-compile generated barrier C: %v\n%s\n--- C ---\n%s", err, output, generated)
	}
	bytes, err := os.ReadFile(sPath)
	if err != nil {
		t.Fatal(err)
	}
	return generated, strings.ToLower(string(bytes))
}

func TestAArch64BarrierInstructionRefinement(t *testing.T) {
	_, assembly := compileBarrierAArch64Assembly(t)

	cases := []struct {
		fn          string
		mnemonic    string
		operandText string
	}{
		{"barrier_dmb_ishld", "dmb", "ishld"},
		{"barrier_dmb_ish", "dmb", "ish"},
		{"barrier_dmb_sy", "dmb", "sy"},
		{"barrier_dsb_ish", "dsb", "ish"},
		{"barrier_dsb_sy", "dsb", "sy"},
		{"barrier_isb", "isb", ""},
	}

	for _, tc := range cases {
		t.Run(tc.fn, func(t *testing.T) {
			body := aarch64FunctionBody(t, assembly, tc.fn)
			requireInstruction(t, body, tc.mnemonic)
			if tc.operandText != "" && !strings.Contains(body, tc.mnemonic+"\t"+tc.operandText) &&
				!strings.Contains(body, tc.mnemonic+" "+tc.operandText) {
				t.Fatalf("%s lacks exact barrier operand %s:\n%s", tc.fn, tc.operandText, body)
			}
			for _, other := range []string{"dmb", "dsb", "isb"} {
				if other != tc.mnemonic && hasInstruction(body, other) {
					t.Fatalf("%s unexpectedly contains additional barrier %s:\n%s", tc.fn, other, body)
				}
			}
		})
	}
}

func TestAArch64BarrierGeneratedCFailsClosedOnHost(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("host C compiler is not available")
	}
	generated := generateSourceC(t, `
package main
fn barrier() -> ()
  arm64.dsb_sy()
`)
	dir := t.TempDir()
	cPath := filepath.Join(dir, "barrier.c")
	oPath := filepath.Join(dir, "barrier.o")
	if err := os.WriteFile(cPath, []byte(generated), 0o600); err != nil {
		t.Fatal(err)
	}
	// Force the non-AArch64 branch regardless of the host architecture
	// (-DOAK_PORTABLE_INTRINSICS, the same switch the differential
	// execution tests use): barriers must fail closed with #error rather
	// than acquire a fake portable lowering. On an actual AArch64 host the
	// unforced build correctly compiles to the real instruction.
	cmd := exec.Command(cc, "-std=c11", "-O2", "-DOAK_PORTABLE_INTRINSICS", "-c", cPath, "-o", oPath)
	output, err := cmd.CombinedOutput()
	if err == nil {
		t.Fatal("non-AArch64 compilation of architectural barrier unexpectedly succeeded")
	}
	if !strings.Contains(string(output), "arm64.dsb_sy requires an AArch64 target") {
		t.Fatalf("host failure did not explain AArch64 barrier requirement:\n%s\n--- C ---\n%s", output, generated)
	}
}
