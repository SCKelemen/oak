package codegen

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

const aarch64EventControlSource = `
package main
fn mask_irq() -> ()
  arm64.daifset_irq()
fn unmask_irq() -> ()
  arm64.daifclr_irq()
fn wait_irq() -> ()
  arm64.wfi()
fn wait_event() -> ()
  arm64.wfe()
fn send_event() -> ()
  arm64.sev()
`

func compileEventControlAArch64Assembly(t *testing.T) (generated, assembly string) {
	t.Helper()
	clang := requireAArch64Clang(t)
	generated = generateSourceC(t, aarch64EventControlSource)
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "free("} {
		if strings.Contains(generated, forbidden) {
			t.Fatalf("event-control path unexpectedly references heap primitive %q", forbidden)
		}
	}
	dir := t.TempDir()
	cPath := filepath.Join(dir, "event_control.c")
	sPath := filepath.Join(dir, "event_control.s")
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
		t.Fatalf("cross-compile event-control C: %v\n%s\n--- C ---\n%s", err, output, generated)
	}
	bytes, err := os.ReadFile(sPath)
	if err != nil {
		t.Fatal(err)
	}
	return generated, strings.ToLower(string(bytes))
}

func TestAArch64EventControlInstructionRefinement(t *testing.T) {
	_, assembly := compileEventControlAArch64Assembly(t)
	cases := []struct {
		fn   string
		want string
	}{
		{"mask_irq", "msr\tdaifset, #2"},
		{"unmask_irq", "msr\tdaifclr, #2"},
		{"wait_irq", "wfi"},
		{"wait_event", "wfe"},
		{"send_event", "sev"},
	}
	for _, tc := range cases {
		t.Run(tc.fn, func(t *testing.T) {
			body := aarch64FunctionBody(t, assembly, tc.fn)
			if !strings.Contains(body, tc.want) && !strings.Contains(body, strings.ReplaceAll(tc.want, "\t", " ")) {
				t.Fatalf("%s lacks %q:\n%s", tc.fn, tc.want, body)
			}
			for _, forbidden := range []string{"dmb", "dsb", "isb"} {
				if hasInstruction(body, forbidden) {
					t.Fatalf("%s unexpectedly contains hidden %s:\n%s", tc.fn, forbidden, body)
				}
			}
		})
	}
}

func TestAArch64EventControlGeneratedCFailsClosedOnHost(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("host C compiler is not available")
	}
	generated := generateSourceC(t, `
package main
fn wait() -> ()
  arm64.wfi()
`)
	dir := t.TempDir()
	cPath := filepath.Join(dir, "event_control.c")
	oPath := filepath.Join(dir, "event_control.o")
	if err := os.WriteFile(cPath, []byte(generated), 0o600); err != nil {
		t.Fatal(err)
	}
	output, err := exec.Command(cc, "-std=c11", "-O2", "-DOAK_PORTABLE_INTRINSICS", "-c", cPath, "-o", oPath).CombinedOutput()
	if err == nil {
		t.Fatal("host compilation of architectural event control unexpectedly succeeded")
	}
	if !strings.Contains(string(output), "arm64.wfi requires an AArch64 target") {
		t.Fatalf("host failure did not explain AArch64 requirement:\n%s", output)
	}
}
