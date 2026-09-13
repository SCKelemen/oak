package main

import (
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// `-opt N` sets the C compiler's optimization level for the executable
// (docs/spec/05-ergonomics-and-cost.md, the mechanical backend): the same
// C builds and runs at every level, so the -O0 versus -O2 delta on a hot
// loop measures the backend's contribution alone. An unknown level is
// refused before anything is built.
func TestBuildOptLevel(t *testing.T) {
	for _, level := range []string{"0", "2", "3"} {
		bin := filepath.Join(t.TempDir(), "asm_example")
		if code, out := runCLI(t, buildPackage, []string{"-opt", level, "-o", bin, "examples/asm"}); code != 0 || !strings.Contains(out, "Built") {
			t.Fatalf("-opt %s: exit %d\n%s", level, code, out)
		}
		if code := exitCode(t, exec.Command(bin).Run()); code != 42 {
			t.Fatalf("-opt %s: the program exited %d, want 42", level, code)
		}
	}
	cOptLevel = 1
	if code, out := runCLI(t, buildPackage, []string{"-opt", "7", "-o", filepath.Join(t.TempDir(), "x"), "examples/asm"}); code != 2 || !strings.Contains(out, "-opt: expected an optimization level") {
		t.Fatalf("-opt 7 must be refused with exit 2: %d\n%s", code, out)
	}
	if level, ok := parseOptLevel("2"); !ok || level != 2 {
		t.Fatalf("parseOptLevel(2) = %d %v", level, ok)
	}
	if _, ok := parseOptLevel("fast"); ok {
		t.Fatal("parseOptLevel must refuse -Ofast: fast-math is never passed")
	}
}
