package main

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// Object output (docs/spec/115-tooling.md; the OS pilot's N5): `-o name.o`
// on a hosted target compiles the emitted C to one relocatable object,
// asm units inlined, which a host harness links against its own driver —
// here the system C compiler links it alone, since the object carries
// main, and the program runs. `-asm native` with object output is refused.
func TestBuildObjectOutput(t *testing.T) {
	dir := t.TempDir()
	object := filepath.Join(dir, "asm_example.o")
	if code, out := runCLI(t, buildPackage, []string{"-o", object, "examples/asm"}); code != 0 || !strings.Contains(out, "Built") {
		t.Fatalf("object output: exit %d\n%s", code, out)
	}
	if info, err := os.Stat(object); err != nil || info.Size() == 0 {
		t.Fatalf("no object written: %v", err)
	}
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("no C compiler")
	}
	exe := filepath.Join(dir, "asm_example")
	if out, err := exec.Command(cc, object, "-lm", "-o", exe).CombinedOutput(); err != nil {
		t.Fatalf("linking the object: %v\n%s", err, out)
	}
	if code := exitCode(t, exec.Command(exe).Run()); code != 42 {
		t.Fatalf("the linked program exited %d, want 42", code)
	}
	if code, out := runCLI(t, buildPackage, []string{"-asm", "native", "-o", filepath.Join(dir, "x.o"), "examples/asm"}); code != 2 || !strings.Contains(out, "inlines the asm units") {
		t.Fatalf("-asm native with object output must be refused: %d\n%s", code, out)
	}
}
