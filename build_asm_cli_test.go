package main

import (
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"testing"
)

// The build command links asm units exactly once in every asm mode. In the
// default native mode the units live in the companion object and the C
// carries only their prototypes, so the executable must be compiled from
// the native emitter's C — not from the inline-assembly C that -emit-c
// writes, which would define every unit's symbol a second time beside the
// object (the storage engine's fourth-round request 6).
func TestBuildAsmUnitsLinkOnceInEveryMode(t *testing.T) {
	if runtime.GOARCH != "arm64" {
		t.Skip("the asm example targets AArch64")
	}
	for _, args := range [][]string{nil, {"-native"}, {"-asm", "native"}, {"-asm", "c"}, {"-native", "-asm", "c"}} {
		bin := filepath.Join(t.TempDir(), "asm_example")
		flags := append(append([]string{}, args...), "-o", bin, "examples/asm")
		if code, out := runCLI(t, buildPackage, flags); code != 0 || !strings.Contains(out, "Built") {
			t.Fatalf("build %v: exit %d\n%s", args, code, out)
		}
		if code := exitCode(t, exec.Command(bin).Run()); code != 42 {
			t.Fatalf("build %v: executable exit = %d, want 42", args, code)
		}
	}
}
