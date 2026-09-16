package asm

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"testing"
	"time"
)

// checkNativeCNFLean runs the actual Lean process under the deadline, not a
// lake wrapper whose child can remain evaluating after the wrapper is killed.
func checkNativeCNFLean(t *testing.T, filename, source string) {
	t.Helper()
	lake, err := exec.LookPath("lake")
	if err != nil {
		requireOracle(t, "lake not on PATH; the formal workflow runs this kernel oracle")
	}
	path := filepath.Join(t.TempDir(), filename)
	if err := os.WriteFile(path, []byte(source), 0o600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 90*time.Second)
	defer cancel()
	environment := exec.CommandContext(ctx, lake, "env")
	environment.Dir = filepath.Join("..", "spec", "lean")
	environment.WaitDelay = 2 * time.Second
	envOutput, err := environment.Output()
	if err != nil {
		t.Fatalf("resolving Lean environment: %v", err)
	}
	variables := strings.Split(strings.TrimSuffix(string(envOutput), "\n"), "\n")
	var sysroot string
	for i, variable := range variables {
		variable = strings.TrimSuffix(variable, "\r")
		variables[i] = variable
		if value, found := strings.CutPrefix(variable, "LEAN_SYSROOT="); found {
			sysroot = value
		}
	}
	if sysroot == "" {
		t.Fatal("Lake did not report LEAN_SYSROOT")
	}
	lean := filepath.Join(sysroot, "bin", "lean")
	if runtime.GOOS == "windows" {
		lean += ".exe"
	}
	command := exec.CommandContext(ctx, lean, path)
	command.Dir = environment.Dir
	command.Env = append(os.Environ(), variables...)
	command.WaitDelay = 2 * time.Second
	if output, err := command.CombinedOutput(); err != nil {
		t.Fatalf("kernel-checking %s: %v (context: %v)\n%s", filename, err, ctx.Err(), output)
	}
}
