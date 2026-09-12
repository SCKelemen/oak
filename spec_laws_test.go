package main

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// The self-hosted laws (docs/spec/125-verification.md section 6): every
// theorem under spec/oak — the single files and the standard-library
// packages — is decided by the compiler, except the files named
// *_lean.oak, which Lean proves from the projection when a Lean toolchain
// is present.
func TestSelfHostedLaws(t *testing.T) {
	files, err := filepath.Glob(filepath.Join("spec", "oak", "*.oak"))
	if err != nil || len(files) == 0 {
		t.Fatalf("spec/oak: %v (%d files)", err, len(files))
	}
	// The standard-library laws import the library, so they are packages.
	packages, _ := filepath.Glob(filepath.Join("spec", "oak", "*", "main.oak"))
	for _, main := range packages {
		files = append(files, filepath.Dir(main))
	}
	for _, file := range files {
		file := file
		t.Run(filepath.Base(file), func(t *testing.T) {
			// The decided files are also witnessed in the compiled program.
			args := []string{"-witness", file}
			if strings.HasSuffix(file, "_lean.oak") {
				lean := leanBinary(t)
				args = []string{"-lean", filepath.Join(t.TempDir(), "laws.lean"), "-check", "-lean-binary", lean, file}
			}
			code, out := runCLI(t, func(args []string) int { return proveCommand(args, os.Stdout, os.Stderr) }, args)
			if code != 0 || strings.Contains(out, "open ") || strings.Contains(out, "refuted ") {
				t.Fatalf("exit %d:\n%s", code, out)
			}
		})
	}
}

// leanBinary finds Lean (PATH, then ~/.elan/bin) and pins the toolchain
// the specification builds with, or skips.
func leanBinary(t *testing.T) string {
	t.Helper()
	lean, err := exec.LookPath("lean")
	if err != nil {
		home, _ := os.UserHomeDir()
		lean = filepath.Join(home, ".elan", "bin", "lean")
		if _, statErr := os.Stat(lean); statErr != nil {
			t.Skip("lean not found (PATH or ~/.elan/bin); the Lean-proved laws need the toolchain")
		}
	}
	if pinned, err := os.ReadFile(filepath.Join("spec", "lean", "lean-toolchain")); err == nil {
		t.Setenv("ELAN_TOOLCHAIN", strings.TrimSpace(string(pinned)))
	}
	return lean
}
