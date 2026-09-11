package asm

import (
	"bytes"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
)

// The Sail-to-Lean bridge's generated files are committed
// (spec/sail/lean/Out.lean, spec/sail/lean/Out/); this test regenerates them
// with the installed Sail and requires the committed copy to be identical,
// so the Lean the bridge proofs are stated against is exactly what Sail's
// backend produces from spec/sail/arm_primitives.sail
// (docs/spec/94-assembler.md §8, grounding stage 3). It skips when Sail or
// the support library is absent.
func TestSailLeanGenerationCurrent(t *testing.T) {
	sail, err := exec.LookPath("sail")
	if err != nil {
		// opam installs outside PATH by default.
		home, _ := os.UserHomeDir()
		sail = filepath.Join(home, ".opam", "default", "bin", "sail")
		if _, err := os.Stat(sail); err != nil {
			t.Skip("sail not installed")
		}
	}
	root, err := filepath.Abs(filepath.Join("..", "spec", "sail"))
	if err != nil {
		t.Fatal(err)
	}
	lib, err := filepath.Abs(filepath.Join("..", "..", "external", "lean-sail"))
	if err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(lib); err != nil {
		t.Skip("lean-sail support library not checked out (spec/sail/setup.sh)")
	}
	out := t.TempDir()
	cmd := exec.Command(sail, filepath.Join(root, "arm_primitives.sail"), "--lean", "--lean-single-file",
		"--lean-output-dir", out, "--lean-lib-path", lib)
	cmd.Dir = out // sail writes its SMT cache beside the working directory
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	if err := cmd.Run(); err != nil {
		t.Fatalf("sail: %v\n%s", err, stderr.String())
	}
	for _, name := range []string{"Out.lean", "Out/Defs.lean", "Out/Specialization.lean", "Out/FakeReal.lean"} {
		fresh, err := os.ReadFile(filepath.Join(out, "out", name))
		if err != nil {
			t.Fatal(err)
		}
		committed, err := os.ReadFile(filepath.Join(root, "lean", name))
		if err != nil {
			t.Fatal(err)
		}
		if !bytes.Equal(fresh, committed) {
			t.Errorf("%s: the committed generated Lean differs from what sail produces; run spec/sail/regen.sh", name)
		}
	}
}
