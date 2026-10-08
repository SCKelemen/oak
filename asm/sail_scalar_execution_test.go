package asm

import (
	"bytes"
	"crypto/sha256"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
)

func TestSailScalarExecutionRawPins(t *testing.T) {
	for name, want := range map[string]string{
		"Raw.lean":     "db0b8ed93db97925f152d508f3c2020230c13c09cf5ea29942a4666d3df24f83",
		"RawDefs.lean": "4599759ae12f5aff5af70c4fcc35fb4fff1d56bbfa6ef94c8997426fedaeac01",
	} {
		data, err := os.ReadFile(filepath.Join("..", "spec", "sail", "lean", "ScalarExecution", name))
		if err != nil {
			t.Fatal(err)
		}
		if got := fmt.Sprintf("%x", sha256.Sum256(data)); got != want {
			t.Fatalf("%s raw export changed: %s", name, got)
		}
	}
}

// Regeneration checks copied upstream declarations/clauses and raw Sail output,
// not merely a substring containing the intended arithmetic operation.
func TestSailScalarExecutionRegeneration(t *testing.T) {
	if _, err := exec.LookPath("sail"); err != nil {
		requireOracle(t, "pinned Sail generator missing: "+err.Error())
	}
	if _, err := os.Stat(filepath.Join("..", "external", "sail-arm", "arm-v8.5-a", "model", "aarch64.sail")); err != nil {
		requireOracle(t, "pinned Arm source missing: "+err.Error())
	}
	out := t.TempDir()
	cmd := exec.Command("python3", filepath.Join("..", "spec", "sail", "scalar_execution_regen.py"), "--output-dir", out)
	if output, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("scalar regeneration: %v\n%s", err, output)
	}
	for _, name := range []string{"scalar_execution.sail", "scalar_execution_vector.sail", "lean/ScalarExecution/Raw.lean", "lean/ScalarExecution/RawDefs.lean", "lean/ScalarExecution/Generated.lean", "lean/ScalarExecution/Defs.lean"} {
		got, err := os.ReadFile(filepath.Join(out, name))
		if err != nil {
			t.Fatal(err)
		}
		want, err := os.ReadFile(filepath.Join("..", "spec", "sail", name))
		if err != nil {
			t.Fatal(err)
		}
		if !bytes.Equal(got, want) {
			t.Fatalf("%s drifted from pinned source/compiler output", name)
		}
	}
}

func TestSailScalarExecutionLean(t *testing.T) {
	if _, err := exec.LookPath("lake"); err != nil {
		requireOracle(t, "Lean missing: "+err.Error())
	}
	cmd := exec.Command("lake", "build", "ScalarExecutionBridge")
	cmd.Dir = filepath.Join("..", "spec", "sail", "lean")
	if output, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("scalar external proof: %v\n%s", err, output)
	}
}
