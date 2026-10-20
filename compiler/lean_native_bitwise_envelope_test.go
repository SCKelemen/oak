package compiler

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/stdlib"
)

// All three reachable functions are generated directly from the current
// type-checked source. No hand editing, filtering or helper substitution occurs.
func TestLeanNativeBitwiseEnvelopeExtract(t *testing.T) {
	source := selfhostBitwiseELFSource(t)
	extracted, err := New().WithSource("bitwise_elf.oak", stdlib.Prelude+"\n"+source).
		EmitLeanRoots("Oak.BitwiseELFProducer", topLevelNames(t, source)).Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(extracted, "sorry") {
		t.Fatal("native envelope extraction contains sorry")
	}
	path := filepath.Join("..", "spec", "lean", "Oak", "NativeBitwiseEnvelopeExtracted.lean")
	if os.Getenv("OAK_LEAN_EXTRACT_UPDATE") == "1" {
		if err := os.WriteFile(path, []byte(extracted), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	committed, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	if string(committed) != extracted {
		t.Fatal("NativeBitwiseEnvelopeExtracted.lean is stale; regenerate with OAK_LEAN_EXTRACT_UPDATE=1")
	}
}

// This gate rebuilds the entire local proof closure from current source into an
// isolated directory, trust zero and one Lean worker, then audits exact exported
// theorem roots. It cannot pass by loading old candidate .olean files.
func TestLeanNativeBitwiseEnvelopeProof(t *testing.T) {
	TestLeanNativeBitwiseEnvelopeExtract(t)
	lake := findLake()
	if lake == "" {
		if os.Getenv("OAK_REQUIRE_SELFHOST_IMAGE_PRODUCERS") == "1" {
			t.Fatal("OAK_REQUIRE_SELFHOST_IMAGE_PRODUCERS=1 requires lake for native envelope proof")
		}
		t.Skip("lake unavailable; equipped lane requires the native envelope proof")
	}
	python, err := exec.LookPath("python3")
	if err != nil {
		t.Fatal("native envelope proof requires python3")
	}
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Minute)
	defer cancel()
	cmd := exec.CommandContext(ctx, python, "tools/native_envelope_proof/check.py", "--lake", lake)
	cmd.Dir = ".."
	cmd.WaitDelay = 5 * time.Second
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("fresh native envelope proof failed: %v\n%s", err, out)
	}
	t.Log(string(out))
}
