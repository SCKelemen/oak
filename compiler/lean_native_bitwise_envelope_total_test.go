package compiler

import (
	"context"
	"os"
	"os/exec"
	"testing"
	"time"
)

// This gate rebuilds the entire local proof closure from current source into an
// isolated directory, trust zero and one Lean worker, then audits exact exported
// theorem roots. It cannot pass by loading old candidate .olean files.
func TestLeanNativeBitwiseEnvelopeTotalProof(t *testing.T) {
	TestLeanNativeBitwiseEnvelopeExtract(t)
	lake := findLake()
	if lake == "" {
		if os.Getenv("OAK_REQUIRE_SELFHOST_IMAGE_PRODUCERS") == "1" {
			t.Fatal("OAK_REQUIRE_SELFHOST_IMAGE_PRODUCERS=1 requires lake for native envelope total-outcome proof")
		}
		t.Skip("lake unavailable; equipped lane requires the native envelope total-outcome proof")
	}
	python, err := exec.LookPath("python3")
	if err != nil {
		t.Fatal("native envelope total-outcome proof requires python3")
	}
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Minute)
	defer cancel()
	cmd := exec.CommandContext(ctx, python, "tools/native_envelope_total_proof/check.py", "--lake", lake)
	cmd.Dir = ".."
	cmd.WaitDelay = 5 * time.Second
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("fresh native envelope total-outcome proof failed: %v\n%s", err, out)
	}
	t.Log(string(out))
}
