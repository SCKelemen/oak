package compiler

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// This gate joins extraction *consistency* and source/layout regression evidence
// to a kernel proof of lifted extracted semantics. It does not prove frontend,
// compiler, machine ABI transport, or instruction execution correctness.
func TestLeanStatefulCopyProof(t *testing.T) {
	// Regenerate the existing bytes module through its ordinary extraction path.
	// Never rewrite the committed module, even under OAK_LEAN_EXTRACT_UPDATE.
	source, roots := leanStdlibProgram(t, "bytes", nil, "", "")
	extracted, err := New().WithSource("stdlib_bytes.oak", source).
		EmitLeanRoots("Oak.Stdlib.Bytes", roots).Get()
	if err != nil {
		t.Fatal(err)
	}
	committed, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "Stdlib", "BytesExtracted.lean"))
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(extracted, "sorry") || extracted != string(committed) {
		t.Fatal("stateful-copy extraction differs from the frozen bytes module")
	}
	lake := findLake()
	if lake == "" {
		if os.Getenv("OAK_REQUIRE_STATEFUL_COPY_LEAN") == "1" {
			t.Fatal("OAK_REQUIRE_STATEFUL_COPY_LEAN=1 requires the pinned Lean toolchain")
		}
		t.Skip("lake unavailable; equipped stateful-copy lane requires fresh kernel proof")
	}
	python, err := exec.LookPath("python3")
	if err != nil {
		t.Fatal("stateful-copy proof requires python3")
	}
	ctx, cancel := context.WithTimeout(t.Context(), 5*time.Minute)
	defer cancel()
	for _, args := range [][]string{
		{"-B", "-m", "unittest", "discover", "-s", "tools/stateful_copy_proof", "-p", "test_check.py"},
		{"-B", "tools/stateful_copy_proof/check.py", "--lake", lake},
	} {
		cmd := exec.CommandContext(ctx, python, args...)
		cmd.Dir = ".."
		cmd.WaitDelay = 5 * time.Second
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("fresh stateful-copy proof %v failed: %v\n%s", args, err, out)
		}
		t.Log(string(out))
	}
}
