package compiler

import (
	"context"
	"os/exec"
	"testing"
	"time"
)

// Called by the already-required Faithful gate after fresh extraction checking.
// The total-outcome superset retains both root inventories and both control
// files. Every local import is rebuilt in an isolated directory with trust
// zero; no candidate .olean cache can satisfy either universal proof.
func testLeanWasmBitwiseModuleProof(t *testing.T, lake string) {
	t.Helper()
	python, err := exec.LookPath("python3")
	if err != nil {
		t.Fatal("Wasm module proof requires python3")
	}
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Minute)
	defer cancel()
	for _, args := range [][]string{
		{"-m", "unittest", "discover", "-s", "tools/wasm_module_proof", "-p", "test_check.py"},
		{"-m", "unittest", "discover", "-s", "tools/wasm_module_total_proof", "-p", "test_check.py"},
		{"tools/wasm_module_total_proof/check.py", "--lake", lake},
	} {
		cmd := exec.CommandContext(ctx, python, args...)
		cmd.Dir = ".."
		cmd.WaitDelay = 5 * time.Second
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("fresh Wasm module proof %v failed: %v\n%s", args, err, out)
		}
		t.Log(string(out))
	}
}
