package asm

import (
	"os"
	"os/exec"
	"path/filepath"
	"testing"
)

// This is an explicit known-discrepancy audit, not a passing source-equivalence
// test. It freezes the defect and independently exercises the admitted subset.
func TestSailScalarExecutionGuardedMutationAudit(t *testing.T) {
	for _, name := range []string{"sail", "lake", "python3"} {
		if _, err := exec.LookPath(name); err != nil {
			requireOracle(t, name+" required for exporter audit: "+err.Error())
		}
	}
	if _, err := os.Stat(filepath.Join("..", "external", "sail-arm", "arm-v8.5-a", "model", "aarch_mem.sail")); err != nil {
		requireOracle(t, "pinned Arm source required: "+err.Error())
	}
	cmd := exec.Command("python3", filepath.Join("..", "spec", "sail", "repros", "guarded_mutation", "check.py"), "--output-dir", t.TempDir())
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("known exporter discrepancy/selected-path audit: %v\n%s", err, out)
	} else {
		t.Log(string(out))
	}
}
