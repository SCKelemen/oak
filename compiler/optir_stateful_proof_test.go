package compiler

import (
	"context"
	"crypto/sha256"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// This proof consumes a freshly checked and exported actual CFG. The committed
// generated file is a development snapshot only; it is never proof authority
// for the equipped test. No OptIR optimization or target adapter is enabled.
func TestLeanStatefulCopyRawProof(t *testing.T) {
	// Exercise realistic long checkout/package paths on every equipped run.
	// Keep the full absolute source identity; do not normalize it into a hash.
	fixture := statefulCopySource(t)
	root := filepath.Join(t.TempDir(), "ordinary-checkout-layout", "source-identity-portability", strings.Repeat("long-package-directory-", 4))
	if err := os.MkdirAll(root, 0755); err != nil {
		t.Fatal(err)
	}
	for name, text := range map[string]string{
		"oak.mod":  "module example.com/stateful-copy-contract\noak 0.1.0\n",
		"main.oak": fixture,
	} {
		if err := os.WriteFile(filepath.Join(root, name), []byte(text), 0644); err != nil {
			t.Fatal(err)
		}
	}
	rootFile := filepath.Join(root, "main.oak")
	if len(rootFile) < 180 {
		t.Fatal("source identity portability control is not long enough")
	}
	artifact, err := New().WithPackageDir(root).StatefulCopyOptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	if sources := artifact.Sources(); len(sources) != 3 || sources[1].Package != "example.com/stateful-copy-contract" || sources[1].Path != rootFile || sources[1].Text != fixture {
		t.Fatal("full long source identity was not retained")
	}
	t.Logf("exact long source identity (%d bytes): %s", len(rootFile), rootFile)
	lean, err := artifact.ExportLean()
	if err != nil {
		t.Fatal(err)
	}
	data, err := artifact.ExportJSON()
	if err != nil {
		t.Fatal(err)
	}
	if err := artifact.ValidateExportJSON(data); err != nil {
		t.Fatal(err)
	}
	leanHash := fmt.Sprintf("%x", sha256.Sum256([]byte(lean)))
	jsonHash := fmt.Sprintf("%x", sha256.Sum256(data))
	t.Logf("fresh checked raw-CFG Lean sha256 %s; full export JSON sha256 %s", leanHash, jsonHash)
	if evidence := os.Getenv("OAK_STATEFUL_RAW_PROOF_EVIDENCE"); evidence != "" {
		if err := os.MkdirAll(evidence, 0755); err != nil {
			t.Fatal(err)
		}
		for name, contents := range map[string][]byte{leanHash + ".lean": []byte(lean), jsonHash + ".json": data} {
			if err := os.WriteFile(filepath.Join(evidence, name), contents, 0644); err != nil {
				t.Fatal(err)
			}
		}
	}

	if strings.Contains(lean, "sorry") {
		t.Fatal("raw generated module contains a proof placeholder")
	}
	lake := findLake()
	if lake == "" {
		if os.Getenv("OAK_REQUIRE_STATEFUL_COPY_OPTIR_LEAN") == "1" {
			t.Fatal("OAK_REQUIRE_STATEFUL_COPY_OPTIR_LEAN=1 requires pinned Lean")
		}
		t.Skip("lake unavailable; equipped raw-CFG gate requires fresh kernel proof")
	}
	python, err := exec.LookPath("python3")
	if err != nil {
		t.Fatal("raw-CFG proof requires python3")
	}
	dir := t.TempDir()
	generated := filepath.Join(dir, "OptIRStatefulCopyGenerated.lean")
	jsonPath := filepath.Join(dir, "raw.json")
	if err := os.WriteFile(generated, []byte(lean), 0644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(jsonPath, data, 0644); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 8*time.Minute)
	defer cancel()
	for _, args := range [][]string{
		{"-B", "-m", "unittest", "discover", "-s", "tools/stateful_copy_optir_proof", "-p", "test_check.py"},
		{"-B", "tools/stateful_copy_optir_proof/check.py", "--lake", lake, "--generated", generated, "--export-json", jsonPath},
	} {
		cmd := exec.CommandContext(ctx, python, args...)
		cmd.Dir = ".."
		cmd.WaitDelay = 5 * time.Second
		cmd.Env = append(os.Environ(), "OAK_RAW_GATE_TEST_GENERATED="+generated, "OAK_RAW_GATE_TEST_JSON="+jsonPath)
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("fresh actual raw-CFG proof %v failed: %v\n%s", args, err, out)
		}
		t.Log(string(out))
	}
}
