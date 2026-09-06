package serialize

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

const repoGoldenDir = "../golden"

// TestGoldenCorpusMatches regenerates every corpus case and compares each
// compiler stage against the recorded golden files, so pipeline drift fails
// go test instead of rotting silently. Regenerate deliberately with
// go run ./cmd/generate_golden after reviewing the diff.
func TestGoldenCorpusMatches(t *testing.T) {
	for _, tc := range GoldenCases() {
		t.Run(tc.Name, func(t *testing.T) {
			if tc.Skip {
				t.Skip("case marked as known issue")
			}
			mismatches, err := VerifyGoldenCase(tc, repoGoldenDir, filepath.Join(t.TempDir(), tc.Name))
			if err != nil {
				t.Fatal(err)
			}
			if len(mismatches) > 0 {
				t.Fatalf("golden drift (regenerate deliberately after review):\n  %s",
					strings.Join(mismatches, "\n  "))
			}
		})
	}
}

// TestGoldenCOutputSanity pins load-bearing properties of the generated C:
// block bodies keep their locals and self tail recursion is loop-lowered.
func TestGoldenCOutputSanity(t *testing.T) {
	mustRead := func(name string) string {
		t.Helper()
		data, err := os.ReadFile(filepath.Join(repoGoldenDir, name))
		if err != nil {
			t.Fatalf("missing golden C file (run go run ./cmd/generate_golden): %v", err)
		}
		return string(data)
	}

	blockBody := mustRead("block_body_function_7_codegen.c")
	if !strings.Contains(blockBody, "doubled") {
		t.Fatalf("block-body locals missing from generated C:\n%s", blockBody)
	}

	tail := mustRead("tail_recursion_7_codegen.c")
	if !strings.Contains(tail, "while (1)") || !strings.Contains(tail, "continue;") {
		t.Fatalf("tail recursion not loop-lowered in generated C:\n%s", tail)
	}
	if strings.Contains(tail, "return oak_countdown") {
		t.Fatalf("tail self-call emitted as a recursive call:\n%s", tail)
	}
}

// TestGoldenCCompiles syntax-checks every golden C file with the system C
// compiler when one is available: the corpus is the trust anchor that the
// backend emits valid C.
func TestGoldenCCompiles(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("no C compiler on PATH")
	}
	entries, err := os.ReadDir(repoGoldenDir)
	if err != nil {
		t.Fatal(err)
	}
	for _, entry := range entries {
		if !strings.HasSuffix(entry.Name(), "_codegen.c") {
			continue
		}
		name := entry.Name()
		t.Run(name, func(t *testing.T) {
			cmd := exec.Command(cc, "-fsyntax-only", "-std=c99", filepath.Join(repoGoldenDir, name))
			out, err := cmd.CombinedOutput()
			if err != nil {
				t.Fatalf("golden C does not compile: %v\n%s", err, out)
			}
		})
	}
}
