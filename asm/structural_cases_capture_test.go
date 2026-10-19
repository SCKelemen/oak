package asm

import (
	"compress/gzip"
	"crypto/sha256"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// This is the complete captured result obligation, preserving DAG sharing,
// widths, raw/canonical roots and the nil domain. No source recompilation or
// candidate reconstruction is needed to replay the actual checker input.
func capturedStructuralCaseResult(t *testing.T) ([]*term, map[string]int) {
	return capturedStructuralCaseDAG(t, "structural_cases_status_word.dag.gz", "3b3ae62b07fd3fb305f6a286e4eae89c9d269744d7910d38da35f13351a2d3d0", []string{"kind", "le.bytes_at", "le.state_at", "le.strs_at"})
}

func capturedStructuralCaseMemory(t *testing.T) ([]*term, map[string]int) {
	return capturedStructuralCaseDAG(t, "structural_cases_status_word_memory.dag.gz", "4c36ee5210db0887ba49611847bc04536531d92549e4434cc4c549c7545642e6", []string{"ew[?]", "kind", "le.bytes_at", "le.state_at", "le.strs_at"})
}

func capturedStructuralCaseDAG(t *testing.T, name, digest string, names []string) ([]*term, map[string]int) {
	t.Helper()
	f, err := os.Open(filepath.Join("testdata", name))
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	z, err := gzip.NewReader(f)
	if err != nil {
		t.Fatal(err)
	}
	defer z.Close()
	b, err := io.ReadAll(io.LimitReader(z, 1<<20))
	if err != nil {
		t.Fatal(err)
	}
	if got := fmt.Sprintf("%x", sha256.Sum256(b)); got != digest {
		t.Fatalf("captured DAG digest changed: %s", got)
	}
	p := filepath.Join(t.TempDir(), "result.dag")
	if err := os.WriteFile(p, b, 0600); err != nil {
		t.Fatal(err)
	}
	roots, widths, err := readTermDAG(p)
	if err != nil {
		t.Fatal(err)
	}
	if len(roots) != 5 || roots[4] != nil || len(widths) != len(names) {
		t.Fatal("capture roots/domain/declarations changed")
	}
	for _, name := range names {
		if widths[name] != 32 {
			t.Fatalf("%s width = %d", name, widths[name])
		}
	}
	return roots, widths
}

func TestStructuralCasesCapturedMemory(t *testing.T) {
	roots, widths := capturedStructuralCaseMemory(t)
	for _, swap := range []bool{false, true} {
		for _, reverse := range []bool{false, true} {
			a, b := roots[2], roots[3]
			if swap {
				a, b = b, a
			}
			s := newStructuralCases(structuralCaseLimits{1 << 16, 1 << 17, 1 << 20, 4})
			s.reverse = reverse
			start := time.Now()
			if !s.equal(a, b) || s.leaves != 5 {
				t.Fatalf("captured memory remains unknown: swap=%v reverse=%v nodes=%d work=%d leaves=%d exhausted=%v", swap, reverse, len(s.nodes), s.work, s.leaves, s.exhausted)
			}
			t.Logf("captured memory proved structurally: swap=%v reverse=%v duration=%s nodes=%d work=%d leaves=%d", swap, reverse, time.Since(start), len(s.nodes), s.work, s.leaves)
			negative := newStructuralCases(structuralCaseLimits{1 << 16, 1 << 17, 1 << 20, 4})
			negative.reverse = reverse
			if negative.equal(binaryTerm("xor", a, constTerm(1, 32)), b) {
				t.Fatal("direct structural helper accepted changed whole-memory value")
			}
		}
	}
	lo := &oakLowering{params: widths, spans: map[string]spanContract{"ew": {elemWidth: 32}}}
	fn := &Function{Name: "status_word"}
	start := time.Now()
	v := decideEqual(fn, lo, roots[0], roots[1], 32, "")
	if v.Kind != VerdictProven || !strings.Contains(v.Message, "structural branch case") {
		t.Fatalf("captured memory decision: %s: %s", v.Kind, v.Message)
	}
	t.Logf("captured memory checker including unchanged witnesses: %s", time.Since(start))
	v = decideEqual(fn, lo, binaryTerm("xor", roots[0], constTerm(1, 32)), roots[1], 32, "")
	if v.Kind != VerdictMismatch || !strings.Contains(v.Message, "asm yields") || strings.Contains(v.Message, "(bit ") {
		t.Fatalf("mutated memory was not refuted by witnesses: %s: %s", v.Kind, v.Message)
	}
}

func TestStructuralCasesCapturedStatusWord(t *testing.T) {
	roots, _ := capturedStructuralCaseResult(t)
	for _, swap := range []bool{false, true} {
		for _, reverse := range []bool{false, true} {
			a, b := roots[2], roots[3]
			if swap {
				a, b = b, a
			}
			s := newStructuralCases(structuralCaseLimits{1 << 16, 1 << 17, 1 << 20, 4})
			s.reverse = reverse
			start := time.Now()
			if !s.equal(a, b) {
				t.Fatalf("captured result remains unknown: swap=%v reverse=%v nodes=%d work=%d leaves=%d exhausted=%v", swap, reverse, len(s.nodes), s.work, s.leaves, s.exhausted)
			}
			if s.leaves != 5 {
				t.Fatalf("got %d leaves, want the five exhaustive captured cases", s.leaves)
			}
			t.Logf("captured result proved structurally: swap=%v reverse=%v duration=%s nodes=%d work=%d leaves=%d", swap, reverse, time.Since(start), len(s.nodes), s.work, s.leaves)
		}
	}
}

func TestStructuralCasesCapturedDecision(t *testing.T) {
	roots, widths := capturedStructuralCaseResult(t)
	lo := &oakLowering{params: widths, spans: map[string]spanContract{"ew": {elemWidth: 32}}}
	fn := &Function{Name: "status_word"}
	start := time.Now()
	v := decideEqual(fn, lo, roots[0], roots[1], 32, "")
	if v.Kind != VerdictProven || !strings.Contains(v.Message, "structural branch case") {
		t.Fatalf("captured result decision: %s: %s", v.Kind, v.Message)
	}
	t.Logf("captured result checker including unchanged witnesses: %s", time.Since(start))
	// Every input differs after this mutation; the existing witness path must
	// reject it before a structural shortcut can report a proof.
	v = decideEqual(fn, lo, binaryTerm("xor", roots[0], constTerm(1, 32)), roots[1], 32, "")
	if v.Kind != VerdictMismatch || !strings.Contains(v.Message, "asm yields") || !strings.Contains(v.Message, "Oak yields") || strings.Contains(v.Message, "(bit ") {
		t.Fatalf("mutated result was not refuted by witnesses: %s: %s", v.Kind, v.Message)
	}
}
