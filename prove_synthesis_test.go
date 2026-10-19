package main

import (
	"bytes"
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/prove"
)

func TestProveSynthesisCommand(t *testing.T) {
	source, err := os.ReadFile("examples/verification_synthesis.oak")
	if err != nil {
		t.Fatal(err)
	}
	dir := writeTree(t, map[string]string{
		"laws.oak":        string(source),
		"candidates.json": `["false", "d.x == d.y"]`,
	})
	path := filepath.Join(dir, "laws.oak")
	var out, stderr bytes.Buffer
	code := proveCommand([]string{"-solver", "go", "-cases", "1", "-synthesize", "ordered", "-candidates", filepath.Join(dir, "candidates.json"), "-synthesis-json", path}, &out, &stderr)
	if code != 0 {
		t.Fatalf("exit %d: %s\n%s", code, stderr.String(), out.String())
	}
	var report prove.SynthesisResult
	if err := json.Unmarshal(out.Bytes(), &report); err != nil {
		t.Fatal(err)
	}
	if report.Status != prove.Decided || report.Property != "ordered" || len(report.Checks) != 3 || len(report.Rejected) != 1 {
		t.Fatalf("bad evidence report: %+v", report)
	}
	after, err := os.ReadFile(path)
	if err != nil || !bytes.Equal(source, after) {
		t.Fatal("synthesis modified the original theorem source")
	}
	for _, input := range []string{"null", `[] true`, `["true"]; replacement`, `[1]`, "[]" + strings.Repeat(" ", 1<<20) + "true"} {
		candidatePath := filepath.Join(dir, "bad.json")
		if err := os.WriteFile(candidatePath, []byte(input), 0o600); err != nil {
			t.Fatal(err)
		}
		out.Reset()
		stderr.Reset()
		code := proveCommand([]string{"-solver", "go", "-synthesize", "ordered", "-candidates", candidatePath, path}, &out, &stderr)
		if code != 2 || out.Len() != 0 {
			t.Fatalf("invalid candidates accepted: code %d, %s %s", code, out.String(), stderr.String())
		}
	}
}

func TestProveSynthesisUsageAndOpen(t *testing.T) {
	for _, args := range [][]string{
		{"-synthesize", "ordered", "missing.oak"},
		{"-solver", "self", "-synthesize", "ordered", "missing.oak"},
		{"-solver", "sat", "-synthesize", "ordered", "missing.oak"},
		{"-solver", "go", "-synthesize", "ordered", "-lean", "out.lean", "missing.oak"},
		{"-candidates", "missing.json"},
		{"-synthesis-json"},
	} {
		var out, stderr bytes.Buffer
		if code := proveCommand(args, &out, &stderr); code != 2 || out.Len() != 0 {
			t.Fatalf("invalid combination %v: code %d, %s %s", args, code, out.String(), stderr.String())
		}
	}
	source, err := os.ReadFile("examples/verification_synthesis.oak")
	if err != nil {
		t.Fatal(err)
	}
	dir := writeTree(t, map[string]string{"laws.oak": string(source), "none.json": `[]`})
	var out, stderr bytes.Buffer
	code := proveCommand([]string{"-solver", "go", "-cases", "1", "-synthesize", "ordered", "-candidates", filepath.Join(dir, "none.json"), filepath.Join(dir, "laws.oak")}, &out, &stderr)
	if code != 1 || !strings.Contains(out.String(), "no inductive strengthening established") || strings.Contains(out.String(), "invariant:") {
		t.Fatalf("failed induction reported incorrectly: code %d, %s %s", code, out.String(), stderr.String())
	}
}
