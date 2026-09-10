package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/compiler"
)

// The Lean extraction of the self-hosted checker (docs/spec/95-extraction.md):
// proof/OakTextExtracted.lean is generated from the three Oak sources by the
// compiler and committed, so the proof tree builds without Go. This test
// regenerates it and fails on drift; OAK_LEAN_EXTRACT_UPDATE=1 rewrites the
// committed file.
func TestLeanExtractionMatchesCommitted(t *testing.T) {
	var source strings.Builder
	for _, path := range []string{"self_hosted_rup.oak", "self_hosted_stream.oak", "self_hosted_text.oak"} {
		data, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		source.Write(data)
		source.WriteByte('\n')
	}
	extracted, err := compiler.New().WithSource("self_hosted.oak", source.String()).EmitLean("OakVerification.Extracted").Get()
	if err != nil {
		t.Fatalf("extraction failed: %v", err)
	}
	target := filepath.Join("proof", "OakTextExtracted.lean")
	if os.Getenv("OAK_LEAN_EXTRACT_UPDATE") == "1" {
		if err := os.WriteFile(target, []byte(extracted), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	committed, err := os.ReadFile(target)
	if err != nil {
		t.Fatalf("read committed extraction: %v (run with OAK_LEAN_EXTRACT_UPDATE=1 to create it)", err)
	}
	if string(committed) != extracted {
		t.Fatalf("proof/OakTextExtracted.lean is out of date with the Oak sources; rerun with OAK_LEAN_EXTRACT_UPDATE=1")
	}
}
