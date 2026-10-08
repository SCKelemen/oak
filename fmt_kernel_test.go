package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/compiler"
)

func TestFmtKernelClausePreservesMeaning(t *testing.T) {
	source := "touch: (gid: u32, out: [*]u32): () (kernel) effects { } = {  \r\n  gid < len(out) ? { out[gid] = gid }  \r\n}\r\n\r\n"
	file := filepath.Join(t.TempDir(), "kernel.oak")
	if err := os.WriteFile(file, []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	before, err := compiler.New().WithSource(file, source).EmitMetal().Get()
	if err != nil {
		t.Fatal(err)
	}
	if code, out := runCLI(t, fmtCommand, []string{"-w", file}); code != 0 {
		t.Fatalf("fmt: %d: %s", code, out)
	}
	formatted, err := os.ReadFile(file)
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(string(formatted), "\r") || !strings.Contains(string(formatted), "() (kernel) effects { }") {
		t.Fatalf("formatted: %q", formatted)
	}
	after, err := compiler.New().WithSource(file, string(formatted)).EmitMetal().Get()
	if err != nil {
		t.Fatal(err)
	}
	if before.Source != after.Source {
		t.Fatal("formatting changed emitted kernel")
	}
	if code, out := runCLI(t, fmtCommand, []string{"-l", file}); code != 0 || out != "" {
		t.Fatalf("fmt is not idempotent: %d %q", code, out)
	}
}

func TestFmtStdoutRefusesChangingLiteralContents(t *testing.T) {
	source := "message: string = \"first  \nsecond\"\n"
	file := filepath.Join(t.TempDir(), "literal.oak")
	if err := os.WriteFile(file, []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	if _, err := compiler.New().WithSource(file, source).Parse().Get(); err != nil {
		t.Fatalf("fixture must parse: %v", err)
	}
	if code, out := runCLI(t, fmtCommand, []string{file}); code != 1 || !strings.Contains(out, "formatting would change the syntax tree") {
		t.Fatalf("must not print a changed string literal: code=%d output=%q", code, out)
	}
	data, err := os.ReadFile(file)
	if err != nil || string(data) != source {
		t.Fatalf("source changed: %q, %v", data, err)
	}
}
