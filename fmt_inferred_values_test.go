package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/compiler"
)

func TestFmtInferredBitwiseValuePreservesMeaning(t *testing.T) {
	source := "main: (): i32 {  \r\n  a := u32(40)\r\n  b := u32(2)\r\n  mask := a | b  \r\n  i32_bits_u32(mask)\r\n}\r\n\r\n"
	file := filepath.Join(t.TempDir(), "inferred.oak")
	if err := os.WriteFile(file, []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	before, err := compiler.New().WithSource(file, source).EmitC().Get()
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
	if strings.Contains(string(formatted), "\r") || !strings.Contains(string(formatted), "mask := a | b") {
		t.Fatalf("formatted: %q", formatted)
	}
	after, err := compiler.New().WithSource(file, string(formatted)).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if before != after {
		t.Fatal("formatting changed emitted bitwise value")
	}
	if code, out := runCLI(t, fmtCommand, []string{"-l", file}); code != 0 || out != "" {
		t.Fatalf("fmt is not idempotent: %d %q", code, out)
	}
}
