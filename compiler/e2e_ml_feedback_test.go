package compiler

// End-to-end tests for the fixes motivated by the ml project's tensor
// compiler pilot (docs/notes/ml-feedback-2026-09.md): per-package scoping of
// the no-shadowing rule, the explicit discard form, string literal escapes,
// constant-constructor loop steps under the strict profile, and total data
// flow in the C emitted for a match-valued binding.

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

const mlFeedbackManifest = "module example.com/ml\noak 0.1.0\n"

// F5: a root `pub rank` must not make `rank` an illegal local in an imported
// package (docs/spec/83-modules.md section 7, law "scope is per package").
func TestE2ERootDeclarationDoesNotShadowImportedPackageLocals(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": mlFeedbackManifest,
		"main.oak": `package main
import("example.com/ml/view")

pub rank: (t: u32): u32 { t + 1 }

main: (): i32 {
  i32_bits_u32(view.f(u32(3)) + rank(u32(1)))
}
`,
		"view/view.oak": `package view

pub f: (id: u32): u32 {
  rank: u32 = id * u32(2)
  rank
}
`,
	})
	code, _ := buildPackageAndRun(t, New().WithPackageDir(root))
	if code != 8 {
		t.Fatalf("exit code %d, want 8 (view.f(3) = 6, rank(1) = 2)", code)
	}
}

// F5, prelude direction: the standard prelude declares locals named
// `maximum`; a root package exporting `maximum` must still compile.
func TestE2ERootDeclarationDoesNotShadowPreludeLocals(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": mlFeedbackManifest,
		"main.oak": `import(std)
maximum: (a: u32, b: u32): u32 { a < b ? b | a }
main: (): i32 { i32_bits_u32(maximum(u32(1), u32(2))) }
`,
	})
	code, _ := buildPackageAndRun(t, New().WithPackageDir(root))
	if code != 2 {
		t.Fatalf("exit code %d, want 2", code)
	}
}

// Shadowing inside one package is still rejected: the relaxation is about
// which package's scope is consulted, not about shadowing itself.
func TestE2ERootLocalStillCannotShadowRootDeclaration(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": mlFeedbackManifest,
		"main.oak": `rank: (t: u32): u32 { t + 1 }
main: (): i32 {
  rank: u32 = u32(2)
  i32_bits_u32(rank)
}
`,
	})
	_, err := New().WithPackageDir(root).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "already declared") {
		t.Fatalf("root-local shadowing of a root declaration must be rejected, got %v", err)
	}
}

// Explicit discard (docs/spec/85-discipline.md section 6), string escapes
// (docs/spec/10-syntax.md section 2a), and a constant-constructor loop step
// (section 3) all pass the strict profile and run.
func TestE2EDiscardEscapesAndConstantStepUnderStrict(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": mlFeedbackManifest,
		"main.oak": `putchar: (ch: c.Int): c.Int = c.extern("putchar")

count: (): u32 {
  k: u32 = u32(0)
  while k < u32(10) {
    k = k + u32(1)
  }
  k
}

emit: (s: string): () {
  i: u32 = 0
  bytes: []u8 = str_bytes(s)
  n: u32 = len(bytes)
  while i < n {
    _ = putchar(c.Int(i32_bits_u32(u32(bytes[i]))))
    i = i + 1
  }
}

main: (): i32 {
  emit("a\tb\n")
  i32_bits_u32(count()) - 10
}
`,
	})
	comp := New().WithPackageDir(root).WithProfile("strict")
	output, err := comp.EmitC().Get()
	if err != nil {
		t.Fatalf("strict compilation failed: %v", err)
	}
	if !strings.Contains(output, `"a\tb\n"`) {
		t.Fatalf("escape sequences must reach the C literal decoded and re-escaped; got:\n%s", output)
	}
	code, _ := buildPackageAndRun(t, comp)
	if code != 0 {
		t.Fatalf("exit code %d, want 0", code)
	}
}

// Discarding a unit value says nothing and is rejected.
func TestE2EDiscardOfUnitRejected(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": mlFeedbackManifest,
		"main.oak": `noop: (): () { }
main: (): i32 {
  _ = noop()
  0
}
`,
	})
	_, err := New().WithPackageDir(root).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "discard of a unit value") {
		t.Fatalf("discard of unit must be rejected, got %v", err)
	}
}

// An unknown escape is a parse error, never a silently different literal.
func TestE2EInvalidEscapeRejected(t *testing.T) {
	_, err := New().WithSource("bad.oak", "main: (): i32 {\n  s: string = \"bad\\q\"\n  0\n}\n").EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "invalid escape sequence") {
		t.Fatalf("invalid escape must be rejected, got %v", err)
	}
}

// F4 (pilots/emit): a binding initialized by an exhaustive ADT match must
// lower to C whose data flow is total, so -Wall reports no
// maybe-uninitialized use.
func TestE2EMatchValuedBindingIsWarningFreeC(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("no C compiler on PATH")
	}
	output, err := New().WithSource("pick.oak", `Op: type = Union | Intersection

pick: (left: u8, right: u8, operation: Op): u8 {
  combined: u8 = operation ?
    | .Union => (left | right)
    | .Intersection => left & right
  combined
}

main: (): i32 {
  i32(pick(u8(1), u8(2), .Union))
}
`).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	dir := t.TempDir()
	cPath := filepath.Join(dir, "pick.c")
	if err := os.WriteFile(cPath, []byte(output), 0o644); err != nil {
		t.Fatal(err)
	}
	build := exec.Command(cc, "-std=c99", "-O1", "-Wall", "-Wextra", "-Wuninitialized", "-Wsometimes-uninitialized", "-Wmaybe-uninitialized", "-Wno-unknown-warning-option", "-c", cPath, "-o", filepath.Join(dir, "pick.o"))
	out, err := build.CombinedOutput()
	if err != nil {
		t.Fatalf("cc failed: %v\n%s", err, out)
	}
	if strings.Contains(string(out), "uninitialized") {
		t.Fatalf("generated C must be free of uninitialized-use warnings:\n%s\n--- C ---\n%s", out, output)
	}
}
