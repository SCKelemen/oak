package compiler

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// Full-range u64 literals (ml finding F12, vgic ask 5): values above 2^63
// parse in decimal and radix forms, live only in 64-bit unsigned contexts,
// and agree between the compiled binary and the interpreter.
func TestE2EFullRangeU64Literals(t *testing.T) {
	src := `
fnv_basis: (): u64 {
  14695981039346656037
}
main: (): i32 {
  all: u64 = 0xFFFFFFFFFFFFFFFF
  high: u64 = 0x8000000000000000
  basis: u64 = fnv_basis()
  assert(all == 18446744073709551615)
  assert(all + 1 == 0)
  assert(high * 2 == 0)
  assert(high > 1)
  assert(all > high)
  assert(basis % 1000 == 37)
  assert(all >> 63 == 1)
  assert(all & high == high)
  folded: u32 = u32_trunc_u64(basis)
  folded == 2216829733 ? { 42 } | { 1 }
}
`
	output, err := New().WithSource("wide.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"18446744073709551615ULL", "9223372036854775808ULL", "14695981039346656037ULL"} {
		if !strings.Contains(output, want) {
			t.Fatalf("generated C lacks %q", want)
		}
	}
	code, abnormal := buildAndRun(t, "wide", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if interpreted := interpretChecked(t, src); interpreted != 42 {
		t.Fatalf("interpreter returned %d", interpreted)
	}
	for _, c := range []struct{ name, src, want string }{
		{"u32-context", "main: (): i32 { x: u32 = 4294967296\n 0 }", "literal 4294967296 does not fit in type u32"},
		{"i64-context", "main: (): i32 { x: i64 = 9223372036854775808\n 0 }", "literal 9223372036854775808 does not fit in type i64"},
		{"negated-wide", "main: (): i32 { x: i64 = -9223372036854775809\n 0 }", "literal -9223372036854775809 does not fit in type i64"},
		{"beyond-u64", "main: (): i32 { x: u64 = 18446744073709551616\n 0 }", "integer literal out of range"},
	} {
		t.Run(c.name, func(t *testing.T) {
			_, err := New().WithSource(c.name+".oak", c.src).Check().Get()
			if err == nil || !strings.Contains(err.Error(), c.want) {
				t.Fatalf("%s: want %q, got %v", c.name, c.want, err)
			}
		})
	}
}

// A loop body is its own scope (vgic ask 6): a name declared inside a while
// body may be declared again after the loop, in both realizations.
func TestE2ELoopBodyScope(t *testing.T) {
	src := `
total: (n: u32): u32 {
  i: u32 = 0
  acc: u32 = 0
  while i < n {
    step: u32 = 2
    acc = acc + step
    i = i + 1
  }
  step: u32 = 1
  acc + step
}
main: (): i32 {
  total(3) == 7 ? { 42 } | { 1 }
}
`
	code, abnormal := buildAndRun(t, "loopscope", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if interpreted := interpretChecked(t, src); interpreted != 42 {
		t.Fatalf("interpreter returned %d", interpreted)
	}
}

// Package scope is order-independent for globals (ml finding F13): a
// function may name a global declared later in the file.
func TestE2EGlobalsDeclaredAfterUse(t *testing.T) {
	src := `
bump: (): u32 {
  counter = counter + 1
  counter
}
main: (): i32 {
  bump()
  bump()
  counter + limit == 44 ? { 42 } | { 1 }
}
counter: u32 = 0
limit: u32 = 42
`
	code, abnormal := buildAndRun(t, "globalorder", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if interpreted := interpretChecked(t, src); interpreted != 42 {
		t.Fatalf("interpreter returned %d", interpreted)
	}
	_, err := New().WithSource("dup.oak", "counter: u32 = 0\ncounter: u32 = 1\nmain: (): i32 { 0 }").Check().Get()
	if err == nil || !strings.Contains(err.Error(), "already declared") {
		t.Fatalf("a duplicate global must still be rejected, got %v", err)
	}
}

// A failed assertion names its source position on stderr before trapping
// (ml finding F14), in hosted builds.
func TestE2EAssertionTrapNamesLocation(t *testing.T) {
	src := `
main: (): i32 {
  limit: u32 = 3
  assert(limit > 0)
  assert(limit > 5)
  42
}
`
	output, err := New().WithSource("located.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(output, `oak_assert( ( limit > 5 ), "located.oak", 5 )`) {
		t.Fatalf("assert did not carry its location:\n%s", output)
	}
	cc, lookErr := exec.LookPath("cc")
	if lookErr != nil {
		t.Skip("no C compiler on PATH")
	}
	dir := t.TempDir()
	cpath, bin := filepath.Join(dir, "located.c"), filepath.Join(dir, "located")
	if err := os.WriteFile(cpath, []byte(output), 0644); err != nil {
		t.Fatal(err)
	}
	if combined, err := exec.Command(cc, "-std=c99", "-O1", "-o", bin, cpath).CombinedOutput(); err != nil {
		t.Fatalf("cc failed: %v\n%s", err, combined)
	}
	run := exec.Command(bin)
	var stderr strings.Builder
	run.Stderr = &stderr
	runErr := run.Run()
	if runErr == nil {
		t.Fatal("the failing assertion must trap")
	}
	if !strings.Contains(stderr.String(), "located.oak:5") {
		t.Fatalf("trap message lacks the location: %q", stderr.String())
	}
}

// Diagnostics point at the spelling Oak has: narrowing names the explicit
// conversions, and a stray ~ names the ^ complement.
func TestPortingDiagnosticsNameTheSpelling(t *testing.T) {
	_, err := New().WithSource("narrow.oak", "f: (x: u64): u8 {\n  u8(x)\n}\nmain: (): i32 { 0 }").Check().Get()
	if err == nil || !strings.Contains(err.Error(), "u8_trunc_u64(x) wraps") || !strings.Contains(err.Error(), "u8_checked_u64(x)") {
		t.Fatalf("narrowing diagnostic lacks the conversion names: %v", err)
	}
	_, err = New().WithSource("tilde.oak", "f: (x: u64): u64 {\n  x & ~x\n}\nmain: (): i32 { 0 }").Check().Get()
	if err == nil || !strings.Contains(err.Error(), "prefix operator ^") {
		t.Fatalf("tilde diagnostic lacks the hint: %v", err)
	}
}
