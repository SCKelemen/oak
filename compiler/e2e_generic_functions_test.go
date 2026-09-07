package compiler

import (
	"strings"
	"testing"
)

// Generic functions (docs/spec/20-types.md §11.2): templates monomorphize
// per call site — inferred from argument types or explicit (max[u32]) —
// and every instantiation is an ordinary function that the borrow checker,
// discipline analysis, and codegen see and gate. The flagship is the
// anti-boolean-blindness pattern: cmp returns Ordering EVIDENCE, max
// absorbs conditional mutation into a domain function.
func TestE2EGenericFunctionsOrdering(t *testing.T) {
	src := `
Ordering: type = Less | Equal | Greater

cmp[T]: (a: T, b: T): Ordering {
  a < b ? .Less | (a == b ? .Equal | .Greater)
}

max[T]: (a: T, b: T): T {
  a < b ? b | a
}

main: (): i32 {
  best: u32 = 5
  v: u32 = 9

  cmp(v, best) ?
    | .Greater => { best = v }
    | .Less => { }
    | .Equal => { }
  assert(best == u32(9))

  best = max(best, u32(3))
  assert(best == u32(9))

  wide: u64 = max(u64(40), u64(2))
  narrow: u32 = max[u32](2, 40)
  assert(wide == u64(40))
  assert(narrow == u32(40))

  cmp(u64(1), u64(1)) ?
    | .Equal => { 42 }
    | .Less => { 0 }
    | .Greater => { 0 }
}
`
	output, err := New().WithSource("genfn.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, want := range []string{"oak_max_u32", "oak_max_u64", "oak_cmp_u32", "oak_cmp_u64"} {
		if !strings.Contains(output, want) {
			t.Fatalf("emitted C lacks specialization %q:\n%s", want, output)
		}
	}
	if strings.Contains(output, "oak_max(") || strings.Contains(output, "oak_cmp(") {
		t.Fatalf("template leaked into emitted C:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "genfn", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// A generic function calling another generic function: the nested call
// re-resolves with concrete types inside the specialized body.
func TestE2EGenericCallsGeneric(t *testing.T) {
	code, abnormal := buildAndRun(t, "genchain", `
smaller[T]: (a: T, b: T): T {
  a < b ? a | b
}

clamp[T]: (v: T, hi: T): T {
  smaller(v, hi)
}

main: (): i32 {
  assert(clamp(u32(50), u32(42)) == u32(42))
  assert(clamp(u8(3), u8(9)) == u8(3))
  42
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// Instantiation-time checking: a body operation illegal for the concrete
// type fails at that instantiation (bitand on a signed type here), and
// uninferable parameters demand explicit instantiation.
func TestGenericFunctionRejections(t *testing.T) {
	_, err := New().WithSource("genbad.oak", `
maskLow[T]: (v: T): T {
  v & 0xF
}

main: (): i32 {
  v: i32 = -3
  x: i32 = maskLow(v)
  x
}
`).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "unsigned") {
		t.Fatalf("signed instantiation of a bitwise body must fail, got: %v", err)
	}

	_, err = New().WithSource("genuninfer.oak", `
zero[T]: (): T {
  0
}

main: (): i32 {
  zero()
}
`).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "cannot infer type parameter") {
		t.Fatalf("uninferable parameter must demand explicit instantiation, got: %v", err)
	}
}
