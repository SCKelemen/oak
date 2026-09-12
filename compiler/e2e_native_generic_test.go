package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Generic instantiations through the native backend
// (docs/spec/94-assembler.md §9, fifteenth increment): Option[u32] and
// Result[u32, Bool] (declared as the standard library declares them),
// specialized by the compiler
// into monomorphic declarations under their mangled names, so building,
// matching, passing, and returning them follow the tagged-union paths; a
// u64 element index is admitted after its high word is checked. The C
// backend's realization of the same program is the oracle.
const nativeGenericProgram = `
Option[T]: type = Some: T | None
Result[T, E]: type = Ok: T | Err: E

find_byte: (v: []u8, needle: u8) -> Option[u32] {
  found: Option[u32] = .None
  i: u32 = u32(0)
  while i < len(v) {
    v[i] == needle ? { found = .Some(i)
                       i = len(v) } | { i = i + u32(1) }
  }
  found
}

unwrap_or: (o: Option[u32], d: u32) -> u32 = o ?
  | .Some(x) -> x
  | .None -> d

// A checked add: the wrapped sum below an operand signals overflow.
checked_add: (a: u32, b: u32) -> Result[u32, Bool] = a + b < a ? .Err(true) | .Ok(a + b)

value_of: (r: Result[u32, Bool]) -> u32 = r ?
  | .Ok(v) -> v
  | .Err(_) -> u32(0)

// A wide index walks a view after its high word is checked.
at_wide: (v: []u8, i: u64) -> u32 = u32(v[i])

main: (): i32 {
  buf: [4]u8 = [u8(1), u8(2), u8(3), u8(4)]
  assert(unwrap_or(find_byte(view(&buf), u8(3)), u32(99)) == u32(2))
  assert(unwrap_or(find_byte(view(&buf), u8(9)), u32(99)) == u32(99))
  assert(value_of(checked_add(u32(5), u32(6))) == u32(11))
  assert(value_of(checked_add(u32(4294967295), u32(1))) == u32(0))
  assert(at_wide(view(&buf), u64(3)) == u32(4))
  42
}
`

// A wide index at or beyond 2^32 traps in both realizations.
const nativeWideIndexTrapProgram = `
at_wide: (v: []u8, i: u64) -> u32 = u32(v[i])

main: (): i32 {
  buf: [4]u8
  at_wide(view(&buf), u64(4294967296))
  0
}
`

func TestE2ENativeGenerics(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("generics.oak", nativeGenericProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_generics", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native generics: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"find_byte", "unwrap_or", "checked_add", "value_of", "at_wide", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	for _, fn := range []string{"unwrap_or", "checked_add", "value_of"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s must be proven equal to its Oak body (an instantiated union as leaf terms); diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_generics_c", New().WithSource("generics.oak", nativeGenericProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_generics_portable", New().WithSource("generics.oak", nativeGenericProgram).WithNativeBodies(), "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
		t.Fatalf("portable realization: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	_, _, nativeAbnormal := buildAndRunFrom(t, "native_wide_index_oob", New().WithSource("wide.oak", nativeWideIndexTrapProgram).WithNativeBodies().WithNativeAsm())
	_, _, cAbnormal := buildAndRunFrom(t, "native_wide_index_oob_c", New().WithSource("wide.oak", nativeWideIndexTrapProgram))
	if !nativeAbnormal || !cAbnormal {
		t.Fatalf("a wide index past 2^32 must trap in both realizations (native abnormal=%v, C abnormal=%v)", nativeAbnormal, cAbnormal)
	}
}
