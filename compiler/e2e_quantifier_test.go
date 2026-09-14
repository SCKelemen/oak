package compiler

import (
	"strings"
	"testing"
)

// Bounded quantifiers (docs/spec/10-syntax.md section 3e) evaluate the
// same way in the interpreter and in the compiled C: the binders range
// over their finite domains, the enumeration stops at the deciding
// assignment, and the words stay identifiers outside the binder form.
const quantifierProgram = `
Color: type = Red | Green | Blue

all_wrap: (): Bool = forall (x: u16) { x + u16(1) - u16(1) == x }

pair_sum: (n: u8): Bool = exists (a: u8, b: u8) { a < b && u16(a) + u16(b) == u16(n) }

main: (): i32 = {
  exists: u8 = u8(7)
  hits: i32 = 0
  forall (b: Bool) { b || !b } ? { hits = hits + 1 } | { }
  exists (c: Color) { c == .Blue } ? { hits = hits + 1 } | { }
  forall (c: Color) { c == .Blue } ? { } | { hits = hits + 1 }
  forall (x: i8) { x >= i8(-128) && x <= i8(127) } ? { hits = hits + 1 } | { }
  exists (x: u8) { x == exists } ? { hits = hits + 1 } | { }
  all_wrap() ? { hits = hits + 1 } | { }
  pair_sum(u8(7)) ? { hits = hits + 1 } | { }
  pair_sum(u8(0)) ? { } | { hits = hits + 1 }
  hits + 34
}
`

func TestE2EQuantifiers(t *testing.T) {
	if got := interpret(t, quantifierProgram); got != 42 {
		t.Fatalf("interpreter = %d, want 42", got)
	}
	code, abnormal := buildAndRun(t, "quantifiers", quantifierProgram)
	if abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	extracted, err := New().WithSource("quantifiers.oak", quantifierProgram).EmitLean("Oak.QuantifiersTest").Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"((List.range 65536).map (fun n => UInt16.ofNat n)).all (fun x =>",
		"((List.range 256).map (fun n => UInt8.ofNat n)).any (fun a => (((List.range 256).map (fun n => UInt8.ofNat n)).any (fun b =>",
		"[Color.Red, Color.Green, Color.Blue].any (fun c =>",
	} {
		if !strings.Contains(extracted, want) {
			t.Errorf("the Lean projection must fold the domain; want %q in:\n%s", want, extracted)
		}
	}
}
