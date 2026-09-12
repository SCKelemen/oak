package compiler

import (
	"strings"
	"testing"
)

// Effect rows on function types (docs/spec/60-effects-allocation.md section
// 2a): a value of type `(T) -> R effects { ... }` performs at most the row,
// so a call through it is a known fact and a `forbids` sees through it.

// A step launcher that forbids host reads accepts a pure step and runs.
func TestE2EEffectRowAdmitsPureStep(t *testing.T) {
	src := `
launch: (step: (u32) -> u32 effects { }, x: u32): u32 forbids { Host.Read, Memory.Allocate } = step(x)
double: (x: u32): u32 = x * u32(2)
main: (): i32 {
  s: (u32) -> u32 effects { } = double
  v: u32 = launch(double, u32(10)) + launch(s, u32(11))
  i32_bits_u32(v)
}
`
	code, abnormal := buildAndRun(t, "effect_row_pure", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// A step that reaches a host read does not fit an empty row; the path names
// the reader.
func TestEffectRowRejectsHostReadInStep(t *testing.T) {
	src := `
host_read: (x: c.UInt32): c.UInt32 effects { Host.Read } = c.extern("oak_host_read")
peek: (x: u32): u32 = u32(host_read(c.UInt32(x)))
launch: (step: (u32) -> u32 effects { }, x: u32): u32 = step(x)
main: (): i32 = i32_bits_u32(launch(peek, u32(1)))
`
	msg := effectError(t, "effect_row_host_read", src, CodeEffectRow)
	for _, want := range []string{"parameter step of launch", "performs Host.Read", "peek -> host_read"} {
		if !strings.Contains(msg, want) {
			t.Fatalf("missing %q: %s", want, msg)
		}
	}
}

// The row is the fact a call through the value contributes: a forbids that
// reaches it fails when the row carries the effect, by name.
func TestEffectRowIsSeenByForbids(t *testing.T) {
	src := `
launch: (step: (u32) -> u32 effects { Host.Read }, x: u32): u32 forbids { Host.Read } = step(x)
main: (): i32 = 0
`
	msg := effectError(t, "effect_row_forbids", src, CodeEffectForbidden)
	if !strings.Contains(msg, "through the function value step") {
		t.Fatalf("value not named: %s", msg)
	}
	transitive := `
run: (step: (u32) -> u32 effects { Host.Read }, x: u32): u32 = step(x)
hot: (step: (u32) -> u32 effects { Host.Read }, x: u32): u32 forbids { Host.Read } = run(step, x)
main: (): i32 = 0
`
	msg = effectError(t, "effect_row_forbids_path", transitive, CodeEffectForbidden)
	if !strings.Contains(msg, "hot -> run") || !strings.Contains(msg, "through the function value step") {
		t.Fatalf("path or value missing: %s", msg)
	}
}

// Facts are never guessed: an unrowed value, an undeclared extern, and a
// value that cannot be followed all fail closed against a row.
func TestEffectRowFailsClosed(t *testing.T) {
	cases := map[string]string{
		"unrowed value": `
launch: (step: (u32) -> u32 effects { }, x: u32): u32 = step(x)
outer: (f: (u32) -> u32, x: u32): u32 = launch(f, x)
main: (): i32 = 0
`,
		"undeclared extern": `
mystery: (x: c.UInt32): c.UInt32 = c.extern("mystery")
wrapped: (x: u32): u32 = u32(mystery(c.UInt32(x)))
launch: (step: (u32) -> u32 effects { }, x: u32): u32 = step(x)
main: (): i32 = i32_bits_u32(launch(wrapped, u32(1)))
`,
		"wider row into narrower": `
launch: (step: (u32) -> u32 effects { }, x: u32): u32 = step(x)
relaunch: (step: (u32) -> u32 effects { Host.Read }, x: u32): u32 = launch(step, x)
main: (): i32 = 0
`,
		"declaration": `
host_read: (x: c.UInt32): c.UInt32 effects { Host.Read } = c.extern("oak_host_read")
peek: (x: u32): u32 = u32(host_read(c.UInt32(x)))
main: (): i32 {
  s: (u32) -> u32 effects { } = peek
  0
}
`,
	}
	for name, src := range cases {
		effectError(t, "effect_row_"+strings.ReplaceAll(name, " ", "_"), src, CodeEffectRow)
	}
}

// A narrower row fits a wider one, and a function literal is analyzed like
// a body.
func TestE2EEffectRowSubsumptionAndLiterals(t *testing.T) {
	src := `
launch: (step: (u32) -> u32 effects { Host.Read, Memory.Allocate }, x: u32): u32 = step(x)
narrow: (step: (u32) -> u32 effects { }, x: u32): u32 = launch(step, x)
inc: (x: u32): u32 = x + u32(1)
main: (): i32 {
  a: u32 = narrow(inc, u32(20))
  b: u32 = launch(fn(x: u32): u32 { inc(x) }, u32(20))
  i32_bits_u32(a + b)
}
`
	code, abnormal := buildAndRun(t, "effect_row_subsume", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	bad := `
host_read: (x: c.UInt32): c.UInt32 effects { Host.Read } = c.extern("oak_host_read")
peek: (x: u32): u32 = u32(host_read(c.UInt32(x)))
launch: (step: (u32) -> u32 effects { }, x: u32): u32 = step(x)
main: (): i32 = i32_bits_u32(launch(fn(x: u32): u32 { peek(x) }, u32(1)))
`
	msg := effectError(t, "effect_row_literal", bad, CodeEffectRow)
	if !strings.Contains(msg, "the function literal -> peek -> host_read") {
		t.Fatalf("literal path missing: %s", msg)
	}
}

// The row prints back and survives generic substitution.
func TestEffectRowSyntaxAndGenerics(t *testing.T) {
	src := `
apply[T]: (f: (T) -> T effects { }, x: T): T = f(x)
inc: (x: u32): u32 = x + u32(1)
main: (): i32 = i32_bits_u32(apply(inc, u32(41)))
`
	tree, err := New().WithSource("rows.oak", src).Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	if printed := tree.Root.String(); !strings.Contains(printed, "-> T effects { }") {
		t.Fatalf("row must print back: %s", printed)
	}
	code, abnormal := buildAndRun(t, "effect_row_generic", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	badGeneric := `
host_read: (x: c.UInt32): c.UInt32 effects { Host.Read } = c.extern("oak_host_read")
peek: (x: u32): u32 = u32(host_read(c.UInt32(x)))
apply[T]: (f: (T) -> T effects { }, x: T): T = f(x)
main: (): i32 = i32_bits_u32(apply(peek, u32(41)))
`
	effectError(t, "effect_row_generic_bad", badGeneric, CodeEffectRow)
	twice := "f: (g: (u32) -> u32 effects { } effects { }): u32 = 0\nmain: (): i32 = 0"
	if _, err := New().WithSource("twice.oak", twice).Parse().Get(); err == nil {
		t.Fatal("two rows on one type must be rejected")
	}
}
