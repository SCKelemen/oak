package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// A target constant (docs/spec/92-ffi.md section 2.11) is a C identifier
// the target's headers define, bound at top level and resolved by the C
// compiler: CLOCK_MONOTONIC is 1 on Linux and 6 on Darwin, and Oak never
// learns which. The program includes <time.h> for the constant and also
// binds clock_gettime as an extern — the very function that header
// declares — so the asm-labeled extern declaration is exercised against a
// conflicting header prototype.
const targetConstantClock = `
Timespec: type = struct { sec: i64, nsec: i64 }
CLOCK_REALTIME: c.Int = c.const("CLOCK_REALTIME", "<time.h>")
CLOCK_MONOTONIC: c.Int = c.const("CLOCK_MONOTONIC", "<time.h>")
clock_gettime: (id: c.Int, ts: c.Ptr): c.Int = c.extern("clock_gettime")
strlen: (s: c.String): c.UInt64 = c.extern("strlen")

read_clock: (id: c.Int): i64 {
  ts: Timespec = Timespec { sec: i64(0), nsec: i64(0) }
  r: c.Int = clock_gettime(id, c.out(ts))
  assert(i32(r) == i32(0))
  assert(ts.nsec >= i64(0) && ts.nsec < i64(1000000000))
  ts.sec * i64(1000000000) + ts.nsec
}
`

func TestE2ETargetConstantClock(t *testing.T) {
	skipWithoutPosixSpawn(t)
	src := targetConstantClock + `
main: (): i32 {
  wall: i64 = read_clock(CLOCK_REALTIME)
  // After 2020 and before 2100.
  assert(wall > i64(1577836800000000000) && wall < i64(4102444800000000000))
  first: i64 = read_clock(CLOCK_MONOTONIC)
  second: i64 = read_clock(CLOCK_MONOTONIC)
  assert(second >= first)
  // An unrelated extern still resolves through its asm label.
  assert(u64(strlen(c.String("seven!!"))) == u64(7))
  42
}
`
	generated, err := New().WithSource("ffi_const.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"#include <time.h>",
		"static const int oak_const_CLOCK_MONOTONIC = CLOCK_MONOTONIC;",
		"static const int oak_const_CLOCK_REALTIME = CLOCK_REALTIME;",
		"read_clock( oak_const_CLOCK_MONOTONIC )",
		`oak_extern_clock_gettime( int id, void * ts ) __asm__(OAK_ASM_SYMBOL("clock_gettime"))`,
		"oak_extern_clock_gettime( id, ",
		`__asm__(OAK_ASM_SYMBOL("strlen"))`,
	} {
		if !strings.Contains(generated, want) {
			t.Fatalf("generated C lacks %q:\n%s", want, generated)
		}
	}
	_, code, abnormal := buildAndRunFrom(t, "ffi_const", New().WithSource("ffi_const.oak", src))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// A program without target constants keeps the plain extern prototype: the
// asm-label declaration is confined to programs that include foreign
// headers, so every existing program's C is unchanged.
func TestE2ETargetConstantAbsentKeepsPlainExterns(t *testing.T) {
	src := `
strlen: (s: c.String): c.UInt64 = c.extern("strlen")
main: (): i32 { u64(strlen(c.String("abc"))) == u64(3) ? 42 | 0 }
`
	generated, err := New().WithSource("ffi_plain.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(generated, "__asm__(OAK_ASM_SYMBOL") || strings.Contains(generated, "oak_extern_") {
		t.Fatalf("plain program gained asm-labeled externs:\n%s", generated)
	}
	if !strings.Contains(generated, "extern uint64_t strlen( const char * s );") {
		t.Fatalf("plain extern prototype missing:\n%s", generated)
	}
}

func TestE2ETargetConstantRejections(t *testing.T) {
	cases := []struct {
		name string
		src  string
		code string
	}{
		{"identifier with a space", `
X: c.Int = c.const("CLOCK MONOTONIC", "<time.h>")
main: (): i32 { 0 }
`, "OAK-F0114"},
		{"identifier that is not a literal", `
name: string = "CLOCK_MONOTONIC"
X: c.Int = c.const(name, "<time.h>")
main: (): i32 { 0 }
`, "OAK-F0114"},
		{"header without brackets", `
X: c.Int = c.const("CLOCK_MONOTONIC", "time.h")
main: (): i32 { 0 }
`, "OAK-F0114"},
		{"header with a parent segment", `
X: c.Int = c.const("CLOCK_MONOTONIC", "<../time.h>")
main: (): i32 { 0 }
`, "OAK-F0114"},
		{"header with a quote inside", `
X: c.Int = c.const("CLOCK_MONOTONIC", "<time.h>\"")
main: (): i32 { 0 }
`, "OAK-F0114"},
		{"Oak type annotation", `
X: i32 = c.const("CLOCK_MONOTONIC", "<time.h>")
main: (): i32 { 0 }
`, "OAK-F0114"},
		{"pointer annotation", `
X: c.Ptr = c.const("NULL", "<stddef.h>")
main: (): i32 { 0 }
`, "OAK-F0114"},
		{"local binding", `
main: (): i32 {
  x: c.Int = c.const("CLOCK_MONOTONIC", "<time.h>")
  0
}
`, "OAK-F0114"},
		{"expression position", `
take: (n: c.Int): i32 = i32(n)
main: (): i32 { take(c.const("CLOCK_MONOTONIC", "<time.h>")) }
`, "OAK-F0114"},
		{"one argument", `
X: c.Int = c.const("CLOCK_MONOTONIC")
main: (): i32 { 0 }
`, "OAK-F0114"},
		{"assignment", `
X: c.Int = c.const("CLOCK_MONOTONIC", "<time.h>")
main: (): i32 {
  X = c.Int(i32(1))
  0
}
`, "OAK-F0114"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			_, err := New().WithSource("reject.oak", tc.src).EmitC().Get()
			if err == nil || !strings.Contains(err.Error(), tc.code) {
				t.Fatalf("expected %s, got %v", tc.code, err)
			}
		})
	}
}

// A target constant is not a compile-time constant for Oak: a later global
// that reads it is the ordinary OAK-T0501 case (a C static const is not a
// constant expression either).
func TestE2ETargetConstantIsNotAFoldableConstant(t *testing.T) {
	src := `
X: c.Int = c.const("CLOCK_MONOTONIC", "<time.h>")
Y: c.Int = X
main: (): i32 { 0 }
`
	_, err := New().WithSource("derived.oak", src).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "OAK-T0501") {
		t.Fatalf("expected OAK-T0501, got %v", err)
	}
}

// The interpreter has no target and rejects the form.
func TestInterpreterRejectsTargetConstant(t *testing.T) {
	src := `
X: c.Int = c.const("CLOCK_MONOTONIC", "<time.h>")
main: (): i32 { i32(X) }
`
	p := parser.New(layout.New(scanner.New(src)))
	program := p.ParseProgram()
	if errors := p.Errors(); len(errors) != 0 {
		t.Fatalf("parse: %v", errors)
	}
	result := evaluator.Eval(program, object.NewEnvironment())
	err, isErr := result.(*object.Error)
	if !isErr || !strings.Contains(err.Message, "native backend") {
		t.Fatalf("expected the interpreter to reject c.const, got %s", result.Inspect())
	}
}
