package compiler

import (
	"strings"
	"testing"
)

func effectError(t *testing.T, name, src, code string) string {
	t.Helper()
	_, err := New().WithSource(name+".oak", src).EmitC().Get()
	if err == nil {
		t.Fatalf("%s: compiled; want %s", name, code)
	}
	if !strings.Contains(err.Error(), code) {
		t.Fatalf("%s: want %s, got %v", name, code, err)
	}
	return err.Error()
}

func TestE2EForbidsHoldsOnAPureChain(t *testing.T) {
	src := `
leaf: (x: u32): u32 = x + u32(1)
mid: (x: u32): u32 = leaf(x) * u32(2)
hot: (x: u32): u32 forbids { Memory.Allocate, Os.Syscall } = mid(x)
main: (): i32 {
  v: u32 = hot(u32(20))
  i32_bits_u32(v)
}
`
	code, abnormal := buildAndRun(t, "forbids_pure", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestForbidsReachedTransitivelyNamesThePath(t *testing.T) {
	src := `
grow: (n: u32): u32 effects { Memory.Allocate } = n
mid: (n: u32): u32 = grow(n)
hot: (n: u32): u32 forbids { Memory.Allocate } = mid(n)
main: (): i32 = i32_bits_u32(hot(u32(1)))
`
	msg := effectError(t, "forbids_path", src, CodeEffectForbidden)
	if !strings.Contains(msg, "hot -> mid -> grow") {
		t.Fatalf("path missing: %s", msg)
	}
}

func TestForbidsAndEffectsContradict(t *testing.T) {
	src := `
f: (): () effects { Thread.Block } forbids { Thread.Block } = {}
main: (): i32 = 0
`
	effectError(t, "forbids_contradiction", src, CodeEffectContradiction)
}

func TestForbidsFailsClosedOnUndeclaredExtern(t *testing.T) {
	src := `
c_malloc: (n: c.UInt64): c.UInt64 = c.extern("malloc")
hot: (): u64 forbids { Memory.Allocate } = u64(c_malloc(c.UInt64(u64(8))))
main: (): i32 = 0
`
	msg := effectError(t, "forbids_extern", src, CodeEffectUnknown)
	if !strings.Contains(msg, "c_malloc") {
		t.Fatalf("extern not named: %s", msg)
	}
	declared := `
c_malloc: (n: c.UInt64): c.UInt64 effects { Memory.Allocate } = c.extern("malloc")
hot: (): u64 forbids { Memory.Allocate } = u64(c_malloc(c.UInt64(u64(8))))
main: (): i32 = 0
`
	effectError(t, "forbids_extern_declared", declared, CodeEffectForbidden)
	pure := `
c_abs: (n: c.Int32): c.Int32 effects { } = c.extern("abs")
hot: (): i32 forbids { Memory.Allocate, Os.Syscall } = i32(c_abs(c.Int32(i32(-3))))
main: (): i32 = 0
`
	if _, err := New().WithSource("forbids_extern_pure.oak", pure).EmitC().Get(); err != nil {
		t.Fatalf("an extern asserting no effects must satisfy forbids: %v", err)
	}
}

func TestForbidsFailsClosedOnFunctionValues(t *testing.T) {
	src := `
apply: (f: (u32) -> u32, x: u32): u32 forbids { Memory.Allocate } = f(x)
main: (): i32 = 0
`
	effectError(t, "forbids_value", src, CodeEffectUnknown)
}

func TestEffectClausesRoundTripInSyntax(t *testing.T) {
	src := `
f: (x: u32): u32 effects { Memory.Allocate } forbids { Os.Syscall } = x
main: (): i32 = 0
`
	tree, err := New().WithSource("clauses.oak", src).Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	printed := tree.Root.String()
	for _, want := range []string{"effects { Memory.Allocate }", "forbids { Os.Syscall }"} {
		if !strings.Contains(printed, want) {
			t.Fatalf("printed syntax lacks %q: %s", want, printed)
		}
	}
	twice := "f: (): () forbids { A.B } forbids { A.C } = {}\nmain: (): i32 = 0"
	if _, err := New().WithSource("twice.oak", twice).Parse().Get(); err == nil {
		t.Fatalf("two forbids clauses must be rejected")
	}
}
