package compiler

import (
	"strings"
	"testing"
)

// The correctness-checklist pass over two language features
// (docs/notes/language-features-2026-09.md): the alignment fact on spans
// (docs/spec/50-borrowing.md section 2a) flows through every position with
// its direction — function values, joins, returns, template signatures,
// packed records, `align 1` — and the propagation form `try`
// (docs/spec/10-syntax.md section 2d) lowers in function literals, refuses
// a block with `defer`, and reports one located diagnostic per refusal.

const alignmentPassProgram = `
Sector: type = struct(align: 4096) { bytes: [8192]u8 }
needs_sector: (region: [* align 4096]u8): u32 = len(region)
takes_plain: (region: [*]u8): u32 = len(region)
apply: (f: ([*]u8) -> u32, r: [*]u8): u32 = f(r)
apply_aligned: (f: ([* align 4096]u8) -> u32, r: [* align 4096]u8): u32 = f(r)
// A template parameter's declared fact survives instantiation: inside g,
// x is [* align 4096]u8 and satisfies needs_sector.
g[T]: (x: [* align 4096]T): u32 = needs_sector(x)
// A returned fact is a claim the body satisfies: the parameter carries it.
keep: (x: [* align 4096]u8): [* align 4096]u8 = x
// align 1 is the plain type: any span satisfies it.
one: (r: [* align 1]u8): u32 = len(r)
main: (): i32 {
  store: Sector
  aligned: [* align 4096]u8 = span(&store.bytes)
  other: Sector
  aligned2: [* align 4096]u8 = span(&other.bytes)
  ok: Bool = true
  // A function value requiring less than the target supplies is admitted
  // (contravariance), and one requiring exactly the fact is admitted where
  // the fact is supplied.
  ok = ok && apply(takes_plain, aligned) == u32(8192)
  ok = ok && apply_aligned(needs_sector, aligned) == u32(8192)
  ok = ok && apply_aligned(takes_plain, aligned) == u32(8192)
  // A join of two arms that both carry the fact keeps it.
  flag: Bool = len(aligned) > u32(0)
  joined: [* align 4096]u8 = flag ? { aligned } | { aligned2 }
  ok = ok && needs_sector(joined) == u32(8192)
  ok = ok && g(aligned) == u32(8192)
  ok = ok && needs_sector(keep(aligned)) == u32(8192)
  plain: [8]u8
  ok = ok && one(span(&plain)) == u32(8)
  ok ? 42 | 1
}
`

func TestAlignmentFactPassCompiled(t *testing.T) {
	code, abnormal := buildAndRun(t, "alignment_pass", alignmentPassProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestAlignmentFactPassInterpreted(t *testing.T) {
	if got := interpretChecked(t, alignmentPassProgram); got != 42 {
		t.Fatalf("interpreter: got %d, want 42", got)
	}
}

// The positions the pass found forging the fact are refused with both
// types named.
func TestAlignmentFactPassRejections(t *testing.T) {
	prelude := `
Sector: type = struct(align: 4096) { bytes: [8192]u8 }
needs_sector: (region: [* align 4096]u8): u32 = len(region)
takes_plain: (region: [*]u8): u32 = len(region)
`
	cases := map[string]struct{ src, want string }{
		"packed record field has no element fact": {`
P: type = struct(packed) { tag: u8, words: [4]u64 }
needs_eight: (words: [* align 8]u64): u32 = len(words)
main: (): i32 {
  p: P
  needs_eight(span(&p.words)) == u32(0) ? 1 | 0
}
`, "expected [* align 8]u64, got [*]u64"},
		"function value requiring more than the target supplies": {prelude + `
apply: (f: ([*]u8) -> u32, r: [*]u8): u32 = f(r)
main: (): i32 {
  store: [8192]u8
  apply(needs_sector, span(&store)) == u32(0) ? 1 | 0
}
`, "([* align 4096]u8) -> u32"},
		"function value bound to a weaker type": {prelude + `
main: (): i32 {
  f: ([*]u8) -> u32 = needs_sector
  0
}
`, "([* align 4096]u8) -> u32"},
		"join takes the weakest fact": {prelude + `
main: (): i32 {
  store: Sector
  aligned: [* align 4096]u8 = span(&store.bytes)
  off: [*]u8 = subslice(aligned, u32(1), u32(4096))
  flag: Bool = len(off) > u32(0)
  r: [* align 4096]u8 = flag ? { aligned } | { off }
  0
}
`, "expected type [* align 4096]u8, got [*]u8"},
		"match join takes the weakest fact": {prelude + `
main: (): i32 {
  store: Sector
  aligned: [* align 4096]u8 = span(&store.bytes)
  off: [*]u8 = subslice(aligned, u32(1), u32(4096))
  flag: Bool = len(off) > u32(0)
  r: [* align 4096]u8 = flag ? | true => aligned | false => off
  0
}
`, "expected type [* align 4096]u8, got [*]u8"},
		"return claims more than the body gives": {prelude + `
claim: (x: [*]u8): [* align 4096]u8 = x
main: (): i32 = 0
`, "a declaration may not claim more than the borrow gives"},
		"template signature keeps the fact against the argument": {prelude + `
g[T]: (x: [* align 4096]T): u32 = len(x)
main: (): i32 {
  store: [8192]u8
  g(span(&store)) == u32(0) ? 1 | 0
}
`, "[* align 4096]u8"},
	}
	for name, c := range cases {
		_, err := New().WithSource("bad.oak", c.src).EmitC().Get()
		if err == nil || !strings.Contains(err.Error(), c.want) {
			t.Fatalf("%s: want %q, got %v", name, c.want, err)
		}
	}
}

const tryPassProgram = `
import(std)
Fault: type = | Bad
step: (n: u32): Result[u32, Fault] = n > u32(10) ? .Err(.Bad) | .Ok(n + u32(1))
// A function literal with a declared Result return type propagates within
// itself; the enclosing function returns i32 and has no try of its own.
run: (n: u32): u32 {
  twice := fn(k: u32): Result[u32, Fault] {
    a: u32 = try step(k)
    b: u32 = try step(a)
    .Ok(b)
  }
  twice(n) ? | .Ok(v) => v | .Err(_) => u32(99)
}
// A program may spell the generated binder's name: the arm reads its own.
shadow: (n: u32): Result[u32, Fault] {
  oak_try_err_1: u32 = u32(1000)
  a: u32 = try step(n)
  .Ok(a + oak_try_err_1)
}
main: (): i32 {
  ok: Bool = run(u32(1)) == u32(3) && run(u32(10)) == u32(99)
  shadowed: Bool = shadow(u32(1)) ? | .Ok(v) => v == u32(1002) | .Err(_) => false
  ok = ok && shadowed
  ok ? 42 | 1
}
`

func TestTryPassCompiled(t *testing.T) {
	code, abnormal := buildAndRun(t, "try_pass", tryPassProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestTryPassInterpreted(t *testing.T) {
	if got := interpretChecked(t, tryPassProgram); got != 42 {
		t.Fatalf("interpreter: got %d, want 42", got)
	}
}

// Refusals carry the try's position and are reported once.
func TestTryPassDiagnostics(t *testing.T) {
	prelude := "import(std)\nFault: type = | Bad\nstep: (n: u32): Result[u32, Fault] = n > u32(10) ? .Err(.Bad) | .Ok(n + u32(1))\nbump: (): () = {}\n"
	cases := map[string]struct{ src, want string }{
		"located in a loop": {prelude + `f: (n: u32): Result[u32, Fault] {
  i: u32 = 0
  while i < n {
    a: u32 = try step(i)
    i = a
  }
  .Ok(i)
}
main: (): i32 = 0
`, "8:14: try here does not return from the function"},
		"defer in the block": {prelude + `f: (n: u32): Result[u32, Fault] {
  defer bump()
  a: u32 = try step(n)
  .Ok(a)
}
main: (): i32 = 0
`, "try in a block with `defer`"},
		"last statement": {prelude + `f: (n: u32): Result[u32, Fault] {
  _ = try step(n)
}
main: (): i32 = 0
`, "try in the last statement of a block"},
	}
	for name, c := range cases {
		_, err := New().WithSource("bad.oak", c.src).EmitC().Get()
		if err == nil || !strings.Contains(err.Error(), c.want) {
			t.Fatalf("%s: want %q, got %v", name, c.want, err)
		}
		if n := strings.Count(err.Error(), CodeTryShape); n != 1 {
			t.Fatalf("%s: one refusal must be reported once, got %d:\n%v", name, n, err)
		}
	}
}
