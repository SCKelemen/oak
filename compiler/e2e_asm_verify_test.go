package compiler

import (
	"strings"
	"testing"
)

// §8 verification at the asm gate: a wrong body never compiles; a proven
// body compiles and executes on both realizations.
func TestAsmVerificationRejectsMismatch(t *testing.T) {
	_, err := New().WithSource("wrong.oak", `
add_asm: (left, right: u32) -> u32 = left + right

main: (): i32 {
  assert(add_asm(u32(40), u32(2)) == u32(42))
  42
}
`).WithAsmUnit("wrong.arm64.oakasm", `
add_asm: (left, right: u32) -> u32 = {
  bind w0 = left
  bind w1 = right
  sub w0, w0, w1
  ret
}
`).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "disagrees with its Oak body") {
		t.Fatalf("a body disagreeing with its Oak specification must be rejected, got %v", err)
	}
}

func TestE2EAsmVerifiedFallbackExecutesBothWays(t *testing.T) {
	requireArm64Host(t)
	comp := New().WithSource("verified.oak", `
scale: (a: u64) -> u64 = (a + u64(2)) << 3

main: (): i32 {
  assert(scale(u64(3)) == u64(40))
  42
}
`).WithAsmUnit("scale.arm64.oakasm", `
scale: (a: u64) -> u64 = {
  bind x0 = a
  clobber x9
  add x9, x0, #2
  lsl x0, x9, #3
  ret
}
`)
	for _, flags := range [][]string{nil, {"-DOAK_PORTABLE_INTRINSICS"}} {
		_, code, abnormal := buildAndRunFrom(t, "verified", comp, flags...)
		if abnormal || code != 42 {
			t.Fatalf("flags %v: exit = (%d, abnormal=%v), want 42", flags, code, abnormal)
		}
	}
}

// A conditional body: the Oak `a < b ? b | a` is the specification of a
// cmp/csel pair; proven at the asm gate, then executed both ways.
func TestE2EAsmVerifiedConditionalExecutesBothWays(t *testing.T) {
	requireArm64Host(t)
	comp := New().WithSource("max.oak", `
max32: (a, b: u32) -> u32 = a < b ? b | a

main: (): i32 {
  assert(max32(u32(40), u32(2)) == u32(40))
  assert(max32(u32(2), u32(42)) == u32(42))
  assert(max32(u32(7), u32(7)) == u32(7))
  42
}
`).WithAsmUnit("max.arm64.oakasm", `
max32: (a, b: u32) -> u32 = {
  bind w0 = a
  bind w1 = b
  cmp w0, w1
  csel w0, w1, w0, lo
  ret
}
`)
	for _, flags := range [][]string{nil, {"-DOAK_PORTABLE_INTRINSICS"}} {
		_, code, abnormal := buildAndRunFrom(t, "verified_cond", comp, flags...)
		if abnormal || code != 42 {
			t.Fatalf("flags %v: exit = (%d, abnormal=%v), want 42", flags, code, abnormal)
		}
	}
	// Acyclic branches: a clamp with two conditional branches and three
	// paths, proven against its nested Oak conditional and run both ways.
	clamp := New().WithSource("clamp.oak", `
clamp: (v, lo, hi: u32) -> u32 = v < lo ? lo | (v > hi ? hi | v)

main: (): i32 {
  assert(clamp(u32(5), u32(10), u32(20)) == u32(10))
  assert(clamp(u32(50), u32(10), u32(20)) == u32(20))
  assert(clamp(u32(15), u32(10), u32(20)) == u32(15))
  42
}
`).WithAsmUnit("clamp.arm64.oakasm", `
clamp: (v, lo, hi: u32) -> u32 = {
  bind w0 = v
  bind w1 = lo
  bind w2 = hi
  cmp w0, w1
  b.lo low
  cmp w0, w2
  b.hi high
  ret
low:
  mov w0, w1
  ret
high:
  mov w0, w2
  ret
}
`)
	for _, flags := range [][]string{nil, {"-DOAK_PORTABLE_INTRINSICS"}} {
		_, code, abnormal := buildAndRunFrom(t, "verified_clamp", clamp, flags...)
		if abnormal || code != 42 {
			t.Fatalf("clamp, flags %v: exit = (%d, abnormal=%v), want 42", flags, code, abnormal)
		}
	}
	// Span memory: a guarded pair sum over a view, proven against the Oak
	// body that indexes the view under the same length guard.
	pairSum := New().WithSource("pair.oak", `
pair_sum: (v: []u32) -> u32 = len(v) < u32(2) ? u32(0) | v[0] + v[1]

main: (): i32 {
  buf: [4]u32
  buf[0] = u32(40)
  buf[1] = u32(2)
  assert(pair_sum(view(&buf)) == u32(42))
  one: [1]u32
  assert(pair_sum(view(&one)) == u32(0))
  42
}
`).WithAsmUnit("pair.arm64.oakasm", `
pair_sum: (v: []u32) -> u32 = {
  bind x0, w1 = v
  clobber w9
  cmp w1, #2
  b.lo short
  ldr w9, [x0]
  ldr w0, [x0, #4]
  add w0, w0, w9
  ret
short:
  mov w0, #0
  ret
}
`)
	for _, flags := range [][]string{nil, {"-DOAK_PORTABLE_INTRINSICS"}} {
		_, code, abnormal := buildAndRunFrom(t, "verified_pair", pairSum, flags...)
		if abnormal || code != 42 {
			t.Fatalf("pair_sum, flags %v: exit = (%d, abnormal=%v), want 42", flags, code, abnormal)
		}
	}
	// A counted loop: popcount of the low byte, the Oak `while` and the asm
	// loop both unrolled eight times and proven equal bit by bit.
	popcount := New().WithSource("pop.oak", `
popcount8: (v: u32) -> u32 {
  x: u32 = v
  count: u32 = u32(0)
  i: u32 = u32(0)
  while i < u32(8) {
    count = count + (x & u32(1))
    x = x >> u32(1)
    i = i + u32(1)
  }
  count
}

main: (): i32 {
  assert(popcount8(u32(0xFF)) == u32(8))
  assert(popcount8(u32(0x1FF)) == u32(8))
  assert(popcount8(u32(0xA5)) == u32(4))
  assert(popcount8(u32(0)) == u32(0))
  42
}
`).WithAsmUnit("pop.arm64.oakasm", `
popcount8: (v: u32) -> u32 = {
  bind w0 = v
  clobber w9, w10, w11
  mov w9, #0
  mov w10, #8
loop:
  and w11, w0, #1
  add w9, w9, w11
  lsr w0, w0, #1
  sub w10, w10, #1
  cmp w10, #0
  b.ne loop
  mov w0, w9
  ret
}
`)
	for _, flags := range [][]string{nil, {"-DOAK_PORTABLE_INTRINSICS"}} {
		_, code, abnormal := buildAndRunFrom(t, "verified_popcount", popcount, flags...)
		if abnormal || code != 42 {
			t.Fatalf("popcount8, flags %v: exit = (%d, abnormal=%v), want 42", flags, code, abnormal)
		}
	}
	// Register-offset addressing: a counted loop walking a view by element
	// index, proven against the Oak loop and run both ways.
	sum4 := New().WithSource("sum4.oak", `
sum4: (v: []u32) -> u32 {
  len(v) < u32(4) ? { u32(0) } | {
    acc: u32 = u32(0)
    i: u32 = u32(0)
    while i < u32(4) {
      acc = acc + v[i]
      i = i + u32(1)
    }
    acc
  }
}

main: (): i32 {
  buf: [4]u32
  buf[0] = u32(10)
  buf[1] = u32(20)
  buf[2] = u32(5)
  buf[3] = u32(7)
  assert(sum4(view(&buf)) == u32(42))
  short: [2]u32
  assert(sum4(view(&short)) == u32(0))
  42
}
`).WithAsmUnit("sum4.arm64.oakasm", `
sum4: (v: []u32) -> u32 = {
  bind x0, w1 = v
  clobber w9, w10, w11
  mov w9, #0
  mov w10, #0
loop:
  cmp w9, #4
  b.hs done
  cmp w1, #4
  b.lo short
  ldr w11, [x0, w9, uxtw #2]
  add w10, w10, w11
  add w9, w9, #1
  b loop
done:
  mov w0, w10
  ret
short:
  mov w0, #0
  ret
}
`)
	for _, flags := range [][]string{nil, {"-DOAK_PORTABLE_INTRINSICS"}} {
		_, code, abnormal := buildAndRunFrom(t, "verified_sum4", sum4, flags...)
		if abnormal || code != 42 {
			t.Fatalf("sum4, flags %v: exit = (%d, abnormal=%v), want 42", flags, code, abnormal)
		}
	}
	// The wrong condition never compiles.
	_, err := New().WithSource("max.oak", `
max32: (a, b: u32) -> u32 = a < b ? b | a

main: (): i32 {
  assert(max32(u32(1), u32(2)) == u32(2))
  42
}
`).WithAsmUnit("max.arm64.oakasm", `
max32: (a, b: u32) -> u32 = {
  bind w0 = a
  bind w1 = b
  cmp w0, w1
  csel w0, w1, w0, hi
  ret
}
`).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "disagrees with its Oak body") {
		t.Fatalf("csel hi for a < b must be rejected at the gate, got %v", err)
	}
}
