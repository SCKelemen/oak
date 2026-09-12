package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Records across the call boundary through the native backend
// (docs/spec/94-assembler.md §9, seventh increment): AAPCS64 composite
// passing — a record of up to 16 bytes travels as x-register chunks (in and
// out), a larger one by reference to a copy the caller owns and, as a
// result, through the area the caller passes in x8. Every function is
// lowered natively, so both sides of each call follow the same rules; the
// C backend's realization of the same program is the oracle, which also
// checks the layouts agree with the C compiler's.
const nativeRecordABIProgram = `
Point: type = struct {
  x: i32
  y: i32
}

Pair: type = struct {
  lo: u64
  hi: u64
}

Wide: type = struct {
  a: u64
  b: u64
  c: u32
  tag: u8
}

Small: type = struct {
  n: u16
  m: u8
}

shift: (p: Point, dx: i32) -> Point = Point { x: p.x + dx, y: p.y }

swap: (p: Pair) -> Pair = Pair { lo: p.hi, hi: p.lo }

// A 21-byte record (24 with padding) in by reference and out through x8;
// the callee mutates its own copy without touching the caller's.
bump: (w: Wide, k: u64) -> Wide {
  w.a = w.a + k
  w.tag = w.tag + u8(1)
  w
}

wide_sum: (w: Wide) -> u64 = w.a + w.b + u64(w.c) + u64(w.tag)

// A record result chosen by a condition.
pick: (a: Small, b: Small, first: Bool) -> Small = first ? a | b

small_total: (s: Small) -> u32 = u32(s.n) + u32(s.m)

// A record argument that is itself a call's result, and a chain of
// by-reference calls with scalar arguments interleaved.
chain: (n: u64) -> u64 {
  w: Wide = Wide { a: n, b: u64(2), c: u32(3), tag: u8(4) }
  w2: Wide = bump(bump(w, u64(10)), u64(100))
  wide_sum(w2) * u64(1000) + wide_sum(w)
}

main: (): i32 {
  p: Point = Point { x: 11, y: 31 }
  q: Point = shift(p, 9)
  assert(q.x == 20)
  assert(q.y == 31)
  assert(p.x == 11)
  pr: Pair = swap(Pair { lo: u64(1), hi: u64(2) })
  assert(pr.lo == u64(2))
  assert(pr.hi == u64(1))
  assert(chain(u64(1)) == u64(122010))
  a: Small = Small { n: u16(300), m: u8(7) }
  b: Small = Small { n: u16(1), m: u8(1) }
  assert(small_total(pick(a, b, true)) == u32(307))
  assert(small_total(pick(a, b, false)) == u32(2))
  42
}
`

func TestE2ENativeRecordABI(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("record_abi.oak", nativeRecordABIProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_record_abi", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native record ABI: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"shift", "swap", "bump", "wide_sum", "pick", "small_total", "chain", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_record_abi_c", New().WithSource("record_abi.oak", nativeRecordABIProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_record_abi_portable", New().WithSource("record_abi.oak", nativeRecordABIProgram).WithNativeBodies(), "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
		t.Fatalf("portable realization: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// One side native, the other C: a natively lowered function called from a
// C-compiled one and vice versa must agree on the composite rules — the
// mixed program lowers only the leaves natively (main stays in C because
// it uses a feature outside the subset).
const nativeRecordMixedProgram = `
Wide: type = struct {
  a: u64
  b: u64
  c: u32
  tag: u8
}

Pair: type = struct {
  lo: u64
  hi: u64
}

bump: (w: Wide, k: u64) -> Wide {
  w.a = w.a + k
  w.tag = w.tag + u8(1)
  w
}

swap: (p: Pair) -> Pair = Pair { lo: p.hi, hi: p.lo }

total: (w: Wide) -> u64 = w.a + w.b + u64(w.c) + u64(w.tag)

main: (): i32 {
  // A string local keeps main in the C backend.
  label: string = "mixed"
  w: Wide = Wide { a: u64(5), b: u64(6), c: u32(7), tag: u8(8) }
  w2: Wide = bump(w, u64(100))
  p: Pair = swap(Pair { lo: u64(3), hi: u64(9) })
  assert(total(w2) == u64(127))
  assert(total(w) == u64(26))
  assert(p.lo == u64(9))
  assert(len(label) == u32(5))
  42
}
`

func TestE2ENativeRecordMixed(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("record_mixed.oak", nativeRecordMixedProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_record_mixed", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("mixed record ABI: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"bump", "swap", "total"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	if strings.Contains(joined, "asm unit main:") {
		t.Errorf("main must stay in the C backend for this test to exercise the C caller; diagnostics:\n%s", joined)
	}
}
