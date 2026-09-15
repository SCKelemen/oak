package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Vector locals in registers across calls (docs/spec/94-assembler.md
// §9.ad, the optimization system's second increment): a calling function's
// vector locals live in v16–v31 and are saved around a call only when live
// after it, instead of in sixteen-byte slots reloaded at every use. The
// shapes: a vector live across a scalar call, one dead before the call, a
// loop-carried vector across a call in the loop, and a caller with more
// vector locals than the pool holds, which still lowers (the rest in
// slots). The scalar callee is exported and takes a variable argument, so
// neither inliner nor the literal folder removes the call; its result is
// masked to one bit, since a mask added to a whole fresh parameter is
// past the verifier's diagram budget with or without homes. The C backend is the oracle; the
// checker refuses any home read after a call that did not reload it.
const nativeVectorHomesProgram = `
// Exported, so the source-level inliner (compiler/inline.go, private leaf
// helpers) leaves the calls in place.
pub bump: (k: u32) -> u32 = k + u32(1)

live_across: (b: []u8, n: u32) -> u32 {
  v: simd.U8x16 = simd.load_u8x16(b, u32(0))
  k: u32 = bump(n) & u32(1)
  simd.movemask_u8x16(simd.eq_u8x16(v, simd.splat_u8x16(u8(7)))) + k
}

dead_before: (b: []u8) -> u32 {
  v: simd.U8x16 = simd.load_u8x16(b, u32(0))
  m: u32 = simd.movemask_u8x16(simd.eq_u8x16(v, simd.splat_u8x16(u8(7))))
  k: u32 = bump(m)
  k
}

carried: (b: []u8, n: u32) -> u32 {
  acc: simd.U32x4 = simd.splat_u32x4(u32(0))
  i: u32 = u32(0)
  while i < n {
    acc = simd.add_u32x4(acc, simd.splat_u32x4(bump(i)))
    i = i + u32(1)
  }
  simd.any_u32x4(simd.eq_u32x4(acc, simd.splat_u32x4(u32(0)))) ? u32(0) | u32(1)
}

many: (b: []u8, n: u32) -> u32 {
  a0: simd.U8x16 = simd.load_u8x16(b, u32(0))
  a1: simd.U8x16 = simd.load_u8x16(b, u32(1))
  a2: simd.U8x16 = simd.load_u8x16(b, u32(2))
  a3: simd.U8x16 = simd.load_u8x16(b, u32(3))
  a4: simd.U8x16 = simd.load_u8x16(b, u32(4))
  a5: simd.U8x16 = simd.load_u8x16(b, u32(5))
  a6: simd.U8x16 = simd.load_u8x16(b, u32(6))
  a7: simd.U8x16 = simd.load_u8x16(b, u32(7))
  a8: simd.U8x16 = simd.load_u8x16(b, u32(8))
  a9: simd.U8x16 = simd.load_u8x16(b, u32(9))
  a10: simd.U8x16 = simd.load_u8x16(b, u32(10))
  a11: simd.U8x16 = simd.load_u8x16(b, u32(11))
  a12: simd.U8x16 = simd.load_u8x16(b, u32(12))
  a13: simd.U8x16 = simd.load_u8x16(b, u32(13))
  k: u32 = bump(n) & u32(1)
  s: simd.U8x16 = simd.or_u8x16(simd.or_u8x16(simd.or_u8x16(a0, a1), simd.or_u8x16(a2, a3)), simd.or_u8x16(simd.or_u8x16(a4, a5), simd.or_u8x16(a6, a7)))
  t: simd.U8x16 = simd.or_u8x16(simd.or_u8x16(simd.or_u8x16(a8, a9), simd.or_u8x16(a10, a11)), simd.or_u8x16(a12, a13))
  simd.movemask_u8x16(simd.eq_u8x16(simd.or_u8x16(s, t), simd.splat_u8x16(u8(7)))) + k
}

main: (): i32 {
  buf: [32]u8
  i: u32 = u32(0)
  while i < u32(32) {
    buf[i] = i % u32(3) == u32(0) ? u8(7) | u8(1)
    i = i + u32(1)
  }
  b: []u8 = view(&buf)
  assert(live_across(b, u32(3)) == u32(0x9249))
  assert(dead_before(b) == u32(0x9249) + u32(1))
  assert(carried(b, u32(4)) == u32(1))
  assert(carried(b, u32(0)) == u32(0))
  assert(many(b, u32(0)) == u32(0xFFFF) + u32(1))
  42
}
`

func TestE2ENativeVectorHomes(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("vhomes.oak", nativeVectorHomesProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_vector_homes", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native vector homes: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"live_across", "dead_before", "carried", "many"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	for _, want := range []string{"live_across: 1 vector local(s) kept in registers across calls", "dead_before: 1 vector local(s) kept in registers across calls", "carried: 1 vector local(s) kept in registers across calls"} {
		if !strings.Contains(joined, want) {
			t.Errorf("want %q; diagnostics:\n%s", want, joined)
		}
	}
	if !strings.Contains(joined, "many: ") || !strings.Contains(joined, "vector local(s) kept in registers across calls") {
		t.Errorf("many must keep some vector locals in registers and the rest in slots; diagnostics:\n%s", joined)
	}
	if strings.Contains(joined, "keeps its vector slots") {
		t.Errorf("no body may fall back to slots; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_vector_homes_c", New().WithSource("vhomes.oak", nativeVectorHomesProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
