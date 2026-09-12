package compiler

import (
	"strings"
	"testing"
)

// Vector loads and stores under a proving extent fact
// (docs/spec/50-borrowing.md, vector access; typechecker/extents.go
// recordVectorAccessProof): the sixty-four-byte stream idiom
// `while len(v) >= 64 && off <= len(v) - 64` proves loads at `off` through
// `off + 48`; a constant offset is proven by a min-length fact; a load the
// facts do not cover stays checked and still traps out of range.
const simdProvenProgram = `
scan: (bytes: []u8): u32 {
  acc: simd.U8x16 = simd.splat_u8x16(u8(0))
  off: u32 = u32(0)
  while len(bytes) >= u32(64) && off <= len(bytes) - u32(64) {
    a: simd.U8x16 = simd.load_u8x16(bytes, off)
    d: simd.U8x16 = simd.load_u8x16(bytes, off + u32(48))
    // 49 + 15 reaches past the guard's bound of 63: not proven.
    e: simd.U8x16 = simd.load_u8x16(bytes, off + u32(49))
    acc = simd.or_u8x16(acc, simd.or_u8x16(simd.or_u8x16(a, d), e))
    off = off + u32(64)
  }
  len(bytes) >= u32(16) ? {
    acc = simd.or_u8x16(acc, simd.load_u8x16(bytes, u32(0)))
  }
  simd.any_u8x16(acc) ? u32(1) | u32(0)
}

fill: (out: [*]u8): () {
  off: u32 = u32(0)
  while len(out) >= u32(16) && off <= len(out) - u32(16) {
    simd.store_u8x16(out, off, simd.splat_u8x16(u8(7)))
    off = off + u32(16)
  }
}

main: (): u32 {
  buf: [130]u8
  fill(span(&buf))
  v: []u8 = view(&buf)
  scan(v) == u32(1) && buf[u32(129)] == u8(0) && buf[u32(127)] == u8(7) ? u32(42) | u32(1)
}
`

func TestE2ESimdVectorAccessProvenUnderExtentFacts(t *testing.T) {
	output, err := New().WithSource("simd_proven.oak", simdProvenProgram).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	// Two loads under the stream guard and one under the min-length fact
	// are proven; the load at off + 49 is not. The counts are of call
	// sites (the helper definitions take a typed parameter list).
	if got := strings.Count(output, "oak_simd_load_u8x16_proven( bytes,"); got != 3 {
		t.Fatalf("expected 3 proven vector loads, found %d:\n%s", got, output)
	}
	if got := strings.Count(output, "oak_simd_load_u8x16( bytes,"); got != 1 {
		t.Fatalf("expected 1 checked vector load, found %d:\n%s", got, output)
	}
	if got := strings.Count(output, "oak_simd_store_u8x16_proven( out,"); got != 1 {
		t.Fatalf("expected 1 proven vector store, found %d:\n%s", got, output)
	}
	for _, variant := range []struct {
		name  string
		flags []string
	}{{"neon", nil}, {"portable", []string{"-DOAK_PORTABLE_INTRINSICS"}}} {
		_, exit, abnormal := buildAndRunOutput(t, "simd_proven_"+variant.name, simdProvenProgram, variant.flags...)
		if abnormal || exit != 42 {
			t.Fatalf("%s: exit %d abnormal %v", variant.name, exit, abnormal)
		}
	}
}
