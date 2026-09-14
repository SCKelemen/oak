package compiler

import (
	"os"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Portable SIMD through the native backend (docs/spec/93-simd.md section
// 1.4, nativegen/simd.go): every lowered operation exercised over known
// bytes, each function's result a number the C backend and the portable
// realization must reproduce. The functions take views and spans, so the
// loads and stores go through the length-checked idiom.
const nativeSimdProgram = `
// load, splat, add, eq, movemask: bytes 0..15 plus 120, equal to 128 at lane 8.
lanes_mask: (b: []u8) -> u32 {
  v: simd.U8x16 = simd.load_u8x16(b, u32(0))
  w: simd.U8x16 = simd.add_u8x16(v, simd.splat_u8x16(u8(120)))
  simd.movemask_u8x16(simd.eq_u8x16(w, simd.splat_u8x16(u8(128))))
}

// xor, or, and, any, all: 1 + 0 + 43690.
logic: (b: []u8) -> u32 {
  v: simd.U8x16 = simd.load_u8x16(b, u32(0))
  zero: simd.U8x16 = simd.xor_u8x16(v, v)
  fours: simd.U8x16 = simd.or_u8x16(zero, simd.splat_u8x16(u8(4)))
  odd: simd.U8x16 = simd.and_u8x16(v, simd.splat_u8x16(u8(1)))
  a: u32 = simd.all_u8x16(fours) ? u32(1) | u32(0)
  n: u32 = simd.any_u8x16(zero) ? u32(100) | u32(0)
  a + n + simd.movemask_u8x16(simd.eq_u8x16(odd, simd.splat_u8x16(u8(1))))
}

// min, max, subs, shr through a store: dst holds (b >> 2) + min(b, 5) + max(b, 10) + subs(b, 8).
combine_store: (dst: [*]u8, b: []u8) -> () {
  v: simd.U8x16 = simd.load_u8x16(b, u32(0))
  s: simd.U8x16 = simd.shr_u8x16(v, u32(2))
  m: simd.U8x16 = simd.min_u8x16(v, simd.splat_u8x16(u8(5)))
  x: simd.U8x16 = simd.max_u8x16(v, simd.splat_u8x16(u8(10)))
  d: simd.U8x16 = simd.subs_u8x16(v, simd.splat_u8x16(u8(8)))
  simd.store_u8x16(dst, u32(0), simd.add_u8x16(simd.add_u8x16(s, m), simd.add_u8x16(x, d)))
}

// tbl and prev: 65535 + 8.
shuffle: (b: []u8) -> u32 {
  t: simd.U8x16 = simd.load_u8x16(b, u32(0))
  threes: simd.U8x16 = simd.tbl_u8x16(t, simd.splat_u8x16(u8(3)))
  mask_t: u32 = simd.movemask_u8x16(simd.eq_u8x16(threes, simd.splat_u8x16(u8(3))))
  p: simd.U8x16 = simd.prev_u8x16(simd.load_u8x16(b, u32(0)), simd.load_u8x16(b, u32(16)), u32(4))
  mask_p: u32 = simd.movemask_u8x16(simd.eq_u8x16(p, simd.splat_u8x16(u8(15))))
  mask_t + mask_p
}

// u32 lanes: 3 + 10 = 13 in every lane, so any and all of eq both hold;
// min against 5 leaves 5 everywhere, so eq with 13 fails in every lane.
words: () -> u32 {
  v: simd.U32x4 = simd.splat_u32x4(u32(3))
  s: simd.U32x4 = simd.add_u32x4(v, simd.splat_u32x4(u32(10)))
  hit: simd.U32x4 = simd.eq_u32x4(s, simd.splat_u32x4(u32(13)))
  low: simd.U32x4 = simd.min_u32x4(s, simd.splat_u32x4(u32(5)))
  miss: simd.U32x4 = simd.eq_u32x4(low, simd.splat_u32x4(u32(13)))
  (simd.any_u32x4(hit) ? u32(1) | u32(0)) + (simd.all_u32x4(hit) ? u32(10) | u32(0)) + (simd.any_u32x4(miss) ? u32(100) | u32(0))
}

// A vector local across a call: the value must survive in a slot.
across_call: (b: []u8) -> u32 {
  v: simd.U8x16 = simd.load_u8x16(b, u32(0))
  k: u32 = words_zero()
  simd.movemask_u8x16(simd.eq_u8x16(v, simd.splat_u8x16(u8(7)))) + k
}

words_zero: () -> u32 = u32(0)

// A vector across a native-to-native call: double_it keeps the vector
// register contract at its native entry.
double_it: (v: simd.U8x16) -> simd.U8x16 = simd.add_u8x16(v, v)

doubled_mask: (b: []u8) -> u32 {
  d: simd.U8x16 = double_it(simd.load_u8x16(b, u32(0)))
  simd.movemask_u8x16(simd.eq_u8x16(d, simd.splat_u8x16(u8(14))))
}

// A vector across the C boundary: a foreign pointer local keeps this
// caller on the C backend (five views no longer do, since arguments
// beyond the registers cross the stack), so it reaches double_it through
// the converting shim under its Oak name.
c_side: (a: []u8, b: []u8, cc: []u8, d: []u8, e: []u8) -> u32 {
  nothing: c.Ptr = c.null()
  _ = nothing
  v: simd.U8x16 = double_it(simd.load_u8x16(a, u32(0)))
  simd.movemask_u8x16(simd.eq_u8x16(v, simd.splat_u8x16(u8(14)))) + len(b) + len(cc) + len(d) + len(e) - u32(128)
}

// The scalar helpers: 3 + 8 + 64 + 64.
bits: () -> u32 {
  simd.ctz_u32(u32(40)) + simd.popcount_u32(u32(255)) + u32_trunc_u64(simd.ctz_u64(u64(0))) + u32_trunc_u64(simd.popcount_u64(u64(18446744073709551615)))
}

main: (): u32 {
  data: [32]u8
  i: u32 = u32(0)
  while i < u32(16) {
    data[i] = u8_trunc_u32(i)
    data[i + u32(16)] = u8_trunc_u32(i + u32(100))
    i = i + u32(1)
  }
  dst: [16]u8
  combine_store(span(&dst), view(&data))
  total: u32 = u32(0)
  j: u32 = u32(0)
  while j < u32(16) {
    total = total + u32(dst[j])
    j = j + u32(1)
  }
  // (b >> 2): 24; min(b, 5): 0+1+2+3+4+5*11 = 65; max(b, 10): 10*11 + 11+12+13+14+15 = 175; subs(b, 8): 0..7 = 28
  ok1: Bool = lanes_mask(view(&data)) == u32(256)
  ok2: Bool = logic(view(&data)) == u32(43691)
  ok3: Bool = total == u32(292)
  ok4: Bool = shuffle(view(&data)) == u32(65543)
  ok5: Bool = words() == u32(11)
  ok6: Bool = across_call(view(&data)) == u32(128)
  ok7: Bool = bits() == u32(139)
  ok8: Bool = doubled_mask(view(&data)) == u32(128)
  ok9: Bool = c_side(view(&data), view(&data), view(&data), view(&data), view(&data)) == u32(128)
  ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 && ok8 && ok9 ? u32(42) | (ok1 ? u32(0) | u32(1)) + (ok2 ? u32(0) | u32(2)) + (ok3 ? u32(0) | u32(4)) + (ok4 ? u32(0) | u32(8)) + (ok5 ? u32(0) | u32(16)) + (ok6 ? u32(0) | u32(32)) + (ok7 ? u32(0) | u32(64)) + (ok8 ? u32(0) | u32(128)) + (ok9 ? u32(0) | u32(200))
}
`

func TestE2ENativeSimd(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("native_simd.oak", nativeSimdProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_simd", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native simd: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	// double_it carries a vector in its signature, so its native entry is
	// the suffixed symbol (nativegen.VectorContractSuffix).
	for _, fn := range []string{"lanes_mask", "logic", "combine_store", "shuffle", "words", "across_call", "bits", "double_it_neon_abi", "doubled_mask"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	if !strings.Contains(joined, "c_side left to the C backend") {
		t.Errorf("c_side must stay on the C backend (the shim's caller); diagnostics:\n%s", joined)
	}
	// The verifier follows the vector file (asm/verify_vector.go): every
	// straight-line vector body is proven against its Oak body, the
	// vector-contract callee on both halves of v0, and doubled_mask
	// through the expanded callee (nativegen/inline.go) inlined on the Oak
	// side too, and combine_store in the span memory its vector store
	// leaves (asm/effects.go). across_call makes a call: trusted, as its
	// scalar counterparts are.
	for _, fn := range []string{"lanes_mask", "logic", "combine_store", "shuffle", "words", "bits", "double_it_neon_abi", "doubled_mask"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s must be proven equal to its Oak body; diagnostics:\n%s", fn, joined)
		}
	}
	if !strings.Contains(joined, "asm unit double_it_neon_abi: proven equal to its Oak body at the bit level (128-bit vector result, both halves)") {
		t.Errorf("double_it_neon_abi must be proven on both halves of the vector result; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_simd_c", New().WithSource("native_simd.oak", nativeSimdProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// The UTF-8 kernel of benchmarks/native (the simdutf lookup algorithm):
// the straight-line vector helpers are proven, the two-block composition
// is evidence (the bit-level decision exceeds its budget), and the loop
// kernel is evidence too (its three data-dependent loops summarized, the
// witnesses agree, every loop variable is coupled, and the error
// accumulator's obligation exceeds the node budget) — the verdicts
// docs/notes/proof-chain-audit-2026-09.md records for the vector link.
func TestE2ENativeSimdKernelVerdicts(t *testing.T) {
	requireArm64Host(t)
	src, err := os.ReadFile("../benchmarks/native/utf8_valid.oak")
	if err != nil {
		t.Skip(err)
	}
	var infos []string
	comp := New().WithSource("utf8_valid.oak", string(src)).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	if _, err := comp.EmitNative(HostObjectFormat()).Get(); err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	joined := strings.Join(infos, "\n")
	for _, fn := range []string{"special_cases_neon_abi", "check_block_neon_abi"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven equal to its Oak body at the bit level (128-bit vector result, both halves)") {
			t.Errorf("%s must be proven on both halves of the vector result; diagnostics:\n%s", fn, joined)
		}
	}
	if !strings.Contains(joined, "asm unit check_blocks_neon_abi: agrees with its Oak body on every witness input") && !strings.Contains(joined, "asm unit check_blocks_neon_abi: proven") {
		t.Errorf("check_blocks_neon_abi must be evidence or proof; diagnostics:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit valid_with: agrees with its Oak body on") || !strings.Contains(joined, "concrete inputs (evidence, not proof: one iteration of loop 1 was not proven to preserve error") || !strings.Contains(joined, "exceeded its node budget") {
		t.Errorf("valid_with must be witnessed evidence with every loop variable coupled and only the error obligation past the budget; diagnostics:\n%s", joined)
	}
}
