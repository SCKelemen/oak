package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

// Portable SIMD through the native backend's RV64 lane (docs/spec/93-simd.md
// section 1.4, nativegen/rv64_simd.go): the integer fixed-vector corpus of
// e2e_native_simd_test.go — double_it's vector signature under the RVV
// psABI contract (v8 in, v8 out; the native entry is double_it_rvv_abi and
// the C emitter's shim converts the lane-array struct) — without the
// ctz/popcount helpers (no Zbb on the lane), lowered to RVV under
// `vsetivli` configurations, admitted by the checker through the slack
// guard and the frame vector rule, and executed under QEMU with V beside
// the C backend's RVV realization.

const nativeRV64SimdProgram = `
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

// Wider lanes through a span of their own width: u32 elements loaded at
// index 4 of a 12-element view under the slack guard, summed by lanes.
wide_load: (w: []u32) -> u32 {
  v: simd.U32x4 = simd.load_u32x4(w, u32(4))
  s: simd.U32x4 = simd.sub_u32x4(v, simd.splat_u32x4(u32(1)))
  simd.movemask_u32x4(simd.eq_u32x4(s, simd.splat_u32x4(u32(6))))
}

// A vector local across a call: the value must survive in a slot.
across_call: (b: []u8) -> u32 {
  v: simd.U8x16 = simd.load_u8x16(b, u32(0))
  k: u32 = words_zero()
  simd.movemask_u8x16(simd.eq_u8x16(v, simd.splat_u8x16(u8(7)))) + k
}

words_zero: () -> u32 = u32(0)

// A vector across a native-to-native call: double_it keeps the vector
// register contract at its native entry (v8 in, v8 out under the RVV psABI).
double_it: (v: simd.U8x16) -> simd.U8x16 = simd.add_u8x16(v, v)

doubled_mask: (b: []u8) -> u32 {
  d: simd.U8x16 = double_it(simd.load_u8x16(b, u32(0)))
  simd.movemask_u8x16(simd.eq_u8x16(d, simd.splat_u8x16(u8(14))))
}

// A vector across the C boundary: a foreign pointer local keeps this
// caller on the C backend, so it reaches double_it through the converting
// shim under its Oak name (the lane-array struct in, vle8 into v8).
c_side: (a: []u8) -> u32 {
  nothing: c.Ptr = c.null()
  _ = nothing
  v: simd.U8x16 = double_it(simd.load_u8x16(a, u32(0)))
  simd.movemask_u8x16(simd.eq_u8x16(v, simd.splat_u8x16(u8(14))))
}

main: (): u32 {
  data: [32]u8
  i: u32 = u32(0)
  while i < u32(16) {
    data[i] = u8_trunc_u32(i)
    data[i + u32(16)] = u8_trunc_u32(i + u32(100))
    i = i + u32(1)
  }
  wide: [12]u32
  j: u32 = u32(0)
  while j < u32(12) {
    wide[j] = j
    j = j + u32(1)
  }
  dst: [16]u8
  combine_store(span(&dst), view(&data))
  total: u32 = u32(0)
  k: u32 = u32(0)
  while k < u32(16) {
    total = total + u32(dst[k])
    k = k + u32(1)
  }
  // (b >> 2): 24; min(b, 5): 0+1+2+3+4+5*11 = 65; max(b, 10): 10*11 + 11+12+13+14+15 = 175; subs(b, 8): 0..7 = 28
  ok1: Bool = lanes_mask(view(&data)) == u32(256)
  ok2: Bool = logic(view(&data)) == u32(43691)
  ok3: Bool = total == u32(292)
  ok4: Bool = shuffle(view(&data)) == u32(65543)
  ok5: Bool = words() == u32(11)
  ok6: Bool = across_call(view(&data)) == u32(128)
  // lanes 4..7 hold 4, 5, 6, 7; minus one, lane 3 equals 6: bit 3.
  ok7: Bool = wide_load(view(&wide)) == u32(8)
  ok8: Bool = doubled_mask(view(&data)) == u32(128)
  ok9: Bool = c_side(view(&data)) == u32(128)
  ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 && ok8 && ok9 ? u32(42) | (ok1 ? u32(0) | u32(1)) + (ok2 ? u32(0) | u32(2)) + (ok3 ? u32(0) | u32(4)) + (ok4 ? u32(0) | u32(8)) + (ok5 ? u32(0) | u32(16)) + (ok6 ? u32(0) | u32(32)) + (ok7 ? u32(0) | u32(64)) + (ok8 ? u32(0) | u32(128)) + (ok9 ? u32(0) | u32(200))
}
`

// The functions the rv64 lane lowers; main addresses owned arrays through
// frame addresses and stays with the C backend on both lanes.
var nativeRV64SimdFunctions = []string{"lanes_mask", "logic", "combine_store", "shuffle", "words", "wide_load", "across_call", "words_zero", "double_it_rvv_abi", "doubled_mask"}

// nativeRV64LowerCPU is nativeRV64Lower for a named processor.
func nativeRV64LowerCPU(t *testing.T, tgt target.Target, cpu, source string) (NativeOutput, []string) {
	t.Helper()
	var infos []string
	comp := New().WithSource("native.oak", source).WithTarget(tgt).WithCPU(cpu).WithNativeBodies().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	native, err := comp.EmitNative(asm.ELF).Get()
	if err != nil {
		t.Fatalf("rv64 native bodies: %v\n%s", err, strings.Join(infos, "\n"))
	}
	return native, infos
}

func TestE2ENativeRV64SimdLowers(t *testing.T) {
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	native, infos := nativeRV64LowerCPU(t, bare, "generic_rv64+m+v", nativeRV64SimdProgram)
	joined := strings.Join(infos, "\n")
	t.Log(joined)
	for _, fn := range nativeRV64SimdFunctions {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the rv64 lane; diagnostics:\n%s", fn, joined)
		}
	}
	// The vector-signature entry and its caller are proven by the verifier
	// under the v8 contract (docs/spec/94-assembler.md §9).
	for _, fn := range []string{"double_it_rvv_abi", "doubled_mask"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s was not proven by the verifier; diagnostics:\n%s", fn, joined)
		}
	}
	if native.Object == nil {
		t.Fatal("no companion object")
	}
	if !strings.Contains(native.C, "__riscv_v") {
		t.Error("the C backend must carry the RVV realization for the bodies it keeps")
	}
	// The C emitter defines double_it as a converting shim over its native
	// entry (the lane-array struct loaded into a vector register), and
	// c_side, kept on the C backend by its foreign pointer, calls it.
	for _, text := range []string{"vuint8m1_t", "double_it_rvv_abi", "__riscv_vle8_v_u8m1", "__riscv_vse8_v_u8m1"} {
		if !strings.Contains(native.C, text) {
			t.Errorf("the emitted C lacks %q (the RVV shim)", text)
		}
	}
	if !strings.Contains(joined, "c_side left to the C backend") {
		t.Errorf("c_side must stay with the C backend; diagnostics:\n%s", joined)
	}
	// Without V on the processor the vector bodies stay with the C backend,
	// whose portable lane loop realizes them.
	_, infos = nativeRV64Lower(t, bare, nativeRV64SimdProgram)
	joined = strings.Join(infos, "\n")
	if !strings.Contains(joined, "lanes_mask left to the C backend (the fixed simd vectors need the vector extension") {
		t.Fatalf("a processor without V must leave the vector bodies to the C backend:\n%s", joined)
	}
}

// The corpus executes under QEMU with V: every function the lane lowered,
// encoded into the companion object, linked beside the C shell, exits 42 —
// and so does the C backend alone, at two vector lengths.
func TestE2ENativeRV64SimdUnderQEMU(t *testing.T) {
	skipInShort(t)
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	native, infos := nativeRV64LowerCPU(t, bare, "generic_rv64+m+v", nativeRV64SimdProgram)
	joined := strings.Join(infos, "\n")
	for _, fn := range nativeRV64SimdFunctions {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Fatalf("%s was not lowered by the rv64 lane; diagnostics:\n%s", fn, joined)
		}
	}
	for _, vlen := range []int{128, 256} {
		if out := runNativeRV64BareWith(t, "native_rv64_simd", native, nativeRV64Run{vector: true, vlen: vlen}); !strings.Contains(out, "0000002a\n") {
			t.Fatalf("native vectors under QEMU (VLEN %d) did not exit 42:\n%s", vlen, out)
		}
	}
	cOnly, err := New().WithSource("native.oak", nativeRV64SimdProgram).WithTarget(bare).WithCPU("generic_rv64+m+v").EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if out := runNativeRV64BareWith(t, "native_rv64_simd_c", NativeOutput{C: cOnly}, nativeRV64Run{vector: true, vlen: 128}); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("C backend under QEMU did not exit 42:\n%s", out)
	}
}
