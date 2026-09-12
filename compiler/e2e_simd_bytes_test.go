package compiler

import "testing"

// The byte-classification operations of docs/spec/93-simd.md section 1.2:
// saturating subtract, lane shift right, the 16-entry byte-table lookup,
// and the cross-block byte shift. Each program folds every lane of a
// result into an 8-bit checksum; the interpreter (Oak.Simd's lane
// semantics), the NEON lowering, and the portable lane loop must agree.
const simdBytesProgram = `
fold: (v: simd.U8x16): u32 {
  storage: [16]u8
  simd.store_u8x16(span(&storage), u32(0), v)
  acc: u32 = 7
  i: u32 = 0
  while i < u32(16) {
    acc = (acc * u32(31) + u32(storage[i])) % u32(251)
    i = i + u32(1)
  }
  acc
}

main: (): u32 {
  a_bytes: [16]u8 = [u8(0), u8(1), u8(2), u8(3), u8(4), u8(5), u8(6), u8(7), u8(8), u8(9), u8(10), u8(11), u8(12), u8(13), u8(14), u8(15)]
  b_bytes: [16]u8 = [u8(200), u8(191), u8(15), u8(16), u8(255), u8(0), u8(128), u8(1), u8(3), u8(17), u8(33), u8(100), u8(12), u8(240), u8(224), u8(31)]
  a: simd.U8x16 = simd.load_u8x16(view(&a_bytes), u32(0))
  b: simd.U8x16 = simd.load_u8x16(view(&b_bytes), u32(0))
  acc: u32 = 0
  // subs saturates at zero in both directions
  acc = acc + fold(simd.subs_u8x16(a, b))
  acc = acc + fold(simd.subs_u8x16(b, a))
  // shr by 4 (nibbles), by 0, and by 7
  acc = acc + fold(simd.shr_u8x16(b, u32(4)))
  acc = acc + fold(simd.shr_u8x16(b, u32(0)))
  acc = acc + fold(simd.shr_u8x16(b, u32(7)))
  // tbl: indices below 16 select, 16 and above give 0
  acc = acc + fold(simd.tbl_u8x16(b, a))
  acc = acc + fold(simd.tbl_u8x16(a, b))
  acc = acc + fold(simd.tbl_u8x16(b, simd.and_u8x16(b, simd.splat_u8x16(u8(15)))))
  // prev: the window ending n bytes before the end of a ++ b
  acc = acc + fold(simd.prev_u8x16(a, b, u32(0)))
  acc = acc + fold(simd.prev_u8x16(a, b, u32(1)))
  acc = acc + fold(simd.prev_u8x16(a, b, u32(2)))
  acc = acc + fold(simd.prev_u8x16(a, b, u32(3)))
  acc = acc + fold(simd.prev_u8x16(a, b, u32(16)))
  // and the wider shapes' saturation and shifts
  w: simd.U16x8 = simd.splat_u16x8(u16(300))
  z: simd.U16x8 = simd.splat_u16x8(u16(500))
  wide: [8]u16
  simd.store_u16x8(span(&wide), u32(0), simd.subs_u16x8(w, z))
  acc = acc + u32(wide[0])
  simd.store_u16x8(span(&wide), u32(0), simd.subs_u16x8(z, w))
  acc = acc + u32(wide[3])
  simd.store_u16x8(span(&wide), u32(0), simd.shr_u16x8(z, u32(2)))
  acc = acc + u32(wide[7])
  // movemask: one bit per lane's top bit, over every shape; eq masks
  // collapse to the lane mask
  m: u32 = simd.movemask_u8x16(b)
  acc = acc + m
  acc = acc + simd.movemask_u8x16(simd.eq_u8x16(a, simd.splat_u8x16(u8(3))))
  acc = acc + simd.movemask_u16x8(z)
  acc = acc + simd.movemask_u16x8(simd.eq_u16x8(z, z))
  acc = acc + simd.movemask_u16x8(simd.splat_u16x8(u16(32768)))
  acc = acc + simd.movemask_u32x4(simd.eq_u32x4(simd.splat_u32x4(u32(9)), simd.splat_u32x4(u32(9))))
  acc = acc + simd.movemask_u32x4(simd.splat_u32x4(u32(2147483647)))
  acc = acc + simd.movemask_u64x2(simd.eq_u64x2(simd.splat_u64x2(u64(1)), simd.splat_u64x2(u64(1))))
  acc = acc + simd.movemask_u64x2(simd.splat_u64x2(u64(9223372036854775808)))
  // ctz and popcount: total, the zero word gives the width
  acc = acc + simd.ctz_u32(m) + simd.popcount_u32(m)
  acc = acc + simd.ctz_u32(u32(0)) + simd.popcount_u32(u32(0))
  acc = acc + simd.ctz_u32(u32(4294967295)) + simd.popcount_u32(u32(4294967295))
  acc = acc + simd.ctz_u32(u32(1024))
  acc = acc + u32_trunc_u64(simd.ctz_u64(u64(0)) + simd.popcount_u64(u64(0)))
  acc = acc + u32_trunc_u64(simd.ctz_u64(u64(18446744073709551615)) + simd.popcount_u64(u64(18446744073709551615)))
  acc = acc + u32_trunc_u64(simd.ctz_u64(u64(4294967296)) + simd.popcount_u64(u64(4294967296)))
  // the mask-iteration loop visits popcount(m) lanes
  walk: u32 = u32(0)
  visits: u32 = u32(0)
  mm: u32 = m
  while mm != u32(0) {
    walk = walk + simd.ctz_u32(mm)
    visits = visits + u32(1)
    mm = mm & (mm - u32(1))
  }
  acc = acc + walk + (visits == simd.popcount_u32(m) ? u32(100) | u32(0))
  acc % u32(251)
}
`

func TestE2ESimdByteOpsAgreeAcrossLowerings(t *testing.T) {
	want := interpretChecked(t, simdBytesProgram)
	for _, variant := range []struct {
		name  string
		flags []string
	}{{"neon", nil}, {"portable", []string{"-DOAK_PORTABLE_INTRINSICS"}}} {
		_, exit, abnormal := buildAndRunOutput(t, "simd_bytes_"+variant.name, simdBytesProgram, variant.flags...)
		if abnormal || int64(exit) != want {
			t.Fatalf("%s: interpreter %d, compiled exit %d abnormal %v", variant.name, want, exit, abnormal)
		}
	}
}

func TestE2ESimdByteOpsTrapOutOfRange(t *testing.T) {
	for name, body := range map[string]string{
		"shr width": "simd.shr_u8x16(simd.splat_u8x16(u8(1)), u32(8))",
		"prev 17":   "simd.prev_u8x16(simd.splat_u8x16(u8(1)), simd.splat_u8x16(u8(2)), u32(17))",
	} {
		src := `
main: (): u32 {
  n: u32 = u32(8) + u32(9)
  v: simd.U8x16 = ` + body + `
  simd.any_u8x16(v) ? u32(1) | u32(0)
}
`
		// A constant count is rejected where the compiler can see it; the
		// runtime path traps. Either way the program never returns normally.
		_, exit, abnormal := buildAndRunOutput(t, "simd_trap_"+name, src)
		if !abnormal && exit == 0 {
			t.Fatalf("%s: expected a trap or a compile-time rejection", name)
		}
	}
}
