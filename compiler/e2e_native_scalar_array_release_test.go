package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A scalar-replaced array (nativegen/scalar_arrays.go) owns no frame
// slot: its elements are scalars under their own names. Its binding's
// zero offset was recycled at its last use as if it were a slot, so the
// next spilled scalar landed on the first frame slot — a live array's —
// and the blake3 compression came out wrong after its third quarter
// round (benchmarks/kernels, 2026-09-16). Four inlined quarter rounds
// over a sixteen-word state reproduce it: the body must be proven, and
// agree with the C backend when run.
const nativeScalarArrayReleaseProgram = `
rotr32: (x: u32, n: u32): u32 = (x >> n) | (x << (u32(32) - n))

quarter: (a: u32, b: u32, c: u32, d: u32, mx: u32, my: u32): [4]u32 {
  a1: u32 = a + b + mx
  d1: u32 = rotr32(d ^ a1, u32(16))
  c1: u32 = c + d1
  b1: u32 = rotr32(b ^ c1, u32(12))
  a2: u32 = a1 + b1 + my
  d2: u32 = rotr32(d1 ^ a2, u32(8))
  c2: u32 = c1 + d2
  b2: u32 = rotr32(b1 ^ c2, u32(7))
  [4]u32{ a2, b2, c2, d2 }
}

mix: (cv: [8]u32, block: [16]u32, block_len: u32, flags: u32): [16]u32 {
  v: [16]u32 = [16]u32{
    cv[0], cv[1], cv[2], cv[3], cv[4], cv[5], cv[6], cv[7],
    u32(1), u32(2), u32(3), u32(4), u32(5), u32(6), block_len, flags
  }
  g0: [4]u32 = quarter(v[0], v[4], v[8], v[12], block[0], block[1])
  v[0] = g0[0]
  v[4] = g0[1]
  v[8] = g0[2]
  v[12] = g0[3]
  g1: [4]u32 = quarter(v[1], v[5], v[9], v[13], block[2], block[3])
  v[1] = g1[0]
  v[5] = g1[1]
  v[9] = g1[2]
  v[13] = g1[3]
  g2: [4]u32 = quarter(v[2], v[6], v[10], v[14], block[4], block[5])
  v[2] = g2[0]
  v[6] = g2[1]
  v[10] = g2[2]
  v[14] = g2[3]
  g3: [4]u32 = quarter(v[3], v[7], v[11], v[15], block[6], block[7])
  v[3] = g3[0]
  v[7] = g3[1]
  v[11] = g3[2]
  v[15] = g3[3]
  v
}

main: (): i32 {
  cv: [8]u32 = [8]u32{ 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 }
  block: [16]u32 = [16]u32{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16 }
  out: [16]u32 = mix(cv, block, u32(64), u32(1))
  acc: u32 = u32(0)
  j: u32 = u32(0)
  while j < u32(16) {
    acc = (acc * u32(31)) ^ out[j]
    j = j + u32(1)
  }
  i32_bits_u32(acc & u32(255))
}
`

func TestE2ENativeScalarArrayRelease(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("release.oak", nativeScalarArrayReleaseProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	if _, err := comp.SemanticModel().Get(); err != nil {
		t.Fatalf("compilation failed: %v\n%s", err, strings.Join(infos, "\n"))
	}
	joined := strings.Join(infos, "\n")
	if strings.Contains(joined, "disagrees") {
		t.Fatalf("a mismatch:\n%s", joined)
	}
	_, native, abnormal := buildAndRunFrom(t, "scalar_array_release", comp)
	_, viaC, abnormalC := buildAndRunFrom(t, "scalar_array_release_c", New().WithSource("release.oak", nativeScalarArrayReleaseProgram))
	if abnormal || abnormalC || native != viaC {
		t.Fatalf("native %d (abnormal %v), C backend %d (abnormal %v)\n%s", native, abnormal, viaC, abnormalC, joined)
	}
}
