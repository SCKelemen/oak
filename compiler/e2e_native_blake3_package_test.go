package compiler

import (
	"fmt"
	"strings"
	"testing"
)

// The whole hash package through the native backend, hashing inputs of
// many chunks: sixteen and a hundred and twenty-eight (a tree seven
// parents deep), generated in the program by the kernels' LCG and
// compared against the reference digest of the same stream. The
// compression-only test above pins the compression body; this pins the
// chunk and parent bookkeeping around it (absorb, push, final), which
// disagreed with the C backend on the kernels' 1 MiB input for a day
// (2026-09-15/16, benchmarks/native/README.md) while every smaller
// input agreed.
func TestE2ENativeBlake3PackageAgreesWithReference(t *testing.T) {
	requireArm64Host(t)
	t.Setenv("OAK_VERIFY_CACHE", "0")
	sizes := []int{16384, 131072}
	var src strings.Builder
	src.WriteString(`package main
import("hash")

lcg_fill: (buf: [*]u8, count: u32, seed: u64): u64 {
  x: u64 = seed
  i: u32 = 0
  while i < count && i < len(buf) {
    x = x * u64(6364136223846793005) + u64(1442695040888963407)
    buf[i] = u8_trunc_u64(x >> u64(56))
    i = i + u32(1)
  }
  x
}

same32: (digest: []u8, expected: []u8): Bool {
  ok: Bool = len(digest) == u32(32) && len(expected) == u32(32)
  i: u32 = 0
  while ok && i < u32(32) {
    ok = digest[i] == expected[i]
    i = i + u32(1)
  }
  ok
}
`)
	for i, size := range sizes {
		seed := uint64(0x9E3779B97F4A7C15) + uint64(i)
		data := make([]byte, size)
		x := seed
		for j := range data {
			x = x*6364136223846793005 + 1442695040888963407
			data[j] = byte(x >> 56)
		}
		want := blake3Reference(data)
		var literal []string
		for _, b := range want {
			literal = append(literal, fmt.Sprint(b))
		}
		fmt.Fprintf(&src, `
case_%d: (): Bool {
  buf: [%d]u8
  _ = lcg_fill(span(&buf), u32(%d), u64(%d))
  digest: [32]u8
  ok: Bool = hash.blake3(view(&buf), span(&digest))
  expected: [32]u8 = [32]u8{ %s }
  ok && same32(view(&digest), view(&expected))
}
`, i, size, size, seed, strings.Join(literal, ", "))
	}
	src.WriteString("\nmain: (): i32 = case_0() && case_1() ? 42 | 1\n")
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/native_blake3_package\noak 0.1.0\n",
		"main.oak": src.String(),
	})
	for _, lane := range []struct {
		name string
		comp Compilation
	}{
		{"native", New().WithPackageDir(root).WithNativeBodies().WithNativeAsm()},
		{"c", New().WithPackageDir(root)},
	} {
		if _, code, abnormal := buildAndRunFrom(t, "blake3_package_"+lane.name, lane.comp); abnormal || code != 42 {
			t.Fatalf("%s backend: blake3 over %v bytes disagrees with the reference: code=%d abnormal=%v", lane.name, sizes, code, abnormal)
		}
	}
}
