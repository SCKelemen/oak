package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/evaluator"
)

// The scalable vector API (docs/spec/93-simd.md §4): a strip-mined program
// over inputs of every length from zero to forty — final partial chunks of
// every size — folded into one checksum. Its result must not depend on the
// active extent the backend chooses: the interpreter at the portable
// capacity and at a stressed extent of three lanes, the portable C, and
// (compiler/e2e_rvv_test.go) RISC-V Vector at VLEN 128 and 256 all print
// the same number.
const scalableProgram = `
sum_masked: (input: []u8, needle: u8): u32 {
  remaining: u32 = len(input)
  offset: u32 = u32(0)
  total: u32 = u32(0)
  // Per-chunk observations fold with or/and: how many chunks there are
  // depends on the extent, whether the needle occurs anywhere does not.
  found: Bool = false
  all_set: Bool = true
  while remaining != u32(0) {
    // The staging buffer below holds 16 lanes, so the request is bounded
    // to 16: hardware width is not a type property, and the backend may
    // otherwise choose a wider extent (32 lanes at VLEN 256).
    active: simd.Active = simd.active_u8(remaining < u32(16) ? remaining | u32(16))
    chunk: simd.ScalableU8 = simd.load_active_u8(input, offset, active)
    mask: simd.ScalableU8 = simd.eq_active_u8(chunk, simd.splat_active_u8(needle, active), active)
    shifted: simd.ScalableU8 = simd.shr_active_u8(simd.subs_active_u8(chunk, simd.splat_active_u8(u8(3), active), active), u32(1), active)
    kept: simd.ScalableU8 = simd.and_active_u8(shifted, mask, active)
    found = found || simd.any_active_u8(mask, active)
    all_set = all_set && simd.all_active_u8(simd.or_active_u8(chunk, simd.splat_active_u8(u8(1), active), active), active)
    // fold the kept lanes through a store and a scalar walk
    scratch: [16]u8
    i: u32 = u32(0)
    // store only the active lanes into the front of scratch
    simd.store_active_u8(span(&scratch), u32(0), kept, active)
    count: u32 = simd.count(active)
    while i < count {
      total = total + u32(scratch[i]) * (offset + i + u32(1))
      i = i + u32(1)
    }
    offset = offset + count
    remaining = remaining - count
  }
  total * u32(7) + (found ? u32(1) | u32(0)) + (all_set ? u32(2) | u32(0))
}

sum_words: (words: []u32): u32 {
  remaining: u32 = len(words)
  offset: u32 = u32(0)
  total: u32 = u32(0)
  while remaining != u32(0) {
    active: simd.Active = simd.active_u32(remaining)
    chunk: simd.ScalableU32 = simd.load_active_u32(words, offset, active)
    doubled: simd.ScalableU32 = simd.add_active_u32(chunk, chunk, active)
    total = total + simd.reduce_add_active_u32(simd.max_active_u32(doubled, simd.splat_active_u32(u32(5), active), active), active)
    count: u32 = simd.count(active)
    offset = offset + count
    remaining = remaining - count
  }
  total
}

main: (): u32 {
  bytes: [40]u8
  words: [40]u32
  i: u32 = u32(0)
  while i < u32(40) {
    bytes[i] = u8_trunc_u32((i * u32(37) + u32(11)) % u32(256))
    words[i] = i * u32(2654435761)
    i = i + u32(1)
  }
  acc: u32 = u32(0)
  n: u32 = u32(0)
  bv: []u8 = view(&bytes)
  wv: []u32 = view(&words)
  while n <= u32(40) {
    acc = acc * u32(31) + sum_masked(subslice(bv, u32(0), n), u8(11)) + sum_words(subslice(wv, u32(0), n))
    n = n + u32(1)
  }
  acc % u32(251)
}
`

func TestE2EScalableExtentIndependent(t *testing.T) {
	want := interpretChecked(t, scalableProgram)
	previous := evaluator.ScalableExtentCap
	defer func() { evaluator.ScalableExtentCap = previous }()
	for _, cap := range []int{1, 3, 5} {
		evaluator.ScalableExtentCap = cap
		if got := interpretChecked(t, scalableProgram); got != want {
			t.Fatalf("extent capped at %d lanes: %d, at the portable capacity %d", cap, got, want)
		}
	}
	evaluator.ScalableExtentCap = previous
	for _, variant := range []struct {
		name  string
		flags []string
	}{{"portable", []string{"-DOAK_PORTABLE_INTRINSICS"}}, {"host", nil}} {
		_, exit, abnormal := buildAndRunOutput(t, "scalable_"+variant.name, scalableProgram, variant.flags...)
		if abnormal || int64(exit) != want {
			t.Fatalf("%s: interpreter %d, compiled exit %d abnormal %v", variant.name, want, exit, abnormal)
		}
	}
}

// Scalable values are block-local (docs/spec/93-simd.md §4 item 7).
func TestScalableTypesAreBlockLocal(t *testing.T) {
	for name, source := range map[string]string{
		"parameter": "f: (a: simd.Active): u32 { simd.count(a) }\nmain: (): u32 { 0 }\n",
		"result":    "f: (n: u32): simd.Active { simd.active_u8(n) }\nmain: (): u32 { 0 }\n",
		"global":    "g: simd.Active = simd.active_u8(u32(4))\nmain: (): u32 { 0 }\n",
		"record":    "R: type = struct { a: simd.ScalableU8 }\nmain: (): u32 { 0 }\n",
		"array":     "main: (): u32 {\n  xs: [2]simd.ScalableU8\n  0\n}\n",
	} {
		_, err := New().WithSource(name+".oak", source).Check().Get()
		if err == nil || !strings.Contains(err.Error(), "OAK-S0401") {
			t.Errorf("%s: %v", name, err)
		}
	}
}
