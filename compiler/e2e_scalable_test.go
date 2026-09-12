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

// The predicated operations (docs/spec/93-simd.md §4.1): a range filter in
// the shape of a database scan — comparisons to masks, a count of the
// matching lanes, a masked store that leaves the other lanes' marker in
// place, a masked reload that zeroes them, and a select — over bytes and
// words, at every input length from zero to forty.
const maskedProgram = `
filter_bytes: (input: []u8, lo: u8, hi: u8): u32 {
  remaining: u32 = len(input)
  offset: u32 = u32(0)
  matched: u32 = u32(0)
  saw_other: Bool = false
  out: [64]u8
  picked: [64]u8
  i: u32 = u32(0)
  while i < u32(64) {
    out[i] = u8(170)
    i = i + u32(1)
  }
  while remaining != u32(0) {
    active: simd.Active = simd.active_u8(remaining)
    chunk: simd.ScalableU8 = simd.load_active_u8(input, offset, active)
    not_below: simd.ScalableU8 = simd.xor_active_u8(simd.lt_active_u8(chunk, simd.splat_active_u8(lo, active), active), simd.splat_active_u8(u8(255), active), active)
    in_range: simd.ScalableU8 = simd.and_active_u8(not_below, simd.lt_active_u8(chunk, simd.splat_active_u8(hi, active), active), active)
    matched = matched + simd.count_nonzero_active_u8(in_range, active)
    // matching lanes land in out, the marker stays elsewhere
    simd.store_masked_active_u8(span(&out), offset, in_range, chunk, active)
    // a masked reload sees the matches and zeros
    reloaded: simd.ScalableU8 = simd.load_masked_active_u8(view(&out), offset, in_range, active)
    doubled: simd.ScalableU8 = simd.add_active_u8(reloaded, reloaded, active)
    chosen: simd.ScalableU8 = simd.select_active_u8(in_range, doubled, simd.splat_active_u8(u8(1), active), active)
    simd.store_active_u8(span(&picked), offset, chosen, active)
    saw_other = saw_other || simd.any_active_u8(simd.ne_active_u8(chosen, simd.splat_active_u8(u8(1), active), active), active)
    count: u32 = simd.count(active)
    offset = offset + count
    remaining = remaining - count
  }
  total: u32 = u32(0)
  i = u32(0)
  while i < len(input) {
    total = total * u32(3) + u32(out[i]) * u32(5) + u32(picked[i])
    i = i + u32(1)
  }
  total + matched * u32(1000) + (saw_other ? u32(7) | u32(0))
}

clamp_words: (words: []u32, limit: u32): u32 {
  remaining: u32 = len(words)
  offset: u32 = u32(0)
  total: u32 = u32(0)
  clamped: u32 = u32(0)
  scratch: [64]u32
  i: u32 = u32(0)
  while i < len(words) {
    scratch[i] = words[i]
    i = i + u32(1)
  }
  while remaining != u32(0) {
    active: simd.Active = simd.active_u32(remaining)
    chunk: simd.ScalableU32 = simd.load_active_u32(view(&scratch), offset, active)
    cap: simd.ScalableU32 = simd.splat_active_u32(limit, active)
    over: simd.ScalableU32 = simd.gt_active_u32(chunk, cap, active)
    clamped = clamped + simd.count_nonzero_active_u32(over, active)
    // clamp in place: only the lanes over the limit are written
    simd.store_masked_active_u32(span(&scratch), offset, over, cap, active)
    after: simd.ScalableU32 = simd.load_active_u32(view(&scratch), offset, active)
    total = total + simd.reduce_add_active_u32(simd.select_active_u32(over, simd.splat_active_u32(u32(1), active), after, active), active)
    count: u32 = simd.count(active)
    offset = offset + count
    remaining = remaining - count
  }
  total + clamped * u32(65537)
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
    acc = acc * u32(31) + filter_bytes(subslice(bv, u32(0), n), u8(40), u8(200)) + clamp_words(subslice(wv, u32(0), n), u32(2000000000))
    n = n + u32(1)
  }
  acc % u32(251)
}
`

func TestE2EScalableExtentIndependent(t *testing.T) {
	for _, program := range []struct{ name, source string }{{"scalable", scalableProgram}, {"masked", maskedProgram}} {
		t.Run(program.name, func(t *testing.T) {
			want := interpretChecked(t, program.source)
			previous := evaluator.ScalableExtentCap
			defer func() { evaluator.ScalableExtentCap = previous }()
			for _, cap := range []int{1, 3, 5} {
				evaluator.ScalableExtentCap = cap
				if got := interpretChecked(t, program.source); got != want {
					t.Fatalf("extent capped at %d lanes: %d, at the portable capacity %d", cap, got, want)
				}
			}
			evaluator.ScalableExtentCap = previous
			for _, variant := range []struct {
				name  string
				flags []string
			}{{"portable", []string{"-DOAK_PORTABLE_INTRINSICS"}}, {"host", nil}} {
				_, exit, abnormal := buildAndRunOutput(t, program.name+"_"+variant.name, program.source, variant.flags...)
				if abnormal || int64(exit) != want {
					t.Fatalf("%s: interpreter %d, compiled exit %d abnormal %v", variant.name, want, exit, abnormal)
				}
			}
		})
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
