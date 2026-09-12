package compiler

import "testing"

// The utf8 package (stdlib/utf8.oak): Keiser and Lemire's lookup-table
// validator over Oak's portable vectors. Every case is checked against the
// scalar builtin `is_valid_utf8` (the Table 3-7 transliteration the Lean
// model Oak.Utf8Validity brackets) in the same program, under the NEON
// lowering and the portable lane loop; the edge cases also carry their
// expected verdicts, so the two validators cannot agree by being wrong
// together.
const utf8Program = `package main
utf8 := import("utf8")
r := import("random")

agree: (v: []u8): Bool = utf8.valid(v) == is_valid_utf8(v)

main: (): i32 {
  ok: Bool = true
  // ASCII, two, three, four bytes; a sequence across a 16-byte boundary.
  ascii: [5]u8 = [u8(104), u8(101), u8(108), u8(108), u8(111)]
  ok = ok && utf8.valid(view(&ascii)) && agree(view(&ascii))
  mixed: [8]u8 = [u8(104), u8(105), u8(195), u8(169), u8(226), u8(130), u8(172), u8(33)]
  ok = ok && utf8.valid(view(&mixed)) && agree(view(&mixed))
  four: [4]u8 = [u8(240), u8(159), u8(146), u8(150)]
  ok = ok && utf8.valid(view(&four)) && agree(view(&four))
  across: [18]u8 = [u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(226), u8(130), u8(172), u8(97)]
  ok = ok && utf8.valid(view(&across)) && agree(view(&across))
  four_across: [19]u8 = [u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(240), u8(159), u8(146), u8(150)]
  ok = ok && utf8.valid(view(&four_across)) && agree(view(&four_across))
  exactly16: [16]u8 = [u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(195), u8(169)]
  ok = ok && utf8.valid(view(&exactly16)) && agree(view(&exactly16))
  empty: [1]u8 = [u8(0)]
  empty_view: []u8 = view(&empty)
  ok = ok && utf8.valid(subslice(empty_view, u32(0), u32(0)))
  // Every class of error.
  stray: [1]u8 = [u8(128)]
  ok = ok && !utf8.valid(view(&stray)) && agree(view(&stray))
  truncated: [2]u8 = [u8(226), u8(130)]
  ok = ok && !utf8.valid(view(&truncated)) && agree(view(&truncated))
  truncated_mid: [3]u8 = [u8(226), u8(65), u8(66)]
  ok = ok && !utf8.valid(view(&truncated_mid)) && agree(view(&truncated_mid))
  overlong2: [2]u8 = [u8(192), u8(128)]
  ok = ok && !utf8.valid(view(&overlong2)) && agree(view(&overlong2))
  overlong2b: [2]u8 = [u8(193), u8(191)]
  ok = ok && !utf8.valid(view(&overlong2b)) && agree(view(&overlong2b))
  overlong3: [3]u8 = [u8(224), u8(128), u8(128)]
  ok = ok && !utf8.valid(view(&overlong3)) && agree(view(&overlong3))
  overlong3b: [3]u8 = [u8(224), u8(159), u8(191)]
  ok = ok && !utf8.valid(view(&overlong3b)) && agree(view(&overlong3b))
  overlong4: [4]u8 = [u8(240), u8(128), u8(128), u8(128)]
  ok = ok && !utf8.valid(view(&overlong4)) && agree(view(&overlong4))
  overlong4b: [4]u8 = [u8(240), u8(143), u8(191), u8(191)]
  ok = ok && !utf8.valid(view(&overlong4b)) && agree(view(&overlong4b))
  surrogate: [3]u8 = [u8(237), u8(160), u8(128)]
  ok = ok && !utf8.valid(view(&surrogate)) && agree(view(&surrogate))
  surrogate_hi: [3]u8 = [u8(237), u8(191), u8(191)]
  ok = ok && !utf8.valid(view(&surrogate_hi)) && agree(view(&surrogate_hi))
  edge_ok: [3]u8 = [u8(237), u8(159), u8(191)]
  ok = ok && utf8.valid(view(&edge_ok)) && agree(view(&edge_ok))
  too_large: [4]u8 = [u8(244), u8(144), u8(128), u8(128)]
  ok = ok && !utf8.valid(view(&too_large)) && agree(view(&too_large))
  max_ok: [4]u8 = [u8(244), u8(143), u8(191), u8(191)]
  ok = ok && utf8.valid(view(&max_ok)) && agree(view(&max_ok))
  f5: [4]u8 = [u8(245), u8(128), u8(128), u8(128)]
  ok = ok && !utf8.valid(view(&f5)) && agree(view(&f5))
  ff: [1]u8 = [u8(255)]
  ok = ok && !utf8.valid(view(&ff)) && agree(view(&ff))
  extra_cont: [3]u8 = [u8(195), u8(169), u8(128)]
  ok = ok && !utf8.valid(view(&extra_cont)) && agree(view(&extra_cont))
  cont_after_3: [4]u8 = [u8(226), u8(130), u8(172), u8(128)]
  ok = ok && !utf8.valid(view(&cont_after_3)) && agree(view(&cont_after_3))
  lead_lead: [3]u8 = [u8(226), u8(226), u8(130)]
  ok = ok && !utf8.valid(view(&lead_lead)) && agree(view(&lead_lead))
  truncated_at_16: [16]u8 = [u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(226)]
  ok = ok && !utf8.valid(view(&truncated_at_16)) && agree(view(&truncated_at_16))
  cont_at_17: [17]u8 = [u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(97), u8(128)]
  ok = ok && !utf8.valid(view(&cont_at_17)) && agree(view(&cont_at_17))

  // Fuzz: random code points encoded, then randomly corrupted, in lengths
  // that cross several block boundaries; the two validators must agree.
  states: [1]r.Xoshiro
  state: [*]r.Xoshiro = span(&states)
  state[0] = r.random_seed(u64(20260912))
  buf: [80]u8
  round: u32 = u32(0)
  while round < u32(3000) {
    length: u32 = u32_trunc_u64(r.random_below(state, u64(81)))
    i: u32 = u32(0)
    while i < length {
      kind: u64 = r.random_below(state, u64(10))
      cp: u64 = u64(0)
      kind < u64(5) ? { cp = u64(32) + r.random_below(state, u64(95)) }
        | kind < u64(7) ? { cp = u64(128) + r.random_below(state, u64(1920)) }
        | kind < u64(9) ? { cp = u64(2048) + r.random_below(state, u64(63488)) }
        | { cp = u64(65536) + r.random_below(state, u64(1048576)) }
      cp >= u64(55296) && cp <= u64(57343) ? { cp = u64(19968) }
      cp < u64(128) ? {
        buf[i] = u8_trunc_u64(cp)
        i = i + u32(1)
      } | cp < u64(2048) ? {
        i + u32(1) < length ? {
          buf[i] = u8_trunc_u64(u64(192) | (cp >> u64(6)))
          buf[i + u32(1)] = u8_trunc_u64(u64(128) | (cp & u64(63)))
        }
        i = i + u32(2)
      } | cp < u64(65536) ? {
        i + u32(2) < length ? {
          buf[i] = u8_trunc_u64(u64(224) | (cp >> u64(12)))
          buf[i + u32(1)] = u8_trunc_u64(u64(128) | ((cp >> u64(6)) & u64(63)))
          buf[i + u32(2)] = u8_trunc_u64(u64(128) | (cp & u64(63)))
        }
        i = i + u32(3)
      } | {
        i + u32(3) < length ? {
          buf[i] = u8_trunc_u64(u64(240) | (cp >> u64(18)))
          buf[i + u32(1)] = u8_trunc_u64(u64(128) | ((cp >> u64(12)) & u64(63)))
          buf[i + u32(2)] = u8_trunc_u64(u64(128) | ((cp >> u64(6)) & u64(63)))
          buf[i + u32(3)] = u8_trunc_u64(u64(128) | (cp & u64(63)))
        }
        i = i + u32(4)
      }
    }
    // Corrupt: with probability 1/2 overwrite one byte with a random value.
    length > u32(0) && r.random_bool(state) ? {
      at: u32 = u32_trunc_u64(r.random_below(state, u64(length)))
      buf[at] = u8_trunc_u64(r.random_below(state, u64(256)))
    }
    whole: []u8 = view(&buf)
    ok = ok && agree(subslice(whole, u32(0), length))
    round = round + u32(1)
  }
  ok ? 42 | 1
}
`

func TestE2EStdlibUtf8AgreesWithTheScalarValidator(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": utf8Program})
	for _, variant := range []struct {
		name  string
		flags []string
	}{{"neon", nil}, {"portable", []string{"-DOAK_PORTABLE_INTRINSICS"}}} {
		_, exit, abnormal := buildAndRunFrom(t, "stdlib_utf8_"+variant.name, New().WithPackageDir(root), variant.flags...)
		if abnormal || exit != 42 {
			t.Fatalf("%s: exit %d abnormal %v", variant.name, exit, abnormal)
		}
	}
}
