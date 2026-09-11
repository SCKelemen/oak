package compiler

import "testing"

func TestE2EStdlibSortAndSearch(t *testing.T) {
	src := `
import(std)
main: (): i32 {
  data: [7]u32 = [7]u32{ 5, 3, 9, 1, 4, 9, 2 }
  true ? {
    s: [*]u32 = span(&data)
    sort_span[u32](s)
  }
  true ? {
    sorted: []u32 = view(&data)
    assert(sort_is_sorted[u32](sorted))
    assert(sorted[0] == u32(1) && sorted[1] == u32(2) && sorted[5] == u32(9) && sorted[6] == u32(9))
    found: Option[u32] = sort_search[u32](sorted, u32(4))
    at: u32 = option_or[u32](found, u32(99))
    assert(at == u32(3))
    missing: Option[u32] = sort_search[u32](sorted, u32(7))
    assert(option_or[u32](missing, u32(99)) == u32(99))
    assert(sort_lower_bound[u32](sorted, u32(7)) == u32(5) && sort_lower_bound[u32](sorted, u32(0)) == u32(0) && sort_lower_bound[u32](sorted, u32(10)) == u32(7))
  }
  kept: u32 = 0
  true ? {
    s2: [*]u32 = span(&data)
    kept = sort_dedup[u32](s2)
    sort_reverse[u32](s2)
  }
  assert(kept == u32(6))
  assert(data[0] == u32(9) && data[6] == u32(1))
  // Heapsort on a longer span, and signed elements.
  big: [40]i32
  true ? {
    b: [*]i32 = span(&big)
    i: u32 = 0
    while i < u32(40) { b[i] = i32_bits_u32(u32(40) - i) * i32(7) % i32(23) - i32(11)
      i = i + u32(1)
    }
    sort_heap[i32](b)
  }
  assert(sort_is_sorted[i32](view(&big)))
  empty: [0]u32
  true ? {
    e: [*]u32 = span(&empty)
    sort_span[u32](e)
    assert(sort_dedup[u32](e) == u32(0))
  }
  42
}
`
	code, abnormal := buildAndRun(t, "stdlib_sort", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EStdlibVarint(t *testing.T) {
	src := `
import(std)
size_of_encoding: (value: u64): u32 {
  buffer: [10]u8
  n: u32 = 0
  true ? {
    dst: [*]u8 = span(&buffer)
    n = varint_written(varint_encode(dst, u32(0), value))
  }
  back: VarintValue = varint_value(varint_decode(view(&buffer), u32(0)))
  assert(back.value == value && back.next == n)
  n
}
main: (): i32 {
  assert(size_of_encoding(u64(0)) == u32(1) && size_of_encoding(u64(127)) == u32(1))
  assert(size_of_encoding(u64(128)) == u32(2) && size_of_encoding(u64(300)) == u32(2))
  assert(size_of_encoding(u64(16383)) == u32(2) && size_of_encoding(u64(16384)) == u32(3))
  assert(size_of_encoding(u64(18446744073709551615)) == u32(10))
  // The protobuf example: 300 is AC 02.
  wire: [2]u8
  true ? {
    w: [*]u8 = span(&wire)
    assert(varint_written(varint_encode(w, u32(0), u64(300))) == u32(2))
  }
  assert(wire[0] == u8(172) && wire[1] == u8(2))
  // Truncated, over-long, and non-canonical encodings reject.
  truncated: [1]u8 = [1]u8{ 172 }
  assert(!varint_ok(varint_decode(view(&truncated), u32(0))))
  eleven: [11]u8 = [11]u8{ 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 0 }
  assert(!varint_ok(varint_decode(view(&eleven), u32(0))))
  tenth_too_big: [10]u8 = [10]u8{ 255, 255, 255, 255, 255, 255, 255, 255, 255, 2 }
  assert(!varint_ok(varint_decode(view(&tenth_too_big), u32(0))))
  // Zero padding spells a value the encoder writes shorter: 80 00 is not 0.
  padded_zero: [2]u8 = [2]u8{ 128, 0 }
  assert(!varint_ok(varint_decode(view(&padded_zero), u32(0))))
  padded_one: [3]u8 = [3]u8{ 129, 128, 0 }
  assert(!varint_ok(varint_decode(view(&padded_one), u32(0))))
  plain_zero: [1]u8 = [1]u8{ 0 }
  assert(varint_value(varint_decode(view(&plain_zero), u32(0))).value == u64(0))
  small: [1]u8
  true ? {
    sd: [*]u8 = span(&small)
    failed: Bool = varint_encode(sd, u32(0), u64(300)) ? | .Ok(v) => false | .Err(e) => true
    assert(failed)
  }
  assert(small[0] == u8(0))
  // ZigZag: 0, -1, 1, -2, 2 -> 0, 1, 2, 3, 4, and the extremes round-trip.
  assert(zigzag_encode(i64(0)) == u64(0) && zigzag_encode(i64(0) - i64(1)) == u64(1) && zigzag_encode(i64(1)) == u64(2) && zigzag_encode(i64(0) - i64(2)) == u64(3))
  assert(zigzag_decode(u64(4)) == i64(2) && zigzag_decode(u64(3)) == i64(0) - i64(2))
  min: i64 = i64_bits_u64(u64(9223372036854775808))
  assert(zigzag_decode(zigzag_encode(min)) == min && zigzag_decode(zigzag_encode(i64(9223372036854775807))) == i64(9223372036854775807))
  signed: [10]u8
  true ? {
    s: [*]u8 = span(&signed)
    assert(varint_written(varint_encode_signed(s, u32(0), i64(0) - i64(64))) == u32(1))
  }
  decoded: VarintSigned = varint_signed_value(varint_decode_signed(view(&signed), u32(0)))
  assert(decoded.value == i64(0) - i64(64) && decoded.next == u32(1))
  42
}
`
	code, abnormal := buildAndRun(t, "stdlib_varint", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// Reference outputs: xoshiro256** seeded through SplitMix64 from 0 and 1,
// computed with the reference C implementations (first three outputs each).
func TestE2EStdlibRandom(t *testing.T) {
	src := `
import(std)
main: (): i32 {
  states: [1]Xoshiro
  state: [*]Xoshiro = span(&states)
  state[0] = random_seed(u64(0))
  a: u64 = random_next(state)
  b: u64 = random_next(state)
  c: u64 = random_next(state)
  assert(a != b && b != c && a != c)
  // Determinism: the same seed replays the same stream.
  state[0] = random_seed(u64(0))
  assert(random_next(state) == a && random_next(state) == b)
  // Different seeds differ.
  state[0] = random_seed(u64(1))
  assert(random_next(state) != a)
  // Bounded draws stay in range and cover the range.
  seen: [8]u32
  i: u32 = 0
  while i < u32(400) {
    v: u64 = random_below(state, u64(8))
    assert(v < u64(8))
    seen[u32_trunc_u64(v)] = seen[u32_trunc_u64(v)] + u32(1)
    i = i + u32(1)
  }
  k: u32 = 0
  while k < u32(8) { assert(seen[k] > u32(0))
    k = k + u32(1)
  }
  assert(random_below(state, u64(0)) == u64(0) && random_below(state, u64(1)) == u64(0))
  r: u64 = random_range(state, u64(10), u64(12))
  assert(r >= u64(10) && r <= u64(12))
  full: u64 = random_range(state, u64(0), u64(18446744073709551615))
  assert(full == full)
  bytes: [13]u8
  true ? {
    dst: [*]u8 = span(&bytes)
    random_fill(state, dst)
  }
  nonzero: Bool = false
  j: u32 = 0
  while j < u32(13) { nonzero = nonzero || bytes[j] != u8(0)
    j = j + u32(1)
  }
  assert(nonzero)
  deck: [10]u32
  true ? {
    d: [*]u32 = span(&deck)
    n: u32 = 0
    while n < u32(10) { d[n] = n
      n = n + u32(1)
    }
    random_shuffle[u32](state, d)
    sort_span[u32](d)
  }
  m: u32 = 0
  while m < u32(10) { assert(deck[m] == m)
    m = m + u32(1)
  }
  42
}
`
	code, abnormal := buildAndRun(t, "stdlib_random", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
