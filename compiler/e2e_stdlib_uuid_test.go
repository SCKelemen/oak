package compiler

import "testing"

// RFC 9562 appendix A.6 test vector: a version 7 UUID whose timestamp is
// 0x017F22E279B0 milliseconds (2022-02-22T19:22:22Z).
func TestE2EStdlibUuid(t *testing.T) {
	src := `
import(std)
main: (): i32 {
  text: [36]u8 = [36]u8{ 48, 49, 55, 70, 50, 50, 69, 50, 45, 55, 57, 66, 48, 45, 55, 67, 67, 51, 45, 57, 56, 67, 52, 45, 68, 67, 48, 67, 48, 67, 48, 55, 51, 57, 56, 70 }
  parsed: [16]u8
  true ? {
    p: [*]u8 = span(&parsed)
    assert(uuid_written(uuid_parse(p, view(&text))) == u32(16))
  }
  true ? {
    value: []u8 = view(&parsed)
    assert(value[0] == u8(1) && value[1] == u8(127) && value[6] == u8(124) && value[8] == u8(152) && value[15] == u8(143))
    assert(option_or[u32](uuid_version(value), u32(99)) == u32(7))
    assert(option_or[u32](uuid_variant(value), u32(99)) == u32(1))
    assert(option_or[u64](uuid_v7_millis(value), u64(0)) == u64(1645557742000))
  }
  // Format lowercase and uppercase; the uppercase form is the RFC's spelling.
  lower: [36]u8
  upper: [36]u8
  true ? {
    l: [*]u8 = span(&lower)
    u: [*]u8 = span(&upper)
    assert(uuid_written(uuid_format(l, view(&parsed), false)) == u32(36))
    assert(uuid_written(uuid_format(u, view(&parsed), true)) == u32(36))
  }
  assert(bytes_equal(view(&upper), view(&text)))
  assert(lower[0] == u8(48) && lower[3] == u8(102) && lower[8] == u8(45) && lower[13] == u8(45) && lower[18] == u8(45) && lower[23] == u8(45) && lower[35] == u8(102))
  again: [16]u8
  true ? {
    a: [*]u8 = span(&again)
    assert(uuid_written(uuid_parse(a, view(&lower))) == u32(16))
  }
  assert(uuid_equal(view(&again), view(&parsed)) && uuid_compare(view(&again), view(&parsed)) == i32(0))
  // Rejections leave the destination unchanged.
  scratch: [16]u8
  true ? {
    s: [*]u8 = span(&scratch)
    short: []u8 = view(&text)
    assert(uuid_failure(uuid_parse(s, short[u32(0):u32(35)])) == u32(1))
    bad: [36]u8 = text
    bad[13] = u8(48)
    assert(uuid_failure(uuid_parse(s, view(&bad))) == u32(2))
    bad[13] = u8(45)
    bad[0] = u8(103)
    assert(uuid_failure(uuid_parse(s, view(&bad))) == u32(2))
    assert(uuid_failure(uuid_format(s, view(&parsed), false)) == u32(3))
    tiny: [*]u8 = s[u32(0):u32(15)]
    assert(uuid_failure(uuid_parse(tiny, view(&text))) == u32(3))
  }
  assert(scratch[0] == u8(0) && scratch[15] == u8(0))
  // Nil, max, and generated values.
  states: [1]Xoshiro
  states[0] = random_seed(u64(7))
  state: [*]Xoshiro = span(&states)
  first: [16]u8
  second: [16]u8
  true ? {
    f: [*]u8 = span(&first)
    s2: [*]u8 = span(&second)
    assert(uuid_written(uuid_nil(f)) == u32(16))
    assert(uuid_written(uuid_max(s2)) == u32(16))
  }
  assert(first[0] == u8(0) && first[15] == u8(0) && second[0] == u8(255) && second[15] == u8(255))
  assert(option_or[u32](uuid_variant(view(&first)), u32(99)) == u32(0) && option_or[u32](uuid_variant(view(&second)), u32(99)) == u32(3))
  true ? {
    f: [*]u8 = span(&first)
    s2: [*]u8 = span(&second)
    assert(uuid_written(uuid_v4(state, f)) == u32(16))
    assert(uuid_written(uuid_v4(state, s2)) == u32(16))
  }
  assert(option_or[u32](uuid_version(view(&first)), u32(99)) == u32(4) && option_or[u32](uuid_variant(view(&first)), u32(99)) == u32(1))
  assert(!uuid_equal(view(&first), view(&second)))
  assert(option_or[u64](uuid_v7_millis(view(&first)), u64(5)) == u64(5))
  true ? {
    f: [*]u8 = span(&first)
    s2: [*]u8 = span(&second)
    assert(uuid_written(uuid_v7(u64(1645557742000), state, f)) == u32(16))
    assert(uuid_written(uuid_v7(u64(1645557742001), state, s2)) == u32(16))
    assert(uuid_failure(uuid_v7(u64(281474976710656), state, f)) == u32(4))
  }
  assert(first[0] == u8(1) && first[1] == u8(127) && first[2] == u8(34) && first[3] == u8(226) && first[4] == u8(121) && first[5] == u8(176))
  assert(option_or[u32](uuid_version(view(&first)), u32(99)) == u32(7) && option_or[u32](uuid_variant(view(&first)), u32(99)) == u32(1))
  assert(option_or[u64](uuid_v7_millis(view(&first)), u64(0)) == u64(1645557742000))
  assert(uuid_compare(view(&first), view(&second)) == i32(0) - i32(1) && uuid_compare(view(&second), view(&first)) == i32(1))
  42
}
`
	code, abnormal := buildAndRun(t, "stdlib_uuid", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EStdlibUuidQualified(t *testing.T) {
	src := `package main
import("uuid")
import("random")
main: (): i32 {
  states: [1]random.Xoshiro
  states[0] = random.random_seed(u64(1))
  state: [*]random.Xoshiro = span(&states)
  value: [16]u8
  text: [36]u8
  true ? {
    v: [*]u8 = span(&value)
    assert(uuid.uuid_written(uuid.uuid_v7(u64(1000), state, v)) == u32(16))
  }
  true ? {
    t: [*]u8 = span(&text)
    assert(uuid.uuid_written(uuid.uuid_format(t, view(&value), false)) == u32(36))
  }
  back: [16]u8
  true ? {
    b: [*]u8 = span(&back)
    assert(uuid.uuid_written(uuid.uuid_parse(b, view(&text))) == u32(16))
  }
  uuid.uuid_equal(view(&back), view(&value)) ? { 42 } | { 0 }
}
`
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/uuid_qualified\noak 0.1.0\n",
		"main.oak": src,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
