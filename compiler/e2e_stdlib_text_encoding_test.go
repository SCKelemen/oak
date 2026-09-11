package compiler

import "testing"

// Byte order marks, UTF-16 as bytes in either order, Latin-1, and signed or
// radix numbers (stdlib/strings.oak, STRINGS.md). Spans end with their block
// before the owner is viewed again.
func TestE2EStdlibTextByteOrderAndLatin1(t *testing.T) {
	src := `
import(std)
same_bytes: (a: []u8, b: []u8): Bool {
  same: Bool = len(a) == len(b)
  i: u32 = 0
  while same && i < len(a) { same = a[i] == b[i]
    i = i + u32(1)
  }
  same
}
main: (): i32 {
  bom8: [5]u8 = [5]u8{ 239, 187, 191, 104, 105 }
  bom16le: [4]u8 = [4]u8{ 255, 254, 104, 0 }
  bom32be: [4]u8 = [4]u8{ 0, 0, 254, 255 }
  plain: []u8 = text_literal("hi")
  assert(text_bom(view(&bom8)) == u32(1) && text_bom_width(u32(1)) == u32(3))
  assert(text_bom(view(&bom16le)) == u32(2) && text_bom(view(&bom32be)) == u32(5) && text_bom(plain) == u32(0))
  stripped: TextRange = text_strip_bom(view(&bom8))
  assert(stripped.start == u32(3) && stripped.end == u32(5))

  // UTF-16 LE and BE bytes of "A😀": 41 00 3D D8 00 DE / 00 41 D8 3D DE 00.
  le: [6]u8 = [6]u8{ 65, 0, 61, 216, 0, 222 }
  be: [6]u8 = [6]u8{ 0, 65, 216, 61, 222, 0 }
  out: [5]u8
  true ? {
    dst: [*]u8 = span(&out)
    assert(text_result_value(utf16_bytes_to_utf8_size(view(&le), false)) == u32(5))
    assert(text_result_value(utf16_bytes_to_utf8(dst, view(&le), false)) == u32(5))
  }
  assert(text_equal(view(&out), text_literal("A😀")))
  true ? {
    dst: [*]u8 = span(&out)
    assert(text_result_value(utf16_bytes_to_utf8(dst, view(&be), true)) == u32(5))
  }
  assert(text_equal(view(&out), text_literal("A😀")))
  odd: [3]u8 = [3]u8{ 65, 0, 61 }
  assert(!text_result_ok(utf16_bytes_to_utf8_size(view(&odd), false)))
  lone: [2]u8 = [2]u8{ 61, 216 }
  assert(!text_result_ok(utf16_bytes_to_utf8_size(view(&lone), false)))
  back: [6]u8
  assert(text_result_value(utf8_to_utf16_bytes_size(text_literal("A😀"))) == u32(6))
  true ? {
    bdst: [*]u8 = span(&back)
    assert(text_result_value(utf8_to_utf16_bytes(bdst, text_literal("A😀"), true)) == u32(6))
  }
  assert(same_bytes(view(&back), view(&be)))
  true ? {
    bdst: [*]u8 = span(&back)
    assert(text_result_value(utf8_to_utf16_bytes(bdst, text_literal("A😀"), false)) == u32(6))
  }
  assert(same_bytes(view(&back), view(&le)))

  // Latin-1: "café" is 63 61 66 E9; UTF-8 needs five bytes.
  latin: [4]u8 = [4]u8{ 99, 97, 102, 233 }
  utf: [5]u8
  assert(text_result_value(latin1_to_utf8_size(view(&latin))) == u32(5))
  true ? {
    udst: [*]u8 = span(&utf)
    assert(text_result_value(latin1_to_utf8(udst, view(&latin))) == u32(5))
  }
  assert(text_equal(view(&utf), text_literal("café")))
  again: [4]u8
  true ? {
    adst: [*]u8 = span(&again)
    assert(text_result_value(utf8_to_latin1(adst, view(&utf))) == u32(4))
  }
  assert(same_bytes(view(&again), view(&latin)))
  assert(!text_result_ok(utf8_to_latin1_size(text_literal("😀"))))
  small: [2]u8
  true ? {
    sdst: [*]u8 = span(&small)
    assert(!text_result_ok(latin1_to_utf8(sdst, view(&latin))))
  }
  assert(small[0] == u8(0) && small[1] == u8(0))
  42
}
`
	code, abnormal := buildAndRun(t, "text_byte_order", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EStdlibTextSignedAndRadixNumbers(t *testing.T) {
	src := `
import(std)
parsed_i64: (src: []u8): i64 = text_parse_i64(src, u32(10)) ? | .Ok(v) => v | .Err(e) => i64(0) - i64(1)
parse_fails: (src: []u8, radix: u32): Bool = text_parse_i64(src, radix) ? | .Ok(v) => false | .Err(e) => true
main: (): i32 {
  assert(parsed_i64(text_literal("-42")) == i64(0) - i64(42))
  assert(parsed_i64(text_literal("+7")) == i64(7))
  assert(parsed_i64(text_literal("-0")) == i64(0))
  assert(parsed_i64(text_literal("9223372036854775807")) == i64(9223372036854775807))
  assert(parse_fails(text_literal("9223372036854775808"), u32(10)))
  assert(parsed_i64(text_literal("-9223372036854775808")) == i64_bits_u64(u64(9223372036854775808)))
  assert(parse_fails(text_literal("-9223372036854775809"), u32(10)))
  assert(parse_fails(text_literal("-"), u32(10)) && parse_fails(text_literal(""), u32(10)))
  assert(parse_fails(text_literal("1x"), u32(10)))
  hex_parsed: i64 = text_parse_i64(text_literal("-ff"), u32(16)) ? | .Ok(v) => v | .Err(e) => i64(0)
  assert(hex_parsed == i64(0) - i64(255))

  buffer: [80]u8
  n: u32 = 0
  true ? {
    dst: [*]u8 = span(&buffer)
    b: TextBuilder = text_builder()
    b = append_i64(b, dst, i64(0) - i64(42))
    b = append_text(b, dst, text_literal(" "))
    b = append_u64_radix(b, dst, u64(255), u32(16), true)
    b = append_text(b, dst, text_literal(" "))
    b = append_u64_radix(b, dst, u64(255), u32(16), false)
    b = append_text(b, dst, text_literal(" "))
    b = append_u64_radix(b, dst, u64(5), u32(2), false)
    b = append_text(b, dst, text_literal(" "))
    b = append_i64(b, dst, i64_bits_u64(u64(9223372036854775808)))
    n = text_result_value(finish_text(b))
    bad: TextBuilder = append_u64_radix(text_builder(), dst, u64(1), u32(37), false)
    assert(!text_result_ok(finish_text(bad)))
  }
  whole: []u8 = view(&buffer)
  written: []u8 = whole[u32(0):n]
  assert(text_equal(written, text_literal("-42 FF ff 101 -9223372036854775808")))
  tiny: [2]u8
  true ? {
    tdst: [*]u8 = span(&tiny)
    short: TextBuilder = append_i64(text_builder(), tdst, i64(0) - i64(100))
    assert(!text_result_ok(finish_text(short)))
  }
  42
}
`
	code, abnormal := buildAndRun(t, "text_signed_radix", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
