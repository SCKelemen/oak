package compiler

import "testing"

func TestE2EStdlibTextSmoke(t *testing.T) {
	code, abnormal := buildAndRun(t, "textsmoke", `
import(std)
main: (): i32 {
 input: [4]u8
 input[0] = u8(240)
 input[1] = u8(159)
 input[2] = u8(152)
 input[3] = u8(128)
 src: []u8 = view(&input)
 assert(utf8_validate(src))
 assert(text_result_value(utf8_count(src)) == u32(1))
 decoded: TextScalar = text_decoded(utf8_decode(src, u32(0)))
 assert(decoded.value == u32(128512) && decoded.next == u32(4))
 wide: [2]u16
 true ? {
  dst: [*]u16 = span(&wide)
  assert(text_result_value(utf8_to_utf16(dst, src)) == u32(2))
  assert(dst[0] == u16(55357) && dst[1] == u16(56832))
 }
 true ? {
  units: []u16 = view(&wide)
  out: [4]u8
  dst: [*]u8 = span(&out)
  assert(text_result_value(utf16_to_utf8(dst, units)) == u32(4))
  assert(dst[0] == u8(240) && dst[3] == u8(128))
 }
 assert(text_contains(src, src))
 assert(option_or(text_index_rune(src, u32(128512)), u32(99)) == u32(0))
 42
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
