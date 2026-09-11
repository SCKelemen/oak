package compiler

import "testing"

// F9 and F10: a string view conversion stands directly in argument position
// as a temporary with the call's extent, from a literal or from a tracked
// string source, so the path and text helpers take spelled text without a
// binding per call.
func TestE2EStringLiteralArguments(t *testing.T) {
	src := `
import(std)
count: (name: string): u32 = len(str_bytes(name))
first: (bytes: []u8): u8 = len(bytes) > u32(0) ? bytes[0] | u8(0)
main: (): i32 {
  parsed: Result[u64, TextParseError] = text_parse_u64(str_bytes("42"), u32(10))
  value: u64 = parsed ? | .Ok(v) => v | .Err(e) => u64(0)
  assert(value == u64(42))
  who: string = "oak"
  assert(count(who) == u32(3) && count("tree") == u32(4))
  assert(first(str_bytes(who)) == u8(111) && first(str_bytes("x")) == u8(120))
  out: [16]u8
  n: u32 = u32(0)
  true ? {
    dst: [*]u8 = span(&out)
    n = path_written(path_clean(dst, str_bytes("a/./b//c/..")))
  }
  cleaned: []u8 = view(&out)
  assert(n == u32(3) && bytes_equal(cleaned[u32(0):n], str_bytes("a/b")))
  assert(bytes_equal(str_bytes(who), str_bytes("oak")))
  42
}
`
	code, abnormal := buildAndRun(t, "string_literal_arguments", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
