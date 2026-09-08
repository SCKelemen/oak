package compiler

import (
	"fmt"
	"math/rand"
	"strings"
	"testing"
)

func TestE2EJsonFastInteger(t *testing.T) {
	var source strings.Builder
	source.WriteString(`import(std)
check_integer: (src: []u8, offset: u32): Bool {
 fast: Result[JsonInteger, JsonDecodeError] = json_read_integer(src, offset)
 slow: Result[JsonInteger, JsonDecodeError] = json_read_integer_slow(src, offset)
 fast ?
 | .Err(a) => { slow ? | .Err(b) => json_decode_error_code(a) == json_decode_error_code(b) | .Ok(b) => false }
 | .Ok(a) => { slow ? | .Err(b) => false | .Ok(b) => a.magnitude == b.magnitude && a.negative == b.negative && a.next == b.next }
}
main: (): i32 {
 data: [1]u8
 n: u32 = 0
 while n < u32(256) {
  data[0] = u8_trunc_u32(n)
  byte_input: []u8 = view(&data)
  assert(check_integer(byte_input, u32(0)))
  n = n + u32(1)
 }
`)
	fixtures := []string{"", "0", "-0", "00", "-01", "-", "+1", "1.", "1.0", "1e0", "1e", "1e+", "1e-2", "0x1", "true", "false", "null", "[]", "{}", `"text"`, "18446744073709551615", "18446744073709551616", "-18446744073709551615", "184467440737095516150.0", "184467440737095516150e", strings.Repeat("9", 1024), strings.Repeat("9", 1024) + ".0", "01.0", "1,2", "1]", "1}", "1\t", "1x", "1\x00"}
	random := rand.New(rand.NewSource(731))
	for i := 0; i < 100; i++ {
		number := fmt.Sprintf("%d", random.Uint64())
		if i%2 == 0 {
			number = "-" + number
		}
		fixtures = append(fixtures, number)
	}
	for _, fixture := range fixtures {
		source.WriteString("true ? {\n")
		writeTextView(&source, "input", " \t"+fixture)
		source.WriteString("assert(check_integer(input, u32(0)))\nassert(check_integer(input, u32(2)))\n}\n")
	}
	source.WriteString("42\n}\n")
	_, code, abnormal := buildAndRunOutput(t, "json_fast_integer", source.String(), "-fsanitize=address,undefined", "-DOAK_PORTABLE_INTRINSICS")
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EJsonFastKeys(t *testing.T) {
	var source strings.Builder
	source.WriteString("import(std)\nmain: (): i32 {\n")
	for _, key := range []string{`""`, `"id"`, `"active"`, `"samples"`, `"\u0069d"`, `"a\\b"`, `"😀"`, `"\ud83d\ude00"`, `"é"`} {
		for _, expected := range []string{"", "id", "active", "samples", "a\\b", "😀", "é", "different"} {
			source.WriteString("true ? {\n")
			writeTextView(&source, "input", key)
			writeTextView(&source, "expected", expected)
			source.WriteString("key: JsonToken = json_token(input, u32(0))\nassert(key.kind == u32(6))\nassert(json_key_equal(input, key, expected) == json_key_equal_unicode(input, key, expected))\n}\n")
		}
	}
	source.WriteString("42\n}\n")
	_, code, abnormal := buildAndRunOutput(t, "json_fast_keys", source.String(), "-fsanitize=address,undefined", "-DOAK_PORTABLE_INTRINSICS")
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EJsonFastUtf8AndTokens(t *testing.T) {
	var source strings.Builder
	source.WriteString(`import(std)
main: (): i32 {
 data: [65]u8
 position: u32 = 0
 while position < u32(65) {
  unit_value: u32 = 0
  while unit_value < u32(256) {
   data[position] = u8_trunc_u32(unit_value)
   input: []u8 = view(&data)
   assert(json_valid_utf8(input) == is_valid_utf8(input))
   unit_value = unit_value + u32(1)
  }
  data[position] = u8(0)
  position = position + u32(1)
 }
`)
	for length := 0; length <= 65; length++ {
		source.WriteString("true ? {\n")
		writeTextView(&source, "ascii_input", strings.Repeat(" ", length))
		source.WriteString("assert(json_valid_utf8(ascii_input))\n}\n")
	}
	for _, prefix := range []int{0, 14, 15, 16, 30, 31, 32, 63} {
		for _, suffix := range []string{"é", "€", "😀", "\xc0\x80", "\xed\xa0\x80", "\xf4\x90\x80\x80", "\xf0\x9f"} {
			source.WriteString("true ? {\n")
			writeTextView(&source, "unicode_input", strings.Repeat(" ", prefix)+suffix)
			source.WriteString("assert(json_valid_utf8(unicode_input) == is_valid_utf8(unicode_input))\n}\n")
		}
	}
	for _, input := range []string{"", " ", "{", "}", "[", "]", ",", ":", " \ttrue", "false", "null", "01", "1e+", "-1", `"\ud800"`, `"\u0061"`, `"😀"`} {
		source.WriteString("true ? {\n")
		writeTextView(&source, "token_input", input)
		source.WriteString("a: JsonToken = json_token(token_input, u32(0))\nb: JsonToken = json_token_full(token_input, u32(0))\nassert(a.kind == b.kind && a.start == b.start && a.end == b.end)\n}\n")
	}
	source.WriteString("42\n}\n")
	_, code, abnormal := buildAndRunOutput(t, "json_fast_utf8", source.String(), "-fsanitize=address,undefined", "-DOAK_PORTABLE_INTRINSICS")
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
