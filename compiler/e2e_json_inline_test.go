package compiler

import (
	"strings"
	"testing"
)

// The derived record reader's hot path (docs/spec/71-codecs.md section 20):
// integer and Boolean fields decode in place through the compact scanner
// instead of the per-type reader's Result round trip, the opening brace and
// bracket are one byte after whitespace, an escaped key is decoded once and
// compared byte for byte, and the scanner and its word arithmetic are forced
// inline. The emitted C is asserted for each, and a document with an
// escaped key, reordered fields and whitespace decodes to the same values.
const jsonInlineProgram = `import(std)
Bench: type = struct { id: u64, active: Bool, samples: [4]i32 }
read_bench: (src: []u8): Result[Bench, JsonDecodeError] = decode[Bench, Json](src)
main: (): i32 {
  text: string = " { \"samples\":[-2147483648,2147483647,123456,-123456], \"\\u0061ctive\":true, \"id\":18446744073709551615 } "
  bytes: []u8 = str_bytes(text)
  result: Result[Bench, JsonDecodeError] = read_bench(bytes)
  result ?
  | .Ok(value) => {
    value.id == u64(18446744073709551615) && value.active && value.samples[u32(0)] == i32(0) - i32(2147483647) - i32(1) &&
      value.samples[u32(1)] == i32(2147483647) && value.samples[u32(2)] == i32(123456) && value.samples[u32(3)] == i32(0) - i32(123456) ? 42 | 1
  }
  | .Err(_) => 2
}
`

func TestE2EDerivedJsonReaderDecodesScalarsInline(t *testing.T) {
	output, err := New().WithSource("json_inline.oak", jsonInlineProgram).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	reader := output[strings.Index(output, "oak___oak_json_read_Bench( oak_view_u8 src, u32 offset ) {"):]
	reader = reader[:strings.Index(reader, "\n}\n")]
	for _, want := range []string{
		"oak_json_scan_integer( src, colon.end )",  // the u64 field, in place
		"oak_json_scan_integer( src, at )",         // the array elements, from the element start
		"( src ).base[ open_at ] == ((u8)( 123 ))", // the opening brace by byte
		"( src ).base[ array_at ] == ((u8)( 91 ))", // the opening bracket by byte
		// The fixed integer array: one structural pass over the span, then
		// every element parsed from its own extent (section 21).
		"oak_json_array_index( src, at, (oak_span_u32){ marks.v, 4 } )",
		"oak_json_digits_at( src, digits_at, oak_sub_u32( sep, digits_at ) )",
	} {
		if !strings.Contains(reader, want) {
			t.Fatalf("record reader lacks %q:\n%s", want, reader)
		}
	}
	for _, unwanted := range []string{"oak___oak_json_read_u64( src", "oak___oak_json_read_i32( src", "oak___oak_json_read_Bool( src", "oak_byte_pack_le_u32( src", "oak_byte_pack_le_u64( src", "oak_JsonToken separator"} {
		if strings.Contains(reader, unwanted) {
			t.Fatalf("record reader still calls the per-type reader %q:\n%s", unwanted, reader)
		}
	}
	for _, want := range []string{
		// Key and Boolean spellings load through packs the checker proved
		// in range under the wrap-free remaining guard: no check.
		"oak_byte_pack_le_u64_proven( src, at )",
		"oak_byte_pack_le_u32_proven( src, value_at )",
		"OAK_INLINE oak_JsonIntegerScan oak_json_scan_integer(",
		"OAK_INLINE u32 oak_json_skip_space(",
		"OAK_INLINE oak_JsonIntegerScan oak_json_digits_at(",
		// The digit words of an indexed element load through proven packs.
		"oak_byte_pack_le_u64_proven( src, (u64)( base ) + 8u )",
		"oak_json_key_decode( src, key, (oak_span_u8){ storage.v, 64 } )",
		"oak_json_key_decoded_equal( decoded, key",
	} {
		if !strings.Contains(output, want) {
			t.Fatalf("emitted C lacks %q", want)
		}
	}
	code, abnormal := buildAndRun(t, "json_inline", jsonInlineProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v), want 42", code, abnormal)
	}
}
