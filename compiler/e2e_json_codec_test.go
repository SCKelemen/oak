package compiler

import (
	"encoding/json"
	"fmt"
	"strings"
	"testing"
)

func TestE2EJsonCodec(t *testing.T) {
	var source strings.Builder
	source.WriteString("import(std)\nmain: (): i32 {\n")
	fixtures := []string{"", "hello", "é世界😀", "\x00\b\t\n\f\r\"\\/", strings.Repeat("a", 65)}
	for _, n := range []int{15, 16, 17, 31, 32, 33, 63, 64} {
		fixtures = append(fixtures, strings.Repeat("x", n)+"\"\\\n😀")
	}
	for _, value := range fixtures {
		source.WriteString("true ? {\n")
		writeTextView(&source, "input", value)
		// The encoder uses uniform six-byte escapes for all control bytes.
		var encoded strings.Builder
		encoded.WriteByte('"')
		for _, b := range []byte(value) {
			switch {
			case b < 32:
				fmt.Fprintf(&encoded, "\\u%04x", b)
			case b == '"' || b == '\\':
				encoded.WriteByte('\\')
				encoded.WriteByte(b)
			default:
				encoded.WriteByte(b)
			}
		}
		encoded.WriteByte('"')
		var decoded string
		if err := json.Unmarshal([]byte(encoded.String()), &decoded); err != nil || decoded != value {
			t.Fatalf("invalid reference encoding: %v", err)
		}
		writeTextView(&source, "expected", encoded.String())
		fmt.Fprintf(&source, "out_data: [%d]u8\ntrue ? {\ndst: [*]u8 = span(&out_data)\n", encoded.Len())
		source.WriteString("encoder: JsonEncoder[JsonStrict] = json_encoder().append_json_string(dst, input)\nassert(json_result_value(encoder.finish_json()) == len(expected))\n}\nactual: []u8 = view(&out_data)\nassert(text_equal(actual, expected))\n")
		fmt.Fprintf(&source, "decoded_data: [%d]u8\ntrue ? {\ndst: [*]u8 = span(&decoded_data)\nassert(json_result_value(json_string_decode(dst, actual)) == len(input))\n}\nback: []u8 = view(&decoded_data)\nassert(text_equal(back, input))\n}\n", len(value))
	}
	// Independent JSON inputs cover every short escape and surrogate pairs.
	for _, encoded := range []string{`"\/\b\f\n\r\t\"\\"`, `"\u0000\u00e9\u4e16\uD83D\uDE00"`, `"\udbff\udfff"`} {
		var decoded string
		if err := json.Unmarshal([]byte(encoded), &decoded); err != nil {
			t.Fatal(err)
		}
		source.WriteString("true ? {\n")
		writeTextView(&source, "input", encoded)
		writeTextView(&source, "expected", decoded)
		fmt.Fprintf(&source, "data: [%d]u8\ntrue ? {\ndst: [*]u8 = span(&data)\nassert(json_result_value(json_string_decode(dst, input)) == len(expected))\n}\nactual: []u8 = view(&data)\nassert(text_equal(actual, expected))\n}\n", len(decoded))
	}
	for _, invalid := range []string{"", `"`, `"unterminated`, `"a"x`, `"a""`, "\"\n\"", `"\x"`, `"\u"`, `"\uZZZZ"`, `"\ud800"`, `"\udc00"`, `"\ud800\u0041"`, `"\ud800\ud800"`, `"\ud800\u"`, string([]byte{'"', 255, '"'}), `"\"`} {
		source.WriteString("true ? {\n")
		writeTextView(&source, "input", invalid)
		source.WriteString("data: [8]u8\ndst: [*]u8 = span(&data)\ni: u32 = 0\nwhile i < len(dst) { dst[i] = u8(77)\ni = i + u32(1)\n}\nassert(!json_result_ok(json_string_decode(dst, input)))\ni = u32(0)\nwhile i < len(dst) { assert(dst[i] == u8(77))\ni = i + u32(1)\n}\n}\n")
	}
	source.WriteString(`
true ? {
 input: []u8 = text_literal("hello")
 encoded: []u8 = text_literal("\"hello\"")
 data: [4]u8
 dst: [*]u8 = span(&data)
 dst[0] = u8(77)
 dst[3] = u8(88)
 assert(!json_result_ok(json_string_encode(dst, input)))
 assert(!json_result_ok(json_string_decode(dst, encoded)))
 assert(!json_result_ok(json_string_encode_at(dst, u32(4294967295), input)))
 encoder: JsonEncoder[JsonStrict] = json_encoder().append_json_string(dst, input).append_json_string(dst, input)
 assert(!json_result_ok(encoder.finish_json()))
 assert(encoder.written == u32(0))
 assert(dst[0] == u8(77) && dst[3] == u8(88))
}
42
}
`)
	for _, flags := range [][]string{{}, {"-DOAK_PORTABLE_INTRINSICS"}} {
		_, code, abnormal := buildAndRunOutput(t, "json_codec", source.String(), flags...)
		if abnormal || code != 42 {
			t.Fatalf("flags=%v exit=(%d,%v)", flags, code, abnormal)
		}
	}
}

func TestJsonCodecLowering(t *testing.T) {
	source := `import(std)
main: (): i32 {
 input: []u8 = text_literal("abcdefghijklmnopq")
 data: [32]u8
 dst: [*]u8 = span(&data)
 encoder: JsonEncoder[JsonStrict] = json_encoder().append_json_string(dst, input)
 assert(json_result_value(encoder.finish_json()) == u32(19))
 42
}`
	emitted, err := New().WithSource("json_codec.oak", source).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "OAK_UNSUPPORTED", ".append_json_string(", ".finish_json("} {
		if strings.Contains(emitted, forbidden) {
			t.Fatalf("unexpected lowering: %s", forbidden)
		}
	}
	// The policy must not become a field of the emitted cursor record.
	if !strings.Contains(emitted, "vld1q_u8") || !strings.Contains(emitted, "vst1q_u8") {
		t.Fatal("missing NEON block load/store lowering")
	}
}
