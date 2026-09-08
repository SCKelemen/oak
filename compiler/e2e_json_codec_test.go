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
 encoded_data: [7]u8
 encoded_data[0] = u8(34)
 encoded_data[1] = u8(104)
 encoded_data[2] = u8(101)
 encoded_data[3] = u8(108)
 encoded_data[4] = u8(108)
 encoded_data[5] = u8(111)
 encoded_data[6] = u8(34)
 encoded: []u8 = view(&encoded_data)
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
true ? {
 input: []u8 = text_literal("x")
 data: [6]u8
 dst: [*]u8 = span(&data)
 assert(!json_result_ok(json_encoder().finish_json()))
 encoder: JsonEncoder[JsonStrict] = json_encoder().append_json_string(dst, input)
 assert(json_result_value(encoder.finish_json()) == u32(3))
 dst[3] = u8(77)
 twice: JsonEncoder[JsonStrict] = encoder.append_json_string(dst, input)
 assert(!json_result_ok(twice.finish_json()))
 assert(twice.written == u32(3) && dst[3] == u8(77))
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
	// Two u32 fields only: the policy contributes no tag or payload.
	if !strings.Contains(emitted, "sizeof(oak_JsonEncoder_JsonStrict) == 8u") {
		t.Fatal("phantom policy changed cursor layout")
	}
	if !strings.Contains(emitted, "vld1q_u8") || !strings.Contains(emitted, "vst1q_u8") {
		t.Fatal("missing NEON block load/store lowering")
	}
}

func TestE2EJsonCodecScanner(t *testing.T) {
	source := `import(std)
main: (): i32 {
 data: [65]u8
 unitValue: u32 = 0
 while unitValue < u32(256) {
  position: u32 = 0
  while position < u32(65) {
   i: u32 = 0
   while i < u32(65) { data[i] = u8(65)
    i = i + u32(1)
   }
   data[position] = u8_trunc_u32(unitValue)
   true ? {
    input: []u8 = view(&data)
    expected: u32 = unitValue < u32(32) || unitValue == u32(34) || unitValue == u32(92) ? position | u32(65)
    assert(json_string_run(input, u32(0)) == expected)
    assert(json_string_run(input, position) == expected)
    assert(json_string_run(input, u32(65)) == u32(65))
   }
   position = position + u32(1)
  }
  unitValue = unitValue + u32(1)
 }
 42
}`
	_, code, abnormal := buildAndRunOutput(t, "json_scan", source, "-DOAK_PORTABLE_INTRINSICS", "-fsanitize=address,undefined")
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestJsonCodecRejectsPolicyMismatch(t *testing.T) {
	source := `import(std)
Other: type = | OtherPolicy
main: (): i32 {
 encoder: JsonEncoder[Other]
 encoder.written = u32(0)
 encoder.status = u32(0)
 finish_json(encoder)
 42
}`
	_, err := New().WithSource("json_policy.oak", source).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "JsonEncoder") {
		t.Fatalf("expected nominal policy mismatch, got %v", err)
	}
}
