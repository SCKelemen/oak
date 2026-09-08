package compiler

import (
	"fmt"
	"strings"
	"testing"
)

const jsonDecodePrelude = `import(std)
json: tag = { name: string }
DecodePoint: type = struct { x: i16, y: u64 }
DecodeRecord: type = struct { id(json: "record_id"): u64, active: Bool, point: DecodePoint }
DecodeLabel: type = struct { number(json: "😀"): u32 }
`

func TestE2EJsonDecodeRecords(t *testing.T) {
	var source strings.Builder
	source.WriteString(jsonDecodePrelude + "main: (): i32 {\n")
	for _, input := range []string{
		`{"record_id":18446744073709551615,"active":true,"point":{"x":-32768,"y":9007199254740993}}`,
		" \r\n\t" + `{"point":{"y":9007199254740993,"x":-32768},"active":true,"\u0072ecord_id":18446744073709551615}` + "\r\n",
	} {
		source.WriteString("true ? {\n")
		writeTextView(&source, "input", input)
		source.WriteString(`
 result: Result[DecodeRecord, JsonDecodeError] = from[Json](input).to[DecodeRecord]()
 result ?
  | .Err(reason) => { assert(false) }
  | .Ok(value) => {
   assert(value.id == (u64(9223372036854775807) * u64(2) + u64(1)))
   assert(value.active)
   assert(value.point.x == i16(0) - i16(32767) - i16(1))
   assert(value.point.y == u64(9007199254740993))
  }
}
`)
	}
	for _, input := range []string{`{"😀":42}`, `{"\ud83d\ude00":42}`} {
		source.WriteString("true ? {\n")
		writeTextView(&source, "input", input)
		source.WriteString("result: Result[DecodeLabel, JsonDecodeError] = decode[DecodeLabel, Json](input)\nresult ? | .Err(reason) => { assert(false) } | .Ok(value) => { assert(value.number == u32(42)) }\n}\n")
	}
	for _, fixture := range []struct {
		input string
		code  int
	}{
		{`{}`, 5},
		{`{"record_id":1,"active":true}`, 5},
		{`{"record_id":1,"\u0072ecord_id":2}`, 6},
		{`{"extra":1}`, 7},
		{`{"record_id" 1}`, 2},
		{`{"record_id":1,}`, 2},
		{`{"record_id":1 "active":true}`, 2},
		{`{"record_id":1,"active":true,"point":{"x":0,"y":0}}x`, 2},
		{`{"record_id":1,"active":true,"point":{"x":0,"y":0}} {}`, 2},
		{`{"record_id":1,"active":true,"point":{"x":32768,"y":0}}`, 4},
		{`{"record_id":1,"active":true,"point":{"x":0}}`, 5},
		{`{"record_id":1,"active":true,"point":{"x":0,"y":0,"x":1}}`, 6},
		{`{"record_id":1,"active":1}`, 3},
		{`{"record_id":01}`, 2},
		{`{"record_id":1.0}`, 3},
		{`{"\ud800":0}`, 2},
		{`{"bad\x":0}`, 2},
		{"{\"bad\n\":0}", 2},
		{string([]byte{'{', '"', 255, '"', ':', '0', '}'}), 1},
		{`[]`, 3},
		{`null`, 3},
		{``, 2},
	} {
		source.WriteString("true ? {\n")
		writeTextView(&source, "input", fixture.input)
		fmt.Fprintf(&source, "result: Result[DecodeRecord, JsonDecodeError] = decode[DecodeRecord, Json](input)\nresult ? | .Ok(value) => { assert(false) } | .Err(reason) => { assert(json_decode_error_code(reason) == u32(%d)) }\n}\n", fixture.code)
	}
	source.WriteString("42\n}\n")
	_, code, abnormal := buildAndRunOutput(t, "json_decode_record", source.String(), "-fsanitize=address,undefined", "-DOAK_PORTABLE_INTRINSICS")
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EJsonDecodeScalars(t *testing.T) {
	var source strings.Builder
	source.WriteString("import(std)\nmain: (): i32 {\n")
	for _, fixture := range []struct{ typ, input, value string }{
		{"u8", "255", "u8(255)"}, {"u16", "65535", "u16(65535)"},
		{"u32", "4294967295", "u32(4294967295)"},
		{"u64", "18446744073709551615", "(u64(9223372036854775807) * u64(2) + u64(1))"},
		{"i8", "-128", "(i8(0) - i8(127) - i8(1))"},
		{"i16", "-32768", "(i16(0) - i16(32767) - i16(1))"},
		{"i32", "-2147483648", "(i32(0) - i32(2147483647) - i32(1))"},
		{"i64", "-9223372036854775808", "(i64(0) - i64(9223372036854775807) - i64(1))"},
		{"i64", "9223372036854775807", "i64(9223372036854775807)"},
		{"i64", "-0", "i64(0)"}, {"u64", "0", "u64(0)"},
		{"Bool", " true \n", "true"}, {"Bool", "false", "false"},
	} {
		source.WriteString("true ? {\n")
		writeTextView(&source, "input", fixture.input)
		fmt.Fprintf(&source, "result: Result[%s, JsonDecodeError] = decode[%s, Json](input)\nresult ? | .Err(reason) => { assert(false) } | .Ok(value) => { assert(value == %s) }\n}\n", fixture.typ, fixture.typ, fixture.value)
	}
	for _, fixture := range []struct {
		typ, input string
		code       int
	}{
		{"u8", "256", 4}, {"u16", "65536", 4}, {"u32", "4294967296", 4},
		{"u64", "18446744073709551616", 4}, {"i8", "128", 4}, {"i8", "-129", 4},
		{"i16", "32768", 4}, {"i32", "2147483648", 4}, {"i64", "9223372036854775808", 4},
		{"i64", "-9223372036854775809", 4}, {"u64", "-0", 3}, {"u32", "-1", 3},
		{"u64", strings.Repeat("9", 1024), 4},
		{"u64", "01", 2}, {"i64", "-01", 2}, {"i64", "-", 2}, {"i64", "+1", 2},
		{"i64", "1.", 2}, {"i64", "1e", 2}, {"i64", "1e+", 2}, {"i64", "1.5", 3},
		{"i64", "1e2", 3}, {"i64", "12x", 2}, {"i64", "0 1", 2},
		{"Bool", "truex", 2}, {"Bool", "tru", 2}, {"Bool", "null", 3},
		{"Bool", "1", 3}, {"Bool", "false true", 2},
	} {
		source.WriteString("true ? {\n")
		writeTextView(&source, "input", fixture.input)
		fmt.Fprintf(&source, "result: Result[%s, JsonDecodeError] = decode[%s, Json](input)\nresult ? | .Ok(value) => { assert(false) } | .Err(reason) => { assert(json_decode_error_code(reason) == u32(%d)) }\n}\n", fixture.typ, fixture.typ, fixture.code)
	}
	source.WriteString("42\n}\n")
	_, code, abnormal := buildAndRunOutput(t, "json_decode_scalar", source.String(), "-fsanitize=address,undefined")
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestJsonDecodeLowering(t *testing.T) {
	source := jsonDecodePrelude + `main: (): i32 {
 input: []u8 = text_literal("42")
 result: Result[u64, JsonDecodeError] = from[Json](input).to[u64]()
 result ? | .Ok(value) => { assert(value == u64(42)) } | .Err(reason) => { assert(false) }
 42
}`
	fluent, err := New().WithSource("decode.oak", source).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	direct, err := New().WithSource("decode.oak", strings.ReplaceAll(source, "from[Json](input).to[u64]()", "decode[u64, Json](input)")).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if fluent != direct {
		t.Fatal("fluent decoding emitted different C")
	}
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "OAK_UNSUPPORTED"} {
		if strings.Contains(fluent, forbidden) {
			t.Fatalf("unexpected allocation or unsupported lowering: %s", forbidden)
		}
	}
	for _, source := range []string{
		`f: (src: []u8): Result[string, JsonDecodeError] = decode[string, Json](src)`,
		`Bad: type = struct { text: string }
f: (src: []u8): Result[Bad, JsonDecodeError] = decode[Bad, Json](src)`,
	} {
		if _, err := New().WithSource("borrowed_decode.oak", "import(std)\n"+source).EmitC().Get(); err == nil {
			t.Fatal("borrowed decode must not compile without lifetime contracts")
		}
	}
}

func TestE2EJsonDecodeControlFlow(t *testing.T) {
	source := `Item: type = Value: i32 | Empty
read: (item: Item): i32 = item ?
 | .Value(n) => {
  n > 0 ? { incremented: i32 = n + 1
   incremented
  } | { replacement: i32 = 10
   replacement
  }
 }
 | .Empty => 0
classify: (n: i32): i32 {
 result: i32 = 0
 n == 0 ? { result = 1 } | n == 1 ? {
  chosen: i32 = 2
  result = chosen
 } | { result = 3 }
 result
}
main: (): i32 {
 positive: Item = .Value(20)
 negative: Item = .Value(0 - 1)
 empty: Item = .Empty
 assert(read(empty) == 0)
 read(positive) + read(negative) + classify(0) + classify(1) + classify(2) + 5
}`
	code, abnormal := buildAndRun(t, "decoder_control_flow", source)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
