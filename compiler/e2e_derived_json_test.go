package compiler

import (
	"strings"
	"testing"
)

const derivedJsonPrelude = `import(std)
json: tag = { name: string }
Point: type = struct { x: i32, y: u64 }
Record: type = struct {
 id(json: "record_id"): u64
 active: Bool
 point: Point
}
make_record: (): Record {
 value: Record
 value.id = (u64(9223372036854775807) * u64(2) + u64(1))
 value.active = true
 value.point.x = i32(0) - i32(42)
 value.point.y = u64(9007199254740993)
 value
}
`

func TestE2EDerivedJson(t *testing.T) {
	var source strings.Builder
	source.WriteString(derivedJsonPrelude + "main: (): i32 {\n")
	expected := `{"record_id":18446744073709551615,"active":true,"point":{"x":-42,"y":9007199254740993}}`
	writeTextView(&source, "expected", expected)
	source.WriteString(`
 value: Record = make_record()
 assert(json_result_value(encoded_size[Record, Json](value)) == len(expected))
 data: [128]u8
 true ? {
  dst: [*]u8 = span(&data)
  result: Result[u32, JsonError] = from[Record](value).to[Json](dst)
  assert(json_result_value(result) == len(expected))
  i: u32 = 0
  while i < len(expected) { assert(dst[i] == expected[i])
   i = i + u32(1)
  }
 }
 small: [4]u8
 dst: [*]u8 = span(&small)
 dst[0] = u8(77)
 dst[3] = u8(88)
 assert(!json_result_ok(encode[Record, Json](value, dst)))
 assert(dst[0] == u8(77) && dst[3] == u8(88))
 42
}
`)
	code, abnormal := buildAndRun(t, "derived_json_record", source.String())
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EDerivedJsonScalars(t *testing.T) {
	var source strings.Builder
	source.WriteString("import(std)\nmain: (): i32 {\n")
	for _, fixture := range []struct{ typ, expr, expected string }{
		{"u64", "(u64(9223372036854775807) * u64(2) + u64(1))", "18446744073709551615"},
		{"u8", "u8(255)", "255"},
		{"i64", "i64(0) - i64(9223372036854775807) - i64(1)", "-9223372036854775808"},
		{"i64", "i64(9223372036854775807)", "9223372036854775807"},
		{"i8", "i8(0) - i8(127) - i8(1)", "-128"},
		{"i32", "i32(0)", "0"},
		{"Bool", "false", "false"},
		{"Bool", "true", "true"},
		{"string", `"hello"`, `"hello"`},
	} {
		source.WriteString("true ? {\n")
		writeTextView(&source, "expected", fixture.expected)
		source.WriteString("value: " + fixture.typ + " = " + fixture.expr + "\ndata: [32]u8\ndst: [*]u8 = span(&data)\n")
		source.WriteString("assert(json_result_value(encode[" + fixture.typ + ", Json](value, dst)) == len(expected))\ni: u32 = 0\nwhile i < len(expected) { assert(dst[i] == expected[i])\ni = i + u32(1)\n}\n}\n")
	}
	source.WriteString("42\n}\n")
	code, abnormal := buildAndRun(t, "derived_json_scalars", source.String())
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestDerivedJsonLowering(t *testing.T) {
	fluent := derivedJsonPrelude + `main: (): i32 {
 data: [128]u8
 dst: [*]u8 = span(&data)
 assert(json_result_ok(from[Record](make_record()).to[Json](dst)))
 42
}`
	direct := strings.ReplaceAll(fluent, "from[Record](make_record()).to[Json](dst)", "encode[Record, Json](make_record(), dst)")
	a, err := New().WithSource("derived.oak", fluent).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	b, err := New().WithSource("derived.oak", direct).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if a != b {
		t.Fatal("fluent and direct codecs emit different C")
	}
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "OAK_UNSUPPORTED"} {
		if strings.Contains(a, forbidden) {
			t.Fatalf("unexpected generated code: %s", forbidden)
		}
	}
}

func TestDerivedJsonRejectsUnsupported(t *testing.T) {
	for _, fixture := range []struct{ source, message string }{
		{`Bad: type = struct { x: f64 }
f: (x: Bad, out: [*]u8): Result[u32, JsonError] = encode[Bad, Json](x, out)`, "unsupported type f64"},
		{`Bad: type = struct { x: string }
f: (x: Bad, out: [*]u8): Result[u32, JsonError] = encode[Bad, Json](x, out)`, "unsupported field Bad.x"},
		{`json: tag = { name: string }
Bad: type = struct { a(json: "same"): u32, b(json: "same"): u32 }
f: (x: Bad, out: [*]u8): Result[u32, JsonError] = encode[Bad, Json](x, out)`, "duplicate JSON field"},
		{`json: tag = { name: string, omit: Bool }
Bad: type = struct { a(json: { omit: true }): u32 }
f: (x: Bad, out: [*]u8): Result[u32, JsonError] = encode[Bad, Json](x, out)`, "only name is supported"},
		{`f: (out: [*]u8): Result[u32, JsonError] = encode[u32, MsgPack](u32(1), out)`, "Json format"},
		{`f: (): u32 = from[u32](u32(1))`, "immediately consumed"},
		{`__oak_json_encode_u32: (): u32 = u32(0)
f: (out: [*]u8): Result[u32, JsonError] = encode[u32, Json](u32(1), out)`, "conflicts"},
	} {
		_, err := New().WithSource("bad_codec.oak", "import(std)\n"+fixture.source).EmitC().Get()
		if err == nil || !strings.Contains(err.Error(), fixture.message) {
			t.Fatalf("expected %q, got %v", fixture.message, err)
		}
	}
}
