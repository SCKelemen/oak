package compiler

import (
	"fmt"
	"strings"
	"testing"
)

const jsonOptionPrelude = `import(std)
json: tag = { name: string }
NullablePoint: type = struct { lanes: [2]i16 }
NullableRecord: type = struct { id(json: "record_id"): Option[u64], flag: Option[Bool], point: Option[NullablePoint] }
`

func TestE2EJsonOptionRoundTrip(t *testing.T) {
	var source strings.Builder
	source.WriteString(jsonOptionPrelude + "main: (): i32 {\n")
	for _, input := range []string{
		`{"record_id":null,"flag":null,"point":null}`,
		`{"record_id":18446744073709551615,"flag":false,"point":{"lanes":[-32768,32767]}}`,
		`{"record_id":0,"flag":true,"point":null}`,
	} {
		source.WriteString("true ? {\n")
		writeTextView(&source, "input", input)
		source.WriteString(`result: Result[NullableRecord, JsonDecodeError] = from[Json](input).to[NullableRecord]()
result ?
 | .Err(reason) => { assert(false) }
 | .Ok(value) => {
  data: [128]u8
  dst: [*]u8 = span(&data)
  assert(json_result_value(encoded_size[NullableRecord, Json](value)) == len(input))
  written: Result[u32, JsonError] = from[NullableRecord](value).to[Json](dst)
  assert(json_result_ok(written) && json_result_value(written) == len(input))
  i: u32 = 0
  while i < len(input) { assert(dst[i] == input[i])
   i = i + u32(1)
  }
  small: [4]u8
  tiny: [*]u8 = span(&small)
  bytes_fill(tiny, u8(77))
  assert(!json_result_ok(encode[NullableRecord, Json](value, tiny)))
  assert(tiny[0] == u8(77) && tiny[1] == u8(77) && tiny[2] == u8(77) && tiny[3] == u8(77))
 }
}
`)
	}
	source.WriteString("42\n}\n")
	_, code, abnormal := buildAndRunOutput(t, "json_option_roundtrip", source.String(), "-fsanitize=address,undefined", "-DOAK_PORTABLE_INTRINSICS")
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EJsonOptionErrors(t *testing.T) {
	var source strings.Builder
	source.WriteString(jsonOptionPrelude + "main: (): i32 {\n")
	for _, fixture := range []struct {
		input string
		code  int
	}{
		{`{}`, 5},
		{`{"record_id":null,"flag":null}`, 5},
		{`{"record_id":null,"\u0072ecord_id":0}`, 6},
		{`{"record_id":nullx}`, 2},
		{`{"record_id":nul}`, 2},
		{`{"record_id":null,}`, 2},
		{`{"record_id":true}`, 3},
		{`{"record_id":18446744073709551616}`, 4},
		{`{"flag":0}`, 3},
		{`{"point":[]}`, 3},
		{`{"point":{"lanes":[1]}}`, 8},
		{`{"point":{"lanes":[1,32768]}}`, 4},
		{`{"unknown":null}`, 7},
	} {
		source.WriteString("true ? {\n")
		writeTextView(&source, "input", fixture.input)
		fmt.Fprintf(&source, "result: Result[NullableRecord, JsonDecodeError] = decode[NullableRecord, Json](input)\nresult ? | .Ok(value) => { assert(false) } | .Err(reason) => { assert(json_decode_error_code(reason) == u32(%d)) }\n}\n", fixture.code)
	}
	source.WriteString("42\n}\n")
	_, code, abnormal := buildAndRunOutput(t, "json_option_errors", source.String(), "-fsanitize=address,undefined", "-DOAK_PORTABLE_INTRINSICS")
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestJsonOptionLowering(t *testing.T) {
	source := jsonOptionPrelude + `read: (src: []u8): Result[NullableRecord, JsonDecodeError] {
 from[Json](src).to[NullableRecord]()
}
write: (value: NullableRecord, dst: [*]u8): Result[u32, JsonError] {
 from[NullableRecord](value).to[Json](dst)
}
main: (): i32 = 0
`
	fluent, err := New().WithSource("option.oak", source).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	directSource := strings.ReplaceAll(source, "from[Json](src).to[NullableRecord]()", "decode[NullableRecord, Json](src)")
	directSource = strings.ReplaceAll(directSource, "from[NullableRecord](value).to[Json](dst)", "encode[NullableRecord, Json](value, dst)")
	direct, err := New().WithSource("option.oak", directSource).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	withoutLocations := func(code string) string {
		lines := []string{}
		for _, line := range strings.Split(code, "\n") {
			if !strings.HasPrefix(strings.TrimSpace(line), "// @source:") {
				lines = append(lines, line)
			}
		}
		return strings.Join(lines, "\n")
	}
	if withoutLocations(fluent) != withoutLocations(direct) {
		t.Fatal("nullable fluent/direct C differs")
	}
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "OAK_UNSUPPORTED"} {
		if strings.Contains(fluent, forbidden) {
			t.Fatalf("unexpected allocation or unsupported lowering: %s", forbidden)
		}
	}
	for _, typ := range []string{"Option[string]", "Option[Option[u32]]", "Option[[]u8]", "[2]Option[u32]"} {
		_, err := New().WithSource("bad_option.oak", "import(std)\nBad: type = struct { value: "+typ+" }\nf: (src: []u8): Result[Bad, JsonDecodeError] = decode[Bad, Json](src)").EmitC().Get()
		if err == nil {
			t.Fatalf("unsupported nullable type compiled: %s", typ)
		}
	}
}
