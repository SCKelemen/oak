package compiler

import (
	"fmt"
	"strings"
	"testing"
)

const jsonArrayPrelude = `import(std)
json: tag = { name: string }
ArrayPoint: type = struct { lanes: [2]i16 }
ArrayRecord: type = struct { points(json: "items"): [2]ArrayPoint, flags: [1]Bool, ids: [2]u64 }
`

func TestE2EJsonArrayMatchPayload(t *testing.T) {
	source := `Pair: type = struct { lanes: [2]i32 }
Wrapped: type = Present: Pair | Absent
read: (wrapped: Wrapped): i32 = wrapped ?
 | .Present(pair) => pair.lanes[0] + pair.lanes[1]
 | .Absent => 0
main: (): i32 {
 pair: Pair
 pair.lanes[0] = 20
 pair.lanes[1] = 22
 wrapped: Wrapped = .Present(pair)
 read(wrapped)
}`
	code, abnormal := buildAndRun(t, "array_match_payload", source)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EJsonArrayRoundTrip(t *testing.T) {
	var source strings.Builder
	source.WriteString(jsonArrayPrelude + "main: (): i32 {\n")
	writeTextView(&source, "input", ` { "ids": [0,18446744073709551615], "flags": [true], "\u0069tems": [{"lanes":[-32768,32767]},{"lanes":[0,-1]}] } `)
	writeTextView(&source, "expected", `{"items":[{"lanes":[-32768,32767]},{"lanes":[0,-1]}],"flags":[true],"ids":[0,18446744073709551615]}`)
	source.WriteString(`
 result: Result[ArrayRecord, JsonDecodeError] = from[Json](input).to[ArrayRecord]()
 result ?
  | .Err(reason) => { assert(false) }
  | .Ok(value) => {
   assert(value.points[0].lanes[0] == i16(0) - i16(32767) - i16(1))
   assert(value.points[1].lanes[1] == i16(0) - i16(1))
   assert(value.flags[0])
   assert(value.ids[1] == (u64(9223372036854775807) * u64(2) + u64(1)))
   assert(json_result_value(encoded_size[ArrayRecord, Json](value)) == len(expected))
   data: [128]u8
   dst: [*]u8 = span(&data)
   written: Result[u32, JsonError] = from[ArrayRecord](value).to[Json](dst)
   assert(json_result_ok(written) && json_result_value(written) == len(expected))
   i: u32 = 0
   while i < len(expected) { assert(dst[i] == expected[i])
    i = i + u32(1)
   }
   small: [4]u8
   tiny: [*]u8 = span(&small)
   bytes_fill(tiny, u8(77))
   assert(!json_result_ok(encode[ArrayRecord, Json](value, tiny)))
   assert(tiny[0] == u8(77) && tiny[1] == u8(77) && tiny[2] == u8(77) && tiny[3] == u8(77))
  }
 42
}
`)
	_, code, abnormal := buildAndRunOutput(t, "json_array_roundtrip", source.String(), "-fsanitize=address,undefined", "-DOAK_PORTABLE_INTRINSICS")
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EJsonArrayErrors(t *testing.T) {
	var source strings.Builder
	source.WriteString(jsonArrayPrelude + "main: (): i32 {\n")
	for _, fixture := range []struct {
		input string
		code  int
	}{
		{`{"lanes":[]}`, 8},
		{`{"lanes":[1]}`, 8},
		{`{"lanes":[1,2,3]}`, 8},
		{`{"lanes":[1,]}`, 2},
		{`{"lanes":[1,2,]}`, 2},
		{`{"lanes":[1 2]}`, 2},
		{`{"lanes":[1,2}`, 2},
		{`{"lanes":[1,`, 2},
		{`{"lanes":[1,2`, 2},
		{`{"lanes":[32768,0]}`, 4},
		{`{"lanes":[0,-32769]}`, 4},
		{`{"lanes":[true,0]}`, 3},
		{`{"lanes":[[1],0]}`, 3},
		{`{"lanes":null}`, 3},
		{`{"lanes":0}`, 3},
		{`{}`, 5},
		{`{"lanes":[1,2],"lanes":[3,4]}`, 6},
	} {
		source.WriteString("true ? {\n")
		writeTextView(&source, "input", fixture.input)
		fmt.Fprintf(&source, "result: Result[ArrayPoint, JsonDecodeError] = decode[ArrayPoint, Json](input)\nresult ? | .Ok(value) => { assert(false) } | .Err(reason) => { assert(json_decode_error_code(reason) == u32(%d)) }\n}\n", fixture.code)
	}
	source.WriteString("42\n}\n")
	_, code, abnormal := buildAndRunOutput(t, "json_array_errors", source.String(), "-fsanitize=address,undefined", "-DOAK_PORTABLE_INTRINSICS")
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestJsonArrayLowering(t *testing.T) {
	source := jsonArrayPrelude + `read: (input: []u8): Result[ArrayRecord, JsonDecodeError] {
 from[Json](input).to[ArrayRecord]()
}
write: (value: ArrayRecord, dst: [*]u8): Result[u32, JsonError] {
 from[ArrayRecord](value).to[Json](dst)
}
main: (): i32 = 0
`
	fluent, err := New().WithSource("array.oak", source).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	directSource := strings.ReplaceAll(source, "from[Json](input).to[ArrayRecord]()", "decode[ArrayRecord, Json](input)")
	directSource = strings.ReplaceAll(directSource, "from[ArrayRecord](value).to[Json](dst)", "encode[ArrayRecord, Json](value, dst)")
	direct, err := New().WithSource("array.oak", directSource).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	// Different source spellings may carry different source-range comments.
	// Compare every executable line, preserving declarations and checks.
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
		a, b := strings.Split(withoutLocations(fluent), "\n"), strings.Split(withoutLocations(direct), "\n")
		for i := 0; i < len(a) && i < len(b); i++ {
			if a[i] != b[i] {
				t.Fatalf("array fluent/direct C differs at line %d:\nfluent: %s\ndirect: %s", i+1, a[i], b[i])
			}
		}
		t.Fatal("array fluent/direct C lengths differ")
	}
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "OAK_UNSUPPORTED"} {
		if strings.Contains(fluent, forbidden) {
			t.Fatalf("unexpected allocation or unsupported lowering: %s", forbidden)
		}
	}
	for _, typ := range []string{"[0]u8", "[]u8", "[*]u8", "[2]string", "[2][2]u8"} {
		for _, operation := range []string{"encode", "decode"} {
			body := "f: (value: Bad, dst: [*]u8): Result[u32, JsonError] = encode[Bad, Json](value, dst)"
			if operation == "decode" {
				body = "f: (src: []u8): Result[Bad, JsonDecodeError] = decode[Bad, Json](src)"
			}
			_, err := New().WithSource("bad_array.oak", "import(std)\nBad: type = struct { data: "+typ+" }\n"+body).EmitC().Get()
			if err == nil || !strings.Contains(err.Error(), "codec:") {
				t.Fatalf("%s %s: expected codec rejection, got %v", operation, typ, err)
			}
		}
	}
}

// The structural-index fast path of a fixed integer array (section 21)
// agrees with the sequential loop on every shape the corpus exercises, and
// hands the loop every shape it does not cover: whitespace around
// elements, a space before a separator, signs, a leading zero, more than
// sixteen digits, and the width boundaries.
func TestE2EJsonArrayIndexedPath(t *testing.T) {
	var source strings.Builder
	source.WriteString(`import(std)
json: tag = { name: string }
Wide: type = struct { a: [6]i64, b: [3]u32, c: [2]u64 }
main: (): i32 {
`)
	writeTextView(&source, "input", `{"a":[ 1, -2 ,3,1234567890123456,-999999999 , 0],"b":[7,08,4294967295],"c":[18446744073709551615,12345678901234567]}`)
	writeTextView(&source, "fixed", `{"a":[1,-2,3,1234567890123456,-999999999,0],"b":[7,8,4294967295],"c":[18446744073709551615,12345678901234567]}`)
	source.WriteString(`
 first: Result[Wide, JsonDecodeError] = decode[Wide, Json](input)
 first ?
  | .Ok(value) => { assert(false) }
  | .Err(reason) => { assert(json_decode_error_code(reason) == u32(2)) }
 second: Result[Wide, JsonDecodeError] = decode[Wide, Json](fixed)
 second ?
  | .Err(reason) => { assert(false) }
  | .Ok(value) => {
   assert(value.a[0] == i64(1) && value.a[1] == i64(0) - i64(2) && value.a[2] == i64(3))
   assert(value.a[3] == i64(1234567890123456) && value.a[4] == i64(0) - i64(999999999) && value.a[5] == i64(0))
   assert(value.b[0] == u32(7) && value.b[1] == u32(8) && value.b[2] == u32(4294967295))
   assert(value.c[0] == (u64(9223372036854775807) * u64(2) + u64(1)) && value.c[1] == u64(12345678901234567))
  }
 42
}
`)
	_, code, abnormal := buildAndRunOutput(t, "json_array_indexed", source.String(), "-fsanitize=address,undefined", "-DOAK_PORTABLE_INTRINSICS")
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	for _, fixture := range []struct {
		input string
		code  int
	}{
		{`{"a":[1,2,3,4,5,6],"b":[-1,2,3],"c":[1,2]}`, 3},                   // a sign on an unsigned element
		{`{"a":[1,2,3,4,5,6],"b":[1,2,3],"c":[1,18446744073709551616]}`, 4}, // one past the width
		{`{"a":[1,2,3,4,5,6],"b":[1,2,3],"c":[1,99999999999999999999]}`, 4}, // twenty digits
		{`{"a":[1,2,3,4,5,6],"b":[1,4294967296,3],"c":[1,2]}`, 4},           // one past u32
		{`{"a":[1,2,3,4,5,6],"b":[1,2,3],"c":[1,2,3]}`, 8},                  // too long
		{`{"a":[1,2,3,4,5,6],"b":[1,2],"c":[1,2]}`, 8},                      // too short
		{`{"a":[1,2,3,4,5,6],"b":[1,2,3],"c":[1,"2"]}`, 3},                  // a string element
		{`{"a":[1,2,3,4,5,6],"b":[1,2,3],"c":[1,2.5]}`, 3},                  // a fraction: the terminator is not structural
		{`{"a":[1,2,3,4,5,6],"b":[1,2,3],"c":[1,]}`, 2},                     // a trailing comma
		{`{"a":[1,2,3,4,5,6],"b":[1,2,3],"c":[1,[2]]}`, 3},                  // a nested array
	} {
		var errSource strings.Builder
		errSource.WriteString(`import(std)
json: tag = { name: string }
Wide: type = struct { a: [6]i64, b: [3]u32, c: [2]u64 }
main: (): i32 {
`)
		writeTextView(&errSource, "input", fixture.input)
		fmt.Fprintf(&errSource, "result: Result[Wide, JsonDecodeError] = decode[Wide, Json](input)\nresult ? | .Ok(value) => { assert(false) } | .Err(reason) => { assert(json_decode_error_code(reason) == u32(%d)) }\n42\n}\n", fixture.code)
		_, code, abnormal := buildAndRunOutput(t, "json_array_indexed_error", errSource.String(), "-fsanitize=address,undefined", "-DOAK_PORTABLE_INTRINSICS")
		if abnormal || code != 42 {
			t.Fatalf("%s: exit=(%d,%v), want code %d", fixture.input, code, abnormal, fixture.code)
		}
	}
}
