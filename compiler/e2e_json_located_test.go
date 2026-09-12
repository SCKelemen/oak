package compiler

import (
	"fmt"
	"strings"
	"testing"
)

// decode_located[T, Json] (docs/spec/71-codecs.md section 13, "Positions"):
// the same document read as decode[T, Json], with every failure carrying
// the byte offset of the offending token — a value's first byte, an
// unknown or duplicate key's opening quote, the byte where a separator or
// colon was expected, the first ill-formed UTF-8 byte. decode itself is
// unchanged and must report the same error code.
func TestE2EJsonDecodeLocated(t *testing.T) {
	type fixture struct {
		input string
		code  int // 0 = Ok
		at    int
	}
	// Byte offsets counted in the fixture strings below (ASCII, one byte
	// per character, except the deliberate 0xFF).
	fixtures := []fixture{
		{`{"id": 1, "active": true, "samples": [1, 2]}`, 0, 0},
		{`{"id": x, "active": true, "samples": [1, 2]}`, 2, 7},                    // InvalidSyntax at the value
		{`{"id": -1, "active": true, "samples": [1, 2]}`, 3, 7},                   // TypeMismatch: unsigned target, minus at the value
		{`{"id": 99999999999999999999, "active": true, "samples": [1, 2]}`, 4, 7}, // NumericOverflow at the value
		{`{"id": 1, "active": "yes", "samples": [1, 2]}`, 3, 20},                  // TypeMismatch: Bool target, string at the value
		{`{"id": 1, "nope": 2, "active": true, "samples": [1, 2]}`, 7, 10},        // UnknownField at the key
		{`{"id": 1, "id": 2, "active": true, "samples": [1, 2]}`, 6, 10},          // DuplicateField at the key
		{`{"id": 1, "active": true}`, 5, 25},                                      // MissingField at the end of the object
		{`{"id": 1 "active": true, "samples": [1, 2]}`, 2, 9},                     // InvalidSyntax where the separator was expected
		{`{"id" 1, "active": true, "samples": [1, 2]}`, 2, 6},                     // InvalidSyntax where the colon was expected
		{`{"id": 1, "active": true, "samples": [1, 2]} x`, 2, 45},                 // InvalidSyntax: trailing content
		{`{"id": 1, "active": true, "samples": [1]}`, 8, 39},                      // LengthMismatch at the closing bracket
		{`{"id": 1, "active": true, "samples": [1, 2, 3]}`, 8, 44},                // LengthMismatch at the third element
		{`{"id": 1, "active": true, "samples": 7}`, 3, 37},                        // TypeMismatch: array target, number at the value
		{"{\"id\": 1, \"active\": true, \"z\xff\": 1}", 1, 28},                    // InvalidEncoding at the ill-formed byte, over the unknown key
		{`  {"id": 1, "active": true, "samples": [1, 2]}  `, 0, 0},
	}
	var source strings.Builder
	source.WriteString("import(std)\nLocated: type = struct { id: u64, active: Bool, samples: [2]u32 }\n")
	for i, f := range fixtures {
		fmt.Fprintf(&source, "case_%d: (): Bool {\n", i)
		fmt.Fprintf(&source, "  data: [%d]u8 = [", len(f.input))
		for j := 0; j < len(f.input); j++ {
			if j > 0 {
				source.WriteString(", ")
			}
			fmt.Fprintf(&source, "u8(%d)", f.input[j])
		}
		source.WriteString("]\n  input: []u8 = view(&data)\n")
		source.WriteString("  located: Result[Located, JsonFault] = decode_located[Located, Json](input)\n")
		source.WriteString("  plain: Result[Located, JsonDecodeError] = decode[Located, Json](input)\n")
		if f.code == 0 {
			source.WriteString("  ok_located: Bool = located ? | .Ok(v) => v.id == u64(1) && v.active && v.samples[1] == u32(2) | .Err(fault) => false\n")
			source.WriteString("  ok_plain: Bool = plain ? | .Ok(v) => v.id == u64(1) | .Err(reason) => false\n")
		} else {
			fmt.Fprintf(&source, "  ok_located: Bool = located ? | .Ok(v) => false | .Err(fault) => json_decode_error_code(fault.error) == u32(%d) && fault.at == u32(%d)\n", f.code, f.at)
			fmt.Fprintf(&source, "  ok_plain: Bool = plain ? | .Ok(v) => false | .Err(reason) => json_decode_error_code(reason) == u32(%d)\n", f.code)
		}
		source.WriteString("  ok_located && ok_plain\n}\n")
	}
	// The exit code names the first failing case (100 + its index).
	source.WriteString("main: (): i32 {\n  failed: i32 = 42\n")
	for i := len(fixtures) - 1; i >= 0; i-- {
		fmt.Fprintf(&source, "  !case_%d() ? { failed = %d }\n", i, 100+i)
	}
	source.WriteString("  failed\n}\n")
	_, code, abnormal := buildAndRunOutput(t, "json_located", source.String(), "-fsanitize=address,undefined")
	if abnormal || code != 42 {
		if code >= 100 && code-100 < len(fixtures) {
			t.Fatalf("case %d failed: %q (want code %d at %d)", code-100, fixtures[code-100].input, fixtures[code-100].code, fixtures[code-100].at)
		}
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
