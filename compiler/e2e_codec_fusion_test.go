package compiler

import (
	"strings"
	"testing"
)

// One bounds check per record (docs/spec/71-codecs.md section 4a): a
// derived record encoder measures once and checks the destination once at
// its checked entry, then writes every field through the unchecked form.
// No field writer inside the unchecked body measures again or checks
// capacity again, at any nesting depth. The generated C is the witness.
func TestDerivedJsonOneBoundsCheckPerRecord(t *testing.T) {
	output, err := New().WithSource("derived.oak", derivedJsonPrelude+"main: (): i32 {\n data: [128]u8\n dst: [*]u8 = span(&data)\n assert(json_result_ok(encode[Record, Json](make_record(), dst)))\n 42\n}\n").EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, name := range []string{"Record", "Point"} {
		unchecked := cFunctionBody(t, output, "oak___oak_json_write_unchecked_"+name)
		for _, forbidden := range []string{"bytes_range_fits", "__oak_json_encoded_size_", "oak___oak_json_write_" + name + "(", "oak_assert("} {
			if strings.Contains(unchecked, forbidden) {
				t.Fatalf("unchecked writer of %s contains %q:\n%s", name, forbidden, unchecked)
			}
		}
		checked := cFunctionBody(t, output, "oak___oak_json_write_"+name)
		if got := strings.Count(checked, "oak_bytes_range_fits("); got != 1 {
			t.Fatalf("checked writer of %s has %d capacity checks, want 1:\n%s", name, got, checked)
		}
		if got := strings.Count(checked, "oak___oak_json_encoded_size_"+name+"("); got != 1 {
			t.Fatalf("checked writer of %s measures %d times, want 1:\n%s", name, got, checked)
		}
	}
	// The nested record's field write is the unchecked call.
	outer := cFunctionBody(t, output, "oak___oak_json_write_unchecked_Record")
	if !strings.Contains(outer, "oak___oak_json_write_unchecked_Point(") {
		t.Fatalf("Record's writer does not call Point's unchecked writer:\n%s", outer)
	}
}

// cFunctionBody extracts the C definition of a named function (from its
// signature line to the closing brace at column 0).
func cFunctionBody(t *testing.T, output, name string) string {
	t.Helper()
	marker := " " + name + "( "
	start := -1
	for from := 0; ; {
		i := strings.Index(output[from:], marker)
		if i < 0 {
			break
		}
		at := from + i
		lineEnd := strings.IndexByte(output[at:], '\n')
		if lineEnd >= 0 && strings.Contains(output[at:at+lineEnd], "{") {
			start = at
			break
		}
		from = at + len(marker)
	}
	if start < 0 {
		t.Fatalf("no definition of %s in generated C:\n%s", name, output)
	}
	end := strings.Index(output[start:], "\n}\n")
	if end < 0 {
		t.Fatalf("unterminated definition of %s", name)
	}
	return output[start : start+end+3]
}

// The fused measuring pass agrees with the pre-fusion oracle on every
// input: ASCII, escapes, long runs, valid multibyte UTF-8, invalid UTF-8
// at every position class, and mixes — in C and in the interpreter.
func TestE2EJsonStringSizeFusionOracle(t *testing.T) {
	var source strings.Builder
	source.WriteString(`import(std)
same: (a: Result[u32, JsonError], b: Result[u32, JsonError]): Bool = a ?
 | .Ok(x) => { b ? | .Ok(y) => x == y | .Err(e) => false }
 | .Err(e) => { b ? | .Ok(y) => false | .Err(f) => json_error_code(e) == json_error_code(f) }
check: (src: []u8): Bool = same(json_string_encode_size(src), json_string_encode_size_reference(src))
main: (): i32 {
`)
	fixtures := []string{
		"", "a", "hello", "\"quoted\"", "back\\slash", "tab\there", "\x01\x1f",
		strings.Repeat("x", 15), strings.Repeat("x", 16), strings.Repeat("x", 17), strings.Repeat("x", 33) + "\"",
		"caf\xc3\xa9", strings.Repeat("a", 16) + "\xc3\xa9", "\xe2\x82\xac" + strings.Repeat("b", 20), "\xf0\x9f\x98\x80",
		"\xff", "\xc3", "a\xc3", strings.Repeat("a", 16) + "\xc3", strings.Repeat("a", 15) + "\xc3\xa9", "\xed\xa0\x80", "\xc0\xaf",
		strings.Repeat("a", 16) + "\x80" + strings.Repeat("b", 16), "\"" + "\xff", "ok\n\xe2\x82",
	}
	for i, fixture := range fixtures {
		source.WriteString("true ? {\n")
		writeTextView(&source, "input", fixture)
		source.WriteString("assert(check(input))\n}\n")
		_ = i
	}
	source.WriteString(" 42\n}\n")
	code, abnormal := buildAndRun(t, "json_size_fusion", source.String())
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	if interpreted := interpretChecked(t, source.String()); interpreted != 42 {
		t.Fatalf("interpreter returned %d", interpreted)
	}
}

// The fused scan reports the run end the unfused scan reports, plus the
// ASCII verdict, and encoding keeps its atomic contract through the
// unchecked writers: a destination too small leaves every byte untouched.
func TestE2EJsonScanAndAtomicWrite(t *testing.T) {
	var source strings.Builder
	source.WriteString(`import(std)
main: (): i32 {
`)
	writeTextView(&source, "ascii", strings.Repeat("a", 20)+"\"tail")
	writeTextView(&source, "wide", strings.Repeat("a", 20)+"\xc3\xa9\"tail")
	source.WriteString(`
 a: JsonRun = json_string_scan(ascii, u32(0))
 assert(a.end == json_string_run(ascii, u32(0)) && a.end == u32(20) && a.ascii)
 w: JsonRun = json_string_scan(wide, u32(0))
 assert(w.end == json_string_run(wide, u32(0)) && w.end == u32(22) && !w.ascii)
 after: JsonRun = json_string_scan(wide, u32(23))
 assert(after.end == len(wide) && after.ascii)
 small: [8]u8
 dst: [*]u8 = span(&small)
 dst[0] = u8(77)
 dst[7] = u8(88)
 assert(!json_result_ok(json_string_encode_at(dst, u32(0), wide)))
 assert(dst[0] == u8(77) && dst[7] == u8(88))
 assert(!json_result_ok(json_i64_encode_at(dst, u32(6), i64(-123))))
 assert(dst[7] == u8(88))
 assert(json_result_value(json_i64_encode_at(dst, u32(1), i64(-123))) == u32(4))
 assert(dst[1] == u8(45) && dst[2] == u8(49) && dst[4] == u8(51))
 42
}
`)
	code, abnormal := buildAndRun(t, "json_scan_atomic", source.String())
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	if interpreted := interpretChecked(t, source.String()); interpreted != 42 {
		t.Fatalf("interpreter returned %d", interpreted)
	}
}
