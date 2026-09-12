package compiler

import (
	"encoding/json"
	"fmt"
	"os"
	"strconv"
	"strings"
	"testing"
	"unicode/utf16"
	"unicode/utf8"
)

func TestE2EStdlibTextSmoke(t *testing.T) {
	code, abnormal := buildAndRun(t, "textsmoke", `
import(std)
main: (): i32 {
 input: [4]u8
 input[0] = u8(240)
 input[1] = u8(159)
 input[2] = u8(152)
 input[3] = u8(128)
 src: []u8 = view(&input)
 assert(utf8_validate(src))
 assert(text_result_value(utf8_count(src)) == u32(1))
 decoded: TextScalar = text_decoded(utf8_decode(src, u32(0)))
 assert(decoded.value == u32(128512) && decoded.next == u32(4))
 wide: [2]u16
 true ? {
  dst: [*]u16 = span(&wide)
  assert(text_result_value(utf8_to_utf16(dst, src)) == u32(2))
  assert(dst[0] == u16(55357) && dst[1] == u16(56832))
 }
 true ? {
  units: []u16 = view(&wide)
  out: [4]u8
  dst: [*]u8 = span(&out)
  assert(text_result_value(utf16_to_utf8(dst, units)) == u32(4))
  assert(dst[0] == u8(240) && dst[3] == u8(128))
 }
 assert(text_contains(src, src))
 assert(option_or(text_index_rune(src, u32(128512)), u32(99)) == u32(0))
 42
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

const textTestPrelude = `
import(std)
text_code: (result: Result[u32, TextError]): u32 = result ?
 | .Ok(value) => u32(0)
 | .Err(reason) => text_error_code(reason)
text_range: (result: Result[TextRange, TextError]): TextRange = result ?
 | .Ok(value) => value
 | .Err(reason) => TextRange { start: u32(4294967295), end: u32(4294967295) }
range_code: (result: Result[TextRange, TextError]): u32 = result ?
 | .Ok(value) => u32(0)
 | .Err(reason) => text_error_code(reason)
`

func writeTextView(src *strings.Builder, name string, value string) {
	fmt.Fprintf(src, "%s_data: [%d]u8\n", name, len(value))
	for i, b := range []byte(value) {
		fmt.Fprintf(src, "%s_data[%d] = u8(%d)\n", name, i, b)
	}
	fmt.Fprintf(src, "%s: []u8 = view(&%s_data)\n", name, name)
}

func runTextTest(t *testing.T, name string, src string) {
	t.Helper()
	code, abnormal := buildAndRun(t, name, src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EStdlibTextCodecs(t *testing.T) {
	var src strings.Builder
	src.WriteString(textTestPrelude + "main: (): i32 {\n")
	fixtures := []string{"", "A\x00z", "é", "世界", "😀", "\u007f\u0080\u07ff\u0800\ud7ff\ue000\uffff\U00010000\U0010ffff"}
	for _, value := range fixtures {
		src.WriteString("true ? {\n")
		writeTextView(&src, "input", value)
		runes := []rune(value)
		units := utf16.Encode(runes)
		fmt.Fprintf(&src, "wide_data: [%d]u16\nscalar_data: [%d]u32\n", len(units), len(runes))
		for i, v := range units {
			fmt.Fprintf(&src, "wide_data[%d] = u16(%d)\n", i, v)
		}
		for i, v := range runes {
			fmt.Fprintf(&src, "scalar_data[%d] = u32(%d)\n", i, v)
		}
		src.WriteString("wide: []u16 = view(&wide_data)\nscalars: []u32 = view(&scalar_data)\n")
		for _, in := range []struct {
			bits int
			name string
		}{{8, "input"}, {16, "wide"}, {32, "scalars"}} {
			fmt.Fprintf(&src, "assert(text_result_value(utf%d_count(%s)) == u32(%d))\n", in.bits, in.name, len(runes))
			for _, out := range []struct {
				bits   int
				values []uint32
			}{{8, bytesAsU32([]byte(value))}, {16, unitsAsU32(units)}, {32, runesAsU32(runes)}} {
				if in.bits == out.bits {
					continue
				}
				fmt.Fprintf(&src, "true ? {\nout_data: [%d]u%d\ndst: [*]u%d = span(&out_data)\nassert(text_result_value(utf%d_to_utf%d(dst, %s)) == u32(%d))\n", len(out.values), out.bits, out.bits, in.bits, out.bits, in.name, len(out.values))
				for i, v := range out.values {
					fmt.Fprintf(&src, "assert(dst[%d] == u%d(%d))\n", i, out.bits, v)
				}
				src.WriteString("}\n")
			}
		}
		src.WriteString("}\n")
	}
	// Exercise every Unicode scalar through both variable-width codecs.
	src.WriteString(`
 bytes: [4]u8
 wide: [2]u16
 value: u32 = 0
 while value <= u32(1114111) {
  unicode_is_scalar(value) ? {
   n8: u32 = 0
   n16: u32 = 0
   true ? {
    dst: [*]u8 = span(&bytes)
    n8 = text_result_value(utf8_encode(dst, u32(0), value))
   }
   true ? {
    dst: [*]u16 = span(&wide)
    n16 = text_result_value(utf16_encode(dst, u32(0), value))
   }
   true ? {
    v: []u8 = bytes[0:n8]
    decoded: TextScalar = text_decoded(utf8_decode(v, u32(0)))
    assert(decoded.value == value && decoded.next == n8 && is_valid_utf8(v))
   }
   true ? {
    v: []u16 = wide[0:n16]
    decoded: TextScalar = text_decoded(utf16_decode(v, u32(0)))
    assert(decoded.value == value && decoded.next == n16)
   }
  }
  value = value + u32(1)
 }
 42
}
`)
	runTextTest(t, "textcodecs", src.String())
}

func bytesAsU32(values []byte) []uint32 {
	out := make([]uint32, len(values))
	for i, v := range values {
		out[i] = uint32(v)
	}
	return out
}
func unitsAsU32(values []uint16) []uint32 {
	out := make([]uint32, len(values))
	for i, v := range values {
		out[i] = uint32(v)
	}
	return out
}
func runesAsU32(values []rune) []uint32 {
	out := make([]uint32, len(values))
	for i, v := range values {
		out[i] = uint32(v)
	}
	return out
}

func TestE2EStdlibTextInvalidEncoding(t *testing.T) {
	var src strings.Builder
	src.WriteString(textTestPrelude + "main: (): i32 {\n")
	invalid := []string{"\x80", "\xbf", "\xc0\x80", "\xc1\xbf", "\xc2", "\xc2A", "\xe0\x80\x80", "\xed\xa0\x80", "\xed\xbf\xbf", "\xe1\x80", "\xf0\x80\x80\x80", "\xf4\x90\x80\x80", "\xf5\x80\x80\x80", "\xf0\x90\x80", "\xff", "a\xff"}
	for _, value := range invalid {
		if utf8.ValidString(value) {
			t.Fatal("fixture should be invalid")
		}
		src.WriteString("true ? {\n")
		writeTextView(&src, "input", value)
		src.WriteString("out: [8]u16\ndst: [*]u16 = span(&out)\ni: u32 = 0\nwhile i < u32(8) { dst[i] = u16(90)\ni = i + u32(1) }\nassert(!utf8_validate(input) && !is_valid_utf8(input))\nassert(text_code(utf8_to_utf16(dst, input)) == u32(1))\ni = u32(0)\nwhile i < u32(8) { assert(dst[i] == u16(90))\ni = i + u32(1) }\n}\n")
	}
	src.WriteString(`
 data: [4]u8
 dst: [*]u8 = span(&data)
 bytes_fill(dst, u8(90))
 assert(text_code(utf8_encode(dst, u32(0), u32(55296))) == u32(2))
 assert(text_code(utf8_encode(dst, u32(0), u32(1114112))) == u32(2))
 assert(text_code(utf8_encode(dst, u32(4294967295), u32(65))) == u32(4))
 assert(text_code(utf8_encode(dst, u32(1), u32(128512))) == u32(4))
 wide: [1]u16
 wide[0] = u16(55296)
 v: []u16 = view(&wide)
 assert(!utf16_validate(v))
 assert(text_code(utf16_to_utf8(dst, v)) == u32(1))
 scalars: [1]u32
 scalars[0] = u32(4294967295)
 s: []u32 = view(&scalars)
 assert(!utf32_validate(s))
 assert(text_code(utf32_to_utf8(dst, s)) == u32(1))
 assert(dst[0] == u8(90) && dst[1] == u8(90) && dst[2] == u8(90) && dst[3] == u8(90))
 42
}
`)
	runTextTest(t, "textinvalid", src.String())
}

func TestE2EStdlibTextSearch(t *testing.T) {
	var src strings.Builder
	src.WriteString(textTestPrelude + "main: (): i32 {\n")
	for _, haystack := range []string{"", "abababa", "é😀é", "a\x00b", "hello"} {
		for _, needle := range []string{"", "a", "aba", "é", "😀", "\x00", "missing"} {
			src.WriteString("true ? {\n")
			writeTextView(&src, "input", haystack)
			writeTextView(&src, "needle", needle)
			for _, find := range []struct {
				name string
				want int
			}{{"text_index", strings.Index(haystack, needle)}, {"text_last_index", strings.LastIndex(haystack, needle)}} {
				want := uint32(find.want)
				fmt.Fprintf(&src, "assert(option_or(%s(input, needle), u32(4294967295)) == u32(%d))\n", find.name, want)
			}
			fmt.Fprintf(&src, "assert(text_contains(input, needle) == %t)\nassert(text_has_prefix(input, needle) == %t)\nassert(text_has_suffix(input, needle) == %t)\nassert(text_equal(input, needle) == %t)\nassert(text_compare(input, needle) == i32(%d))\n", strings.Contains(haystack, needle), strings.HasPrefix(haystack, needle), strings.HasSuffix(haystack, needle), haystack == needle, strings.Compare(haystack, needle))
			src.WriteString("}\n")
		}
	}
	src.WriteString("42\n}\n")
	runTextTest(t, "textsearch", strings.ReplaceAll(src.String(), "i32(-1)", "-i32(1)"))
}

func TestE2EStdlibTextUnicodeCase(t *testing.T) {
	fixtures := []struct {
		input, lower, upper, fold string
	}{
		{"Straße", "straße", "STRASSE", "strasse"},
		{"İ", "i\u0307", "İ", "i\u0307"},
		{"ΟΣ", "ος", "ΟΣ", "οσ"},
		{"ΟΣ\u0301", "ος\u0301", "ΟΣ\u0301", "οσ\u0301"},
		{"ΟΣ\u0301Α", "οσ\u0301α", "ΟΣ\u0301Α", "οσ\u0301α"},
		{"ﬃ", "ﬃ", "FFI", "ffi"},
		{"\U00010400", "\U00010428", "\U00010400", "\U00010428"},
		{"A\x00z", "a\x00z", "A\x00Z", "a\x00z"},
		{"", "", "", ""},
	}
	var src strings.Builder
	src.WriteString(textTestPrelude + "main: (): i32 {\n")
	for _, fixture := range fixtures {
		for mode, expected := range []string{fixture.lower, fixture.upper, fixture.fold} {
			src.WriteString("true ? {\n")
			writeTextView(&src, "input", fixture.input)
			fmt.Fprintf(&src, "output: [%d]u8\ntrue ? {\ndst: [*]u8 = span(&output)\nassert(text_result_value(text_case_into(dst, input, u32(%d))) == u32(%d))\n", len(expected)+1, mode, len(expected))
			for i, b := range []byte(expected) {
				fmt.Fprintf(&src, "assert(dst[%d] == u8(%d))\n", i, b)
			}
			fmt.Fprintf(&src, "assert(dst[%d] == u8(0))\n}\n", len(expected))
			if len(expected) > 0 {
				fmt.Fprintf(&src, "true ? {\nsmall: [%d]u8\ndst: [*]u8 = span(&small)\nbytes_fill(dst, u8(90))\nassert(text_code(text_case_into(dst, input, u32(%d))) == u32(4))\ni: u32 = 0\nwhile i < len(dst) { assert(dst[i] == u8(90))\ni = i + u32(1) }\n}\n", len(expected)-1, mode)
			}
			writeTextView(&src, "folded", fixture.fold)
			src.WriteString("assert(text_equal_fold(input, folded))\n}\n")
		}
	}
	src.WriteString("42\n}\n")
	runTextTest(t, "textcase", src.String())
}

func TestE2EStdlibTextRangesAndWrites(t *testing.T) {
	var src strings.Builder
	src.WriteString(textTestPrelude + "main: (): i32 {\n")
	writeTextView(&src, "input", "\u2003é,a,,😀,\u00a0")
	writeTextView(&src, "separator", ",")
	writeTextView(&src, "cutset", "\u2003\u00a0")
	writeTextView(&src, "replacement", "--")
	src.WriteString(`
 trimmed: TextRange = text_trim_space(input)
 cut: TextRange = text_trim(input, cutset)
 assert(trimmed.start == u32(3) && trimmed.end == u32(14))
 assert(cut.start == trimmed.start && cut.end == trimmed.end)
 assert(range_code(text_slice_range(input, u32(1), u32(3))) == u32(3))
 assert(range_code(text_slice_range(input, u32(3), u32(5))) == u32(0))
 state: [1]TextSplitCursor
 cursor: [*]TextSplitCursor = span(&state)
 parts: [5]TextRange
 true ? {
  spans: [*]TextRange = span(&parts)
  i: u32 = 0
  while i < u32(5) { spans[i] = text_range(text_split_next(cursor, input, separator))
   i = i + u32(1)
  }
  assert(spans[0].start == u32(0) && spans[0].end == u32(5))
  assert(spans[2].start == u32(8) && spans[2].end == u32(8))
  assert(range_code(text_split_next(cursor, input, separator)) == u32(7))
 }
 true ? {
  spans: []TextRange = view(&parts)
  out: [32]u8
  dst: [*]u8 = span(&out)
  assert(text_result_value(text_join(dst, input, spans, separator)) == len(input))
  i: u32 = 0
  while i < len(input) { assert(dst[i] == input[i])
   i = i + u32(1)
  }
  assert(text_result_value(text_replace(dst, input, separator, replacement)) == len(input) + u32(4))
 }
 true ? {
  tiny: [1]u8
  dst: [*]u8 = span(&tiny)
  dst[0] = u8(90)
  assert(text_code(text_copy(dst, input)) == u32(4))
  assert(text_code(text_repeat(dst, input, u32(4294967295))) == u32(5))
  assert(text_code(text_repeat(dst, input, u32(2))) == u32(4))
  assert(text_code(text_replace(dst, input, separator, replacement)) == u32(4))
  assert(dst[0] == u8(90))
 }
 42
}
`)
	// UTF-8 byte offsets, independently derived from the fixture.
	s := "\u2003é,a,,😀,\u00a0"
	trimEnd := len(strings.TrimRight(s, "\u00a0"))
	source := strings.Replace(src.String(), "trimmed.end == u32(14)", fmt.Sprintf("trimmed.end == u32(%d)", trimEnd), 1)
	runTextTest(t, "textranges", source)
}

func TestE2EStdlibTextBuilder(t *testing.T) {
	var src strings.Builder
	src.WriteString(textTestPrelude + "main: (): i32 {\n")
	writeTextView(&src, "prefix", "id=")
	writeTextView(&src, "bad", "\xff")
	src.WriteString(`
 data: [27]u8
 dst: [*]u8 = span(&data)
 maximum: u64 = (u64(1) << u64(63)) | ((u64(1) << u64(63)) - u64(1))
 b: TextBuilder = text_builder().append_text(dst, prefix).append_u64(dst, maximum).append_rune(dst, u32(128512))
 assert(text_result_value(b.finish_text()) == u32(27))
 assert(dst[0] == u8(105) && dst[3] == u8(49) && dst[22] == u8(53) && dst[23] == u8(240) && dst[26] == u8(128))
 failed: TextBuilder = b.append_rune(dst, u32(65)).append_text(dst, bad)
 assert(failed.length == u32(27) && text_code(failed.finish_text()) == u32(4))
 other: [4]u8
 out: [*]u8 = span(&other)
 bytes_fill(out, u8(90))
 invalid: TextBuilder = text_builder().append_text(out, bad).append_rune(out, u32(65))
 assert(invalid.length == u32(0) && text_code(invalid.finish_text()) == u32(1))
 assert(out[0] == u8(90) && out[3] == u8(90))
 zero: TextBuilder = text_builder().append_u64(out, u64(0))
 assert(zero.length == u32(1) && out[0] == u8(48))
 42
}
`)
	source := strings.Replace(src.String(), "maximum: u64 = (u64(1) << u64(63)) | ((u64(1) << u64(63)) - u64(1))", "maximum: u64 = ((u64(1) << u64(63)) | ((u64(1) << u64(63)) - u64(1)))", 1)
	output, err := New().WithSource("textbuilder.oak", source).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "OAK_UNSUPPORTED", "/* match expression */"} {
		if strings.Contains(output, forbidden) {
			t.Fatalf("unexpected %s in generated text code", forbidden)
		}
	}
	runTextTest(t, "textbuilder", source)
}

func TestE2EStdlibTextExample(t *testing.T) {
	skipInShort(t)
	for _, path := range []string{"stdlib_strings.oak", "strings/strings.oak", "strings/encoding/ascii.oak", "strings/encoding/utf8.oak", "strings/encoding/utf16.oak", "strings/encoding/utf32.oak", "strings/logascii.oak", "strings_encoding.oak"} {
		source, err := os.ReadFile("../examples/" + path)
		if err != nil {
			t.Fatal(err)
		}
		runTextTest(t, "textexample", string(source))
	}
}

func TestE2EStdlibTextLiterals(t *testing.T) {
	runTextTest(t, "textliterals", `
import(std)
main: (): i32 {
 __oak_text_literal_0: u32 = 42
 src: []u8 = text_literal("hé😀")
 again: []u8 = text_literal("hé😀")
 empty: []u8 = text_literal("")
 assert(len(src) == u32(7) && len(empty) == u32(0))
 assert(text_equal(src, again))
 assert(text_result_value(utf8_count(src)) == u32(3))
 assert(__oak_text_literal_0 == u32(42))
 42
}
`)
	for _, source := range []string{
		"import(std)\nmain: (): i32 {\ns: string = \"x\"\nv: []u8 = text_literal(s)\n0\n}",
		"import(std)\nmain: (): i32 {\nv: []u8 = text_literal()\n0\n}",
		"import(std)\ntext_literal: (): u32 = u32(0)\nmain: (): i32 = 0",
	} {
		if _, err := New().WithSource("badtextliteral.oak", source).EmitC().Get(); err == nil {
			t.Fatal("invalid text literal call must be rejected")
		}
	}
}

func TestE2EStdlibTextSplitEdgesAndParse(t *testing.T) {
	runTextTest(t, "textedges", textTestPrelude+`
parsed_value: (result: Result[u64, TextParseError]): u64 = result ? | .Ok(value) => value | .Err(reason) => u64(0)
parse_failed: (result: Result[u64, TextParseError]): Bool = result ? | .Ok(value) => false | .Err(reason) => true
main: (): i32 {
 empty: []u8 = text_literal("")
 comma: []u8 = text_literal(",")
 input: []u8 = text_literal(",a,")
 bad: []u8 = text_literal("é")
 parts: [3]TextRange
 true ? {
  dst: [*]TextRange = span(&parts)
  assert(text_result_value(text_split(dst, input, comma)) == u32(3))
  assert(dst[0].start == u32(0) && dst[0].end == u32(0))
  assert(dst[1].start == u32(1) && dst[1].end == u32(2))
  assert(dst[2].start == u32(3) && dst[2].end == u32(3))
  assert(text_code(text_split(dst, input, empty)) == u32(6))
  assert(dst[1].start == u32(1) && dst[1].end == u32(2))
  assert(text_result_value(text_split(dst, empty, comma)) == u32(1))
 }
 true ? {
  whole: [*]TextRange = span(&parts)
  dst: [*]TextRange = whole[0:2]
  assert(text_code(text_split(dst, input, comma)) == u32(4))
  assert(dst[0].start == u32(0) && dst[0].end == u32(0))
 }
 out: [2]u8
 dst: [*]u8 = span(&out)
 bytes_fill(dst, u8(90))
 assert(text_code(utf8_to_ascii(dst, bad)) == u32(1))
 assert(text_result_value(text_repeat(dst, empty, u32(4294967295))) == u32(0))
 assert(text_result_value(text_repeat(dst, comma, u32(0))) == u32(0))
 assert(dst[0] == u8(90) && dst[1] == u8(90))
 previous: TextScalar = text_decoded(utf8_decode_previous(bad, u32(2)))
 assert(previous.value == u32(233) && previous.next == u32(0))
 assert(!text_decode_ok(utf8_decode_previous(bad, u32(1))))
 fields: []u8 = text_literal("  one　two  ")
 state: [1]TextSplitCursor
 cursor: [*]TextSplitCursor = span(&state)
 first: TextRange = text_range(text_fields_next(cursor, fields))
 second: TextRange = text_range(text_fields_next(cursor, fields))
 assert(first.start == u32(2) && first.end == u32(5))
 assert(second.start == u32(8) && second.end == u32(11))
 assert(range_code(text_fields_next(cursor, fields)) == u32(7))
 assert(parse_failed(text_parse_u64(text_literal("18446744073709551616"), u32(10))))
 assert(parse_failed(text_parse_u64(text_literal("-1"), u32(10))))
 assert(parse_failed(text_parse_u64(empty, u32(10))))
 assert(parse_failed(text_parse_u64(comma, u32(1))))
 maximum: u64 = ((u64(1) << u64(63)) | ((u64(1) << u64(63)) - u64(1)))
 assert(parsed_value(text_parse_u64(text_literal("18446744073709551615"), u32(10))) == maximum)
 assert(parsed_value(text_parse_u64(text_literal("Ff"), u32(16))) == u64(255))
 assert(parsed_value(text_parse_u64(text_literal("z"), u32(36))) == u64(35))
 42
}
`)
}

func TestE2EStdlibTextUnicodeTables(t *testing.T) {
	data, err := os.ReadFile("../stdlib/unicode17.json")
	if err != nil {
		t.Fatal(err)
	}
	var fixture struct {
		Version string                         `json:"version"`
		Maps    map[string]map[string][]uint32 `json:"maps"`
	}
	if err := json.Unmarshal(data, &fixture); err != nil {
		t.Fatal(err)
	}
	if fixture.Version != "17.0.0" {
		t.Fatal("unexpected Unicode version")
	}
	var src strings.Builder
	src.WriteString("import(std)\nmain: (): i32 {\n")
	for _, name := range []string{"lower", "upper", "fold"} {
		mappings := map[uint32][]uint32{}
		for key, values := range fixture.Maps[name] {
			cp, err := strconv.ParseUint(key, 10, 32)
			if err != nil {
				t.Fatal(err)
			}
			mappings[uint32(cp)] = values
		}
		var checksum, count uint64
		for cp := uint32(0); cp <= 0x10ffff; cp++ {
			if cp >= 0xd800 && cp <= 0xdfff {
				continue
			}
			values, ok := mappings[cp]
			if !ok {
				values = []uint32{cp}
			}
			count += uint64(len(values))
			for i, value := range values {
				checksum += uint64(cp+1) * uint64(value+1) * uint64(i+1)
			}
		}
		fmt.Fprintf(&src, "true ? {\ncp: u32 = 0\nchecksum: u64 = 0\ncount: u64 = 0\nwhile cp <= u32(1114111) {\nunicode_is_scalar(cp) ? {\nmapping: UnicodeMapping = unicode_%s(cp)\ncount = count + u64(mapping.count)\ni: u32 = 0\nwhile i < mapping.count {\nvalue: u32 = unicode_mapping_at(mapping, i)\nassert(unicode_is_scalar(value))\nchecksum = checksum + u64(cp + u32(1)) * u64(value + u32(1)) * u64(i + u32(1))\ni = i + u32(1)\n}\n}\ncp = cp + u32(1)\n}\nassert(checksum == u64(%d) && count == u64(%d))\n}\n", name, checksum, count)
	}
	src.WriteString("42\n}\n")
	runTextTest(t, "texttables", src.String())
}

func TestE2EStdlibTextBorrowedSlices(t *testing.T) {
	runTextTest(t, "textviews", `
import(std)
low_calls: u32 = 0
high_calls: u32 = 0
slice_low: (): u32 { low_calls = low_calls + u32(1)
 u32(1)
}
slice_high: (): u32 { high_calls = high_calls + u32(1)
 u32(4)
}
main: (): i32 {
 src: []u8 = text_literal("hello")
 middle: []u8 = src[slice_low():slice_high()]
 assert(low_calls == u32(1) && high_calls == u32(1))
 assert(text_equal(middle, text_literal("ell")))
 nested: []u8 = middle[1:]
 assert(text_equal(nested, text_literal("ll")))
 empty: []u8 = src[5:5]
 assert(len(empty) == u32(0))
 data: [4]u8
 true ? {
  whole: [*]u8 = span(&data)
  writable: [*]u8 = whole[1:3]
  writable[0] = u8(42)
  writable[1] = u8(7)
 }
 assert(data[0] == u8(0) && data[1] == u8(42) && data[2] == u8(7) && data[3] == u8(0))
 42
}
`)
	for _, bounds := range [][2]uint32{{2, 1}, {0, 4}, {^uint32(0), ^uint32(0)}} {
		source := fmt.Sprintf("import(std)\nmain: (): i32 {\nsrc: []u8 = text_literal(\"abc\")\nlow: u32 = %d\nhigh: u32 = %d\npart: []u8 = src[low:high]\n0\n}", bounds[0], bounds[1])
		_, abnormal := buildAndRun(t, "badtextview", source)
		if !abnormal {
			t.Fatal("invalid borrowed slice must trap")
		}
	}
}
