package compiler

import (
	"fmt"
	"strings"
	"testing"
)

// The encoding package (stdlib/encoding.oak): RFC 4648 §10 vectors for
// base64 and base32 in every alphabet, padded and unpadded, hex vectors,
// percent-encoding cases, and the strict rejections.

// encodingVector emits Oak that encodes `input` with `call` (a format with
// one %s for the destination span) and asserts the exact output, then
// decodes the output with `decode` and asserts the input comes back.
func encodingVector(src *strings.Builder, n int, input, expected, encodeCall, decodeCall string) {
	fmt.Fprintf(src, "true ? {\n")
	fmt.Fprintf(src, "  in%d: [%d]u8\n", n, max(len(input), 1))
	for i, b := range []byte(input) {
		fmt.Fprintf(src, "  in%d[%d] = u8(%d)\n", n, i, b)
	}
	fmt.Fprintf(src, "  whole: []u8 = view(&in%d)\n  src: []u8 = whole[u32(0):u32(%d)]\n", n, len(input))
	fmt.Fprintf(src, "  out: [%d]u8\n  back: [%d]u8\n", max(len(expected), 1), max(len(input), 1))
	fmt.Fprintf(src, "  true ? {\n    dst: [*]u8 = span(&out)\n    assert(encoding_value(%s) == u32(%d))\n", fmt.Sprintf(encodeCall, "dst"), len(expected))
	for i, b := range []byte(expected) {
		fmt.Fprintf(src, "    assert(dst[%d] == u8(%d))\n", i, b)
	}
	fmt.Fprintf(src, "  }\n  true ? {\n    all: []u8 = view(&out)\n    enc: []u8 = all[u32(0):u32(%d)]\n    bdst: [*]u8 = span(&back)\n    assert(encoding_value(%s) == u32(%d))\n", len(expected), fmt.Sprintf(decodeCall, "bdst"), len(input))
	for i, b := range []byte(input) {
		fmt.Fprintf(src, "    assert(bdst[%d] == u8(%d))\n", i, b)
	}
	fmt.Fprintf(src, "  }\n}\n")
}

func TestE2EStdlibEncodingVectors(t *testing.T) {
	var src strings.Builder
	src.WriteString("import(std)\nmain: (): i32 {\n")
	n := 0
	// RFC 4648 §10.
	base64 := [][2]string{{"", ""}, {"f", "Zg=="}, {"fo", "Zm8="}, {"foo", "Zm9v"}, {"foob", "Zm9vYg=="}, {"fooba", "Zm9vYmE="}, {"foobar", "Zm9vYmFy"}}
	for _, v := range base64 {
		encodingVector(&src, n, v[0], v[1], "base64_encode(%s, src, false, true)", "base64_decode(%s, enc, false)")
		n++
		encodingVector(&src, n, v[0], strings.TrimRight(v[1], "="), "base64_encode(%s, src, false, false)", "base64_decode(%s, enc, false)")
		n++
	}
	// URL alphabet: bytes that produce '+' and '/' in the standard alphabet.
	encodingVector(&src, n, "\xfb\xff\xbf", "-_-_", "base64_encode(%s, src, true, true)", "base64_decode(%s, enc, true)")
	n++
	encodingVector(&src, n, "\xfb\xff\xbf", "+/+/", "base64_encode(%s, src, false, true)", "base64_decode(%s, enc, false)")
	n++
	base32 := [][2]string{{"", ""}, {"f", "MY======"}, {"fo", "MZXQ===="}, {"foo", "MZXW6==="}, {"foob", "MZXW6YQ="}, {"fooba", "MZXW6YTB"}, {"foobar", "MZXW6YTBOI======"}}
	for _, v := range base32 {
		encodingVector(&src, n, v[0], v[1], "base32_encode(%s, src, false, true)", "base32_decode(%s, enc, false)")
		n++
		encodingVector(&src, n, v[0], strings.TrimRight(v[1], "="), "base32_encode(%s, src, false, false)", "base32_decode(%s, enc, false)")
		n++
	}
	base32hex := [][2]string{{"", ""}, {"f", "CO======"}, {"fo", "CPNG===="}, {"foo", "CPNMU==="}, {"foob", "CPNMUOG="}, {"fooba", "CPNMUOJ1"}, {"foobar", "CPNMUOJ1E8======"}}
	for _, v := range base32hex {
		encodingVector(&src, n, v[0], v[1], "base32_encode(%s, src, true, true)", "base32_decode(%s, enc, true)")
		n++
	}
	hex := [][2]string{{"", ""}, {"\x00\xff\x10", "00ff10"}, {"foobar", "666f6f626172"}}
	for _, v := range hex {
		encodingVector(&src, n, v[0], v[1], "hex_encode(%s, src, false)", "hex_decode(%s, enc)")
		n++
		encodingVector(&src, n, v[0], strings.ToUpper(v[1]), "hex_encode(%s, src, true)", "hex_decode(%s, enc)")
		n++
	}
	// Percent-encoding: unreserved kept, everything else escaped uppercase;
	// a kept set passes '/' through; '+' decodes as space only when asked.
	encodingVector(&src, n, "a b/c~\xe9", "a%20b%2Fc~%E9", "percent_encode(%s, src, text_literal(\"\"))", "percent_decode(%s, enc, false)")
	n++
	src.WriteString("true ? {\n  out: [16]u8\n  keep: [1]u8\n  keep[0] = u8(47)\n  dst: [*]u8 = span(&out)\n  assert(encoding_value(percent_encode(dst, text_literal(\"a b/c\"), view(&keep))) == u32(7))\n  assert(dst[1] == u8(37) && dst[2] == u8(50) && dst[3] == u8(48) && dst[4] == u8(98) && dst[5] == u8(47))\n}\n")
	src.WriteString("true ? {\n  out: [8]u8\n  dst: [*]u8 = span(&out)\n  assert(encoding_value(percent_decode(dst, text_literal(\"a+b%2Bc\"), true)) == u32(5))\n  assert(dst[1] == u8(32) && dst[3] == u8(43))\n  assert(encoding_value(percent_decode(dst, text_literal(\"a+b\"), false)) == u32(3))\n  assert(dst[1] == u8(43))\n}\n")
	src.WriteString("42\n}\n")
	code, abnormal := buildAndRun(t, "encoding_vectors", src.String())
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)\n%s", code, abnormal, src.String())
	}
}

func TestE2EStdlibEncodingRejections(t *testing.T) {
	src := `
import(std)
failure: (result: Result[u32, EncodingError]): u32 = encoding_failure(result)
main: (): i32 {
  out: [8]u8
  dst: [*]u8 = span(&out)
  dst[0] = u8(7)
  // 1 InvalidCharacter, 2 InvalidLength, 3 InvalidPadding, 4 NonCanonical, 5 DestinationTooSmall, 6 SizeOverflow
  assert(failure(base64_decode(dst, text_literal("Zm9v*mFy"), false)) == u32(1))
  assert(failure(base64_decode(dst, text_literal("Zm9vY"), false)) == u32(2))
  assert(failure(base64_decode(dst, text_literal("Zm9v="), false)) == u32(3))
  assert(failure(base64_decode(dst, text_literal("Zg=x"), false)) == u32(3))
  assert(failure(base64_decode(dst, text_literal("Zh=="), false)) == u32(4))
  assert(failure(base64_decode(dst, text_literal("Zm9="), false)) == u32(4))
  assert(failure(base64_decode(dst, text_literal("-_-_"), false)) == u32(1))
  assert(failure(base64_decode(dst, text_literal("+/+/"), true)) == u32(1))
  assert(failure(base64_decode(dst, text_literal("Zm9vYmFyZm9vYmFy"), false)) == u32(5))
  assert(failure(base32_decode(dst, text_literal("MZXW6YTB0I======"), false)) == u32(1))
  assert(failure(base32_decode(dst, text_literal("MZX"), false)) == u32(2))
  assert(failure(base32_decode(dst, text_literal("MZXW6=="), false)) == u32(3))
  assert(failure(base32_decode(dst, text_literal("MZ======"), false)) == u32(4))
  assert(failure(hex_decode(dst, text_literal("abc"))) == u32(2))
  assert(failure(hex_decode(dst, text_literal("zz"))) == u32(1))
  assert(failure(hex_decode(dst, text_literal("000102030405060708"))) == u32(5))
  assert(failure(percent_decode(dst, text_literal("a%2"), false)) == u32(1))
  assert(failure(percent_decode(dst, text_literal("a%zz"), false)) == u32(1))
  assert(failure(percent_encode(dst, text_literal("a b c d"), text_literal(""))) == u32(5))
  assert(failure(base64_encoded_size(u32(4000000000), true)) == u32(6))
  // Every rejection above left the destination untouched.
  assert(dst[0] == u8(7))
  // Unpadded base64 and lowercase base32 are accepted.
  assert(failure(base64_decode(dst, text_literal("Zm9vYmE"), false)) == u32(0))
  assert(dst[0] == u8(102) && dst[4] == u8(97))
  assert(failure(base32_decode(dst, text_literal("mzxw6ytb"), false)) == u32(0))
  assert(dst[0] == u8(102) && dst[4] == u8(97))
  42
}
`
	code, abnormal := buildAndRun(t, "encoding_rejections", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// The package is also importable by name with qualified references (library
// packages resolve through the module loader, so the program is a module root).
func TestE2EStdlibEncodingQualifiedImport(t *testing.T) {
	src := `package main
import("encoding")
main: (): i32 {
  out: [8]u8
  true ? {
    dst: [*]u8 = span(&out)
    n: u32 = encoding.encoding_value(encoding.hex_encode(dst, text_literal("AB"), true))
    assert(n == u32(4))
    assert(dst[0] == u8(52) && dst[1] == u8(49) && dst[2] == u8(52) && dst[3] == u8(50))
  }
  code: u32 = encoding.encoding_failure(encoding.hex_decoded_size(text_literal("abc")))
  code == u32(2) ? { 42 } | { 0 }
}
`
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/encoding_qualified\noak 0.1.0\n",
		"main.oak": src,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
