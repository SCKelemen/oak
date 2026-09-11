package compiler

import (
	"encoding/base32"
	"encoding/base64"
	"encoding/hex"
	"fmt"
	"math/rand"
	"strings"
	"testing"
)

// The table-driven codecs against Go's encoding/base64, encoding/base32 and
// encoding/hex on random inputs of every length class around the group
// sizes: the Oak encoding must equal Go's byte for byte in every alphabet,
// padded and unpadded, and decode back to the input. One compiled program
// carries every case, so the rewrite for speed cannot drift from the
// reference without this test noticing.
func TestE2EStdlibEncodingDifferential(t *testing.T) {
	random := rand.New(rand.NewSource(0xb64))
	var inputs [][]byte
	for _, n := range []int{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 15, 16, 17, 31, 32, 33, 63, 64, 65, 100, 127, 128, 129, 255, 256, 257} {
		data := make([]byte, n)
		random.Read(data)
		inputs = append(inputs, data)
	}
	var src strings.Builder
	src.WriteString("import(std)\n")
	src.WriteString(`
same: (got: []u8, want: []u8): Bool {
  ok: Bool = len(got) == len(want)
  i: u32 = 0
  while ok && i < len(want) {
    ok = got[i] == want[i]
    i = i + u32(1)
  }
  ok
}
`)
	type codec struct {
		name   string
		encode func([]byte) []byte
		call   string // encode call with %s for the destination span and %s for the source view
		decode string // decode call with %s for the destination span and %s for the source view
	}
	codecs := []codec{
		{"b64std_pad", func(b []byte) []byte { return []byte(base64.StdEncoding.EncodeToString(b)) }, "base64_encode(%s, %s, false, true)", "base64_decode(%s, %s, false)"},
		{"b64std_raw", func(b []byte) []byte { return []byte(base64.RawStdEncoding.EncodeToString(b)) }, "base64_encode(%s, %s, false, false)", "base64_decode(%s, %s, false)"},
		{"b64url_pad", func(b []byte) []byte { return []byte(base64.URLEncoding.EncodeToString(b)) }, "base64_encode(%s, %s, true, true)", "base64_decode(%s, %s, true)"},
		{"b64url_raw", func(b []byte) []byte { return []byte(base64.RawURLEncoding.EncodeToString(b)) }, "base64_encode(%s, %s, true, false)", "base64_decode(%s, %s, true)"},
		{"b32std_pad", func(b []byte) []byte { return []byte(base32.StdEncoding.EncodeToString(b)) }, "base32_encode(%s, %s, false, true)", "base32_decode(%s, %s, false)"},
		{"b32std_raw", func(b []byte) []byte {
			return []byte(base32.StdEncoding.WithPadding(base32.NoPadding).EncodeToString(b))
		}, "base32_encode(%s, %s, false, false)", "base32_decode(%s, %s, false)"},
		{"b32hex_pad", func(b []byte) []byte { return []byte(base32.HexEncoding.EncodeToString(b)) }, "base32_encode(%s, %s, true, true)", "base32_decode(%s, %s, true)"},
		{"hex_lower", func(b []byte) []byte { return []byte(hex.EncodeToString(b)) }, "hex_encode(%s, %s, false)", "hex_decode(%s, %s)"},
		{"hex_upper", func(b []byte) []byte { return []byte(strings.ToUpper(hex.EncodeToString(b))) }, "hex_encode(%s, %s, true)", "hex_decode(%s, %s)"},
	}
	count := 0
	for _, input := range inputs {
		for _, c := range codecs {
			expected := c.encode(input)
			fmt.Fprintf(&src, "case_%d: (): Bool {\n", count)
			writeBytes(&src, "input", input)
			writeBytes(&src, "want", expected)
			fmt.Fprintf(&src, "  out: [%d]u8\n  back: [%d]u8\n  ok: Bool = true\n", max(len(expected), 1), max(len(input), 1))
			fmt.Fprintf(&src, "  true ? {\n    dst: [*]u8 = span(&out)\n    ok = encoding_value(%s) == u32(%d)\n  }\n", fmt.Sprintf(c.call, "dst", "input"), len(expected))
			fmt.Fprintf(&src, "  encoded_whole: []u8 = view(&out)\n  encoded: []u8 = encoded_whole[u32(0):u32(%d)]\n  ok = ok && same(encoded, want)\n", len(expected))
			fmt.Fprintf(&src, "  true ? {\n    bdst: [*]u8 = span(&back)\n    ok = ok && encoding_value(%s) == u32(%d)\n  }\n", fmt.Sprintf(c.decode, "bdst", "encoded"), len(input))
			fmt.Fprintf(&src, "  decoded_whole: []u8 = view(&back)\n  ok && same(decoded_whole[u32(0):u32(%d)], input)\n}\n", len(input))
			count++
		}
	}
	src.WriteString("main: (): i32 {\n")
	for i := 0; i < count; i++ {
		fmt.Fprintf(&src, "  assert(case_%d())\n", i)
	}
	src.WriteString("  42\n}\n")
	code, abnormal := buildAndRun(t, "encoding_differential", src.String())
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
