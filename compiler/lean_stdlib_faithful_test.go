package compiler

import (
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"unicode/utf8"
)

// TestLeanStdlibFaithful runs the committed Lean extractions and the
// compiled Oak programs on one fixed corpus and compares their output byte
// for byte (docs/spec/95-extraction.md section 6). The drift test only
// checks that the committed text is current; this is the executable check
// that the text means what the compiled code does — it is what would have
// caught oak #186, where the heap sort's heapify loop lost its array. It
// needs the Lean toolchain (`lake` on PATH or under ~/.elan/bin) and the
// `spec/lean` library built; the Formal Verification workflow runs it.
func TestLeanStdlibFaithful(t *testing.T) {
	skipInShort(t)
	lake := findLake()
	if lake == "" {
		t.Skip("lake not found (PATH or ~/.elan/bin); the faithfulness check needs the Lean toolchain")
	}
	root, err := filepath.Abs(filepath.Join("..", "spec", "lean"))
	if err != nil {
		t.Fatal(err)
	}
	corpus := newFaithfulCorpus(20260911)

	// Oak: one module with qualified imports, printing one line per case.
	oakRoot := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/faithful\noak 0.1.0\n",
		"main.oak": "package main\n" + corpus.oakProgram(),
	})
	if dump := os.Getenv("OAK_FAITHFUL_DUMP"); dump != "" {
		// Keep both drivers for inspection.
		_ = os.MkdirAll(dump, 0o755)
		_ = os.WriteFile(filepath.Join(dump, "main.oak"), []byte("package main\n"+corpus.oakProgram()), 0o644)
		_ = os.WriteFile(filepath.Join(dump, "oak.mod"), []byte("module example.com/faithful\noak 0.1.0\n"), 0o644)
		_ = os.WriteFile(filepath.Join(dump, "faithful.lean"), []byte(corpus.leanProgram()), 0o644)
	}
	stdout, code, abnormal := buildAndRunFrom(t, "faithful", New().WithPackageDir(oakRoot))
	if abnormal || code != 0 {
		t.Fatalf("faithfulness program exited (%d, abnormal=%v):\n%s", code, abnormal, stdout)
	}

	// Lean: a driver over the extracted modules, run in the interpreter.
	build := exec.Command(lake, "build")
	build.Dir = root
	if out, err := build.CombinedOutput(); err != nil {
		t.Fatalf("lake build: %v\n%s", err, out)
	}
	driver := filepath.Join(t.TempDir(), "faithful.lean")
	if err := os.WriteFile(driver, []byte(corpus.leanProgram()), 0o644); err != nil {
		t.Fatal(err)
	}
	run := exec.Command(lake, "env", "lean", "--run", driver)
	run.Dir = root
	leanOut, err := run.CombinedOutput()
	if err != nil {
		t.Fatalf("lake env lean --run: %v\n%s", err, leanOut)
	}

	oakLines := strings.Split(strings.TrimRight(stdout, "\n"), "\n")
	leanLines := strings.Split(strings.TrimRight(string(leanOut), "\n"), "\n")
	if len(oakLines) != corpus.lines || len(leanLines) != corpus.lines {
		t.Fatalf("line counts: oak %d, lean %d, want %d\n--- oak\n%s\n--- lean\n%s", len(oakLines), len(leanLines), corpus.lines, stdout, leanOut)
	}
	mismatches := 0
	for i := range oakLines {
		if oakLines[i] != leanLines[i] {
			mismatches++
			if mismatches <= 10 {
				t.Errorf("line %d differs\n  oak:  %s\n  lean: %s", i+1, oakLines[i], leanLines[i])
			}
		}
	}
	if mismatches > 0 {
		t.Fatalf("%d of %d lines differ between the compiled Oak and the extracted Lean", mismatches, corpus.lines)
	}
}

func findLake() string {
	if path, err := exec.LookPath("lake"); err == nil {
		return path
	}
	home, err := os.UserHomeDir()
	if err != nil {
		return ""
	}
	candidate := filepath.Join(home, ".elan", "bin", "lake")
	if _, err := os.Stat(candidate); err == nil {
		return candidate
	}
	return ""
}

// faithfulCorpus is the shared input set. Every case prints one line of
// decimal numbers separated by single spaces, prefixed by the case name.
type faithfulCorpus struct {
	sortInputs   [][]uint32 // each 1..24 elements
	varintValues []uint64
	bytesInputs  [][]byte // each 1..20 bytes, hex/base64
	seeds        []uint64
	hashInputs   [][]byte // each 1..70 bytes
	// Floats travel as bit patterns; a NaN result prints as the canonical
	// quiet NaN on both sides (payloads are not modeled, section 3).
	f64Bits    []uint64    // float_format, float_format_fixed, math
	f32Bits    []uint32    // float_format_f32, exp_f32/sin_f32
	floatTexts []string    // float_parse, float_parse_f32
	kernelVecs [][]uint32  // f32 bit patterns for dot/sum/axpy/max_abs/widen_mean
	mathPairs  [][2]uint64 // pow(x, y), atan2(y, x)
	// Text: byte strings for the strings package (valid, damaged, and
	// random), grapheme and normalization inputs (valid UTF-8 with
	// combining marks, ZWJ sequences, Hangul), URL references, and paths.
	textInputs  [][]byte
	graphInputs [][]byte
	normInputs  [][]byte
	urlInputs   []string
	pathInputs  []string
	lines       int
}

func newFaithfulCorpus(seed int64) *faithfulCorpus {
	rng := rand.New(rand.NewSource(seed))
	c := &faithfulCorpus{}
	for i := 0; i < 30; i++ {
		n := 1 + rng.Intn(24)
		items := make([]uint32, n)
		switch i % 5 {
		case 0: // sorted
			for j := range items {
				items[j] = uint32(j * 3)
			}
		case 1: // reversed
			for j := range items {
				items[j] = uint32((n - j) * 2)
			}
		case 2: // few distinct
			for j := range items {
				items[j] = uint32(rng.Intn(3))
			}
		default:
			for j := range items {
				items[j] = uint32(rng.Intn(100))
			}
		}
		c.sortInputs = append(c.sortInputs, items)
	}
	for i := 0; i < 60; i++ {
		bits := uint(1 + rng.Intn(64))
		v := rng.Uint64()
		if bits < 64 {
			v &= (uint64(1) << bits) - 1
		}
		c.varintValues = append(c.varintValues, v)
	}
	for i := 0; i < 30; i++ {
		b := make([]byte, 1+rng.Intn(20))
		rng.Read(b)
		c.bytesInputs = append(c.bytesInputs, b)
	}
	c.seeds = []uint64{0, 1, 7, rng.Uint64()}
	for i := 0; i < 12; i++ {
		b := make([]byte, 1+rng.Intn(70))
		rng.Read(b)
		c.hashInputs = append(c.hashInputs, b)
	}
	// Floats: hand-picked hard values plus random bit patterns with
	// bounded exponents so exp/log/sin stay finite and interesting.
	c.f64Bits = []uint64{
		0, 1 << 63, // ±0
		0x3FF0000000000000, 0xBFF0000000000000, // ±1
		0x3FB999999999999A, // 0.1
		0x3FD5555555555555, // 1/3
		0x0000000000000001, // least subnormal
		0x000FFFFFFFFFFFFF, // largest subnormal
		0x0010000000000000, // least normal
		0x7FEFFFFFFFFFFFFF, // largest finite
		0x4415AF1D78B58C40, // 1e20
		0x44B52D02C7E14AF6, // 1e22
		0x3E7AD7F29ABCAF48, // 1e-7
		0x4086240000000000, // 709 (exp's edge)
		0x412E848000000000, // 1e6 (sin's medium reduction)
		0x40C81C8000000000, // 12345
		0xC00921FB54442D18, // -pi
		0x400921FB54442D18, // pi
	}
	for i := 0; i < 40; i++ {
		exponent := uint64(1023 - 30 + rng.Intn(61)) // 2^-30 .. 2^30
		mant := rng.Uint64() & ((1 << 52) - 1)
		sign := uint64(rng.Intn(2)) << 63
		c.f64Bits = append(c.f64Bits, sign|(exponent<<52)|mant)
	}
	c.f32Bits = []uint32{0, 1 << 31, 0x3F800000, 0x3DCCCCCD, 0x00000001, 0x007FFFFF, 0x00800000, 0x7F7FFFFF, 0x42F70000, 0x40490FDB}
	for i := 0; i < 30; i++ {
		exponent := uint32(127 - 20 + rng.Intn(41))
		mant := rng.Uint32() & ((1 << 23) - 1)
		sign := uint32(rng.Intn(2)) << 31
		c.f32Bits = append(c.f32Bits, sign|(exponent<<23)|mant)
	}
	c.floatTexts = []string{
		"0", "-0", "1", "0.1", "0.3", "0.30000000000000004", "1e23", "9.999999999999999e22",
		"2.2250738585072011e-308", "2.2250738585072012e-308", "5e-324", "1.7976931348623157e308",
		"9007199254740993", "123456789012345680", "1e-400", "1e400", "inf", "-Infinity", "nan",
		"3.4028235e38", "1.17549435e-38", "1.4e-45", "16777217", "0.1e1", "-.5", "+7.25E-3",
		"abc", "1..2", "", ".", "1e",
	}
	for i := 0; i < 20; i++ {
		c.floatTexts = append(c.floatTexts, fmt.Sprintf("%.17g", rng.NormFloat64()*1e6))
	}
	for i := 0; i < 12; i++ {
		n := 1 + rng.Intn(9)
		vec := make([]uint32, n)
		for j := range vec {
			exponent := uint32(127 - 8 + rng.Intn(17))
			mant := rng.Uint32() & ((1 << 23) - 1)
			sign := uint32(rng.Intn(2)) << 31
			vec[j] = sign | (exponent << 23) | mant
		}
		c.kernelVecs = append(c.kernelVecs, vec)
	}
	for i := 0; i < 16; i++ {
		x := uint64(rng.Intn(2))<<63 | uint64(1023-6+rng.Intn(13))<<52 | rng.Uint64()&((1<<52)-1)
		y := uint64(rng.Intn(2))<<63 | uint64(1023-3+rng.Intn(7))<<52 | rng.Uint64()&((1<<52)-1)
		c.mathPairs = append(c.mathPairs, [2]uint64{x, y})
	}
	// Text: valid strings from random scalars, the same with one byte
	// damaged, and raw random bytes, so both the accepting and the
	// rejecting paths of the UTF-8 decoder and validator are compared.
	randomScalar := func() rune {
		for {
			r := rune(rng.Intn(0x110000))
			if r >= 0xD800 && r <= 0xDFFF {
				continue
			}
			if rng.Intn(3) == 0 {
				r = rune(rng.Intn(0x80))
			}
			return r
		}
	}
	for i := 0; i < 36; i++ {
		var b []byte
		switch i % 3 {
		case 0:
			for k := 0; k < 1+rng.Intn(8); k++ {
				b = utf8.AppendRune(b, randomScalar())
			}
		case 1:
			for k := 0; k < 1+rng.Intn(8); k++ {
				b = utf8.AppendRune(b, randomScalar())
			}
			b[rng.Intn(len(b))] ^= byte(1 << uint(rng.Intn(8)))
		default:
			b = make([]byte, 1+rng.Intn(12))
			rng.Read(b)
		}
		c.textInputs = append(c.textInputs, b)
	}
	graphemeRunes := [][]rune{
		{'a', 'b', 'c'},
		{'e', 0x301, 'x'}, // e + combining acute
		{0x1F468, 0x200D, 0x1F469, 0x200D, 0x1F467}, // family ZWJ sequence
		{0x1F1FA, 0x1F1F8, 0x1F1EC, 0x1F1E7},        // two flags
		{0x1100, 0x1161, 0x11A8, 'k'},               // Hangul L V T
		{'\r', '\n', 'a', '\n'},
		{0x915, 0x94D, 0x937, 0x93F}, // Devanagari conjunct with virama
		{0x1F600, 0x1F3FB, 0x200D, 0x2640, 0xFE0F},
	}
	for _, rs := range graphemeRunes {
		var b []byte
		for _, r := range rs {
			b = utf8.AppendRune(b, r)
		}
		c.graphInputs = append(c.graphInputs, b)
	}
	for i := 0; i < 8; i++ {
		var b []byte
		for k := 0; k < 1+rng.Intn(6); k++ {
			b = utf8.AppendRune(b, randomScalar())
		}
		c.graphInputs = append(c.graphInputs, b)
	}
	normRunes := [][]rune{
		{'e', 0x301},     // decomposed e-acute
		{0xE9},           // composed e-acute
		{0x212B},         // ANGSTROM SIGN singleton
		{0xAC00, 0xD7A3}, // Hangul syllables
		{0x1100, 0x1161, 0x11A8},
		{'a', 0x315, 0x300, 0x5AE, 0x300}, // CCC reordering
		{0x1E0A, 0x323},                   // D-dot-above + dot-below
		{0x0958},                          // composition exclusion
		{'A', 'S', 'C', 'I', 'I'},
	}
	for _, rs := range normRunes {
		var b []byte
		for _, r := range rs {
			b = utf8.AppendRune(b, r)
		}
		c.normInputs = append(c.normInputs, b)
	}
	c.urlInputs = []string{
		"foo://example.com:8042/over/there?name=ferret#nose",
		"http://a/b/c/d;p?q", "g:h", "//g", "?y", "#s", "../g", "mailto:John.Doe@example.com",
		"urn:example:animal:ferret:nose", "http://[2001:db8::7]/c=GB?objectClass?one",
		"ht tp://bad", "http://host:8x/", "%G1", "http://host/[",
	}
	c.pathInputs = []string{
		"", ".", "/", "a/b/c", "a//b", "a/./b", "a/../b", "/../a", "abc/../..", "/a/b/../../..", "abc/def/..", ".//..//a",
	}
	// sorts: 3 per input; varint: encode+decode lines; bytes: hex enc/dec,
	// b64 enc/dec; random: one line per seed; hash: crc and sha per input;
	// f64: format, fixed, and eleven math functions per value; f32: format
	// plus exp_f32/sin_f32; texts: parse f64 and f32; kernels: five
	// reductions, quantize, and axpy per vector; pairs: pow and atan2.
	// text: validate, count, and a decode scan per input; grapheme: one
	// boundary chain per input; normalize: nfc, nfd, is_nfc per input; url:
	// one line per reference; path: one line per path.
	c.lines = 3*len(c.sortInputs) + 2*len(c.varintValues) + 4*len(c.bytesInputs) + len(c.seeds) + 2*len(c.hashInputs) +
		13*len(c.f64Bits) + 3*len(c.f32Bits) + 2*len(c.floatTexts) + 7*len(c.kernelVecs) + 2*len(c.mathPairs) +
		3*len(c.textInputs) + len(c.graphInputs) + 3*len(c.normInputs) + len(c.urlInputs) + len(c.pathInputs)
	return c
}

func leanF32Array(bits []uint32) string {
	parts := make([]string, len(bits))
	for i, v := range bits {
		parts[i] = fmt.Sprintf("(Float32.ofBits (%d : UInt32))", v)
	}
	return leanArray(parts, "Float32")
}

func oakU32Array(items []uint32) string {
	parts := make([]string, len(items))
	for i, v := range items {
		parts[i] = fmt.Sprintf("%d", v)
	}
	return fmt.Sprintf("[%d]u32{ %s }", len(items), strings.Join(parts, ", "))
}

func oakU8Array(items []byte) string {
	parts := make([]string, len(items))
	for i, v := range items {
		parts[i] = fmt.Sprintf("%d", v)
	}
	return fmt.Sprintf("[%d]u8{ %s }", len(items), strings.Join(parts, ", "))
}

func leanArray(items []string, typ string) string {
	if len(items) == 0 {
		return fmt.Sprintf("(#[] : Array %s)", typ)
	}
	return fmt.Sprintf("(#[%s] : Array %s)", strings.Join(items, ", "), typ)
}

func leanU32Array(items []uint32) string {
	parts := make([]string, len(items))
	for i, v := range items {
		parts[i] = fmt.Sprintf("(%d : UInt32)", v)
	}
	return leanArray(parts, "UInt32")
}

func leanU8Array(items []byte) string {
	parts := make([]string, len(items))
	for i, v := range items {
		parts[i] = fmt.Sprintf("(%d : UInt8)", v)
	}
	return leanArray(parts, "UInt8")
}

// oakProgram prints, per case, the case name and the outputs as decimal
// numbers; helpers print through putchar so no text package is involved.
func (c *faithfulCorpus) oakProgram() string {
	var b strings.Builder
	b.WriteString(`import(std)
import("sort")
import("varint")
import("encoding")
import("random")
import("hash")
import("float")
import("math")
import("strings")
import("grapheme")
import("normalize")
import("url")
import("path")

putchar: (ch: c.Int): c.Int = c.extern("putchar")

put: (unit: u8): () {
  _ = putchar(c.Int(i32_bits_u32(u32(unit))))
}
put_text: (text: []u8): () {
  i: u32 = 0
  while i < len(text) { put(text[i])
    i = i + u32(1)
  }
}
put_u64: (value: u64): () {
  digits: [20]u8
  n: u32 = 0
  rest: u64 = value
  more: Bool = true
  while more {
    digits[n] = u8(48) + u8_trunc_u64(rest % u64(10))
    n = n + u32(1)
    rest = rest / u64(10)
    rest == u64(0) ? { more = false }
  }
  while n > u32(0) {
    n = n - u32(1)
    put(digits[n])
  }
}
put_sep: (): () {
  put(u8(32))
}
put_nl: (): () {
  put(u8(10))
}
put_u32s: (items: []u32): () {
  i: u32 = 0
  while i < len(items) { put_sep(); put_u64(u64(items[i]))
    i = i + u32(1)
  }
}
put_u8s: (items: []u8): () {
  i: u32 = 0
  while i < len(items) { put_sep(); put_u64(u64(items[i]))
    i = i + u32(1)
  }
}
// bits_f64/bits_f32 print a float as its bit pattern with every NaN
// spelled as the canonical quiet NaN.
bits_f64: (x: f64): u64 = is_nan(x) ? u64(9221120237041090560) | u64_bits_f64(x)
bits_f32: (x: f32): u64 = is_nan(x) ? u64(2143289344) | u64(u32_bits_f32(x))
put_f64: (x: f64): () { put_sep(); put_u64(bits_f64(x)) }
put_f32: (x: f32): () { put_sep(); put_u64(bits_f32(x)) }
`)
	b.WriteString(leanFloatKernelsSource)
	// Sorts.
	for i, items := range c.sortInputs {
		fmt.Fprintf(&b, "sort_case_%d: (): () {\n", i)
		for _, kind := range []string{"heap", "span", "insertion"} {
			fmt.Fprintf(&b, "  %s_%d: [%d]u32 = %s\n", kind, i, len(items), oakU32Array(items))
			fmt.Fprintf(&b, "  true ? { s: [*]u32 = span(&%s_%d)\n    sort.sort_%s[u32](s) }\n", kind, i, kind)
			fmt.Fprintf(&b, "  put_text(text_literal(\"sort_%s %d\")); put_u32s(view(&%s_%d)); put_nl()\n", kind, i, kind, i)
		}
		b.WriteString("}\n")
	}
	// Varint.
	b.WriteString("varint_cases: (): () {\n")
	for i, v := range c.varintValues {
		fmt.Fprintf(&b, "  true ? {\n    buf: [10]u8\n    n: u32 = 0\n    true ? { d: [*]u8 = span(&buf)\n      n = varint.varint_written(varint.varint_encode(d, u32(0), u64(%d))) }\n", v)
		fmt.Fprintf(&b, "    whole: []u8 = view(&buf)\n    encoded: []u8 = whole[u32(0):n]\n")
		fmt.Fprintf(&b, "    put_text(text_literal(\"varint_encode %d\")); put_sep(); put_u64(u64(n)); put_u8s(encoded); put_nl()\n", i)
		fmt.Fprintf(&b, "    back: varint.VarintValue = varint.varint_value(varint.varint_decode(encoded, u32(0)))\n")
		fmt.Fprintf(&b, "    put_text(text_literal(\"varint_decode %d\")); put_sep(); put_u64(back.value); put_sep(); put_u64(u64(back.next)); put_nl()\n  }\n", i)
	}
	b.WriteString("}\n")
	// Hex and base64.
	for i, src := range c.bytesInputs {
		fmt.Fprintf(&b, "bytes_case_%d: (): () {\n  src: [%d]u8 = %s\n", i, len(src), oakU8Array(src))
		b.WriteString("  hex: [64]u8\n  hexn: u32 = 0\n  true ? { d: [*]u8 = span(&hex)\n    hexn = encoding.encoding_value(encoding.hex_encode(d, view(&src), false)) }\n")
		b.WriteString("  hexv: []u8 = view(&hex)\n  hexenc: []u8 = hexv[u32(0):hexn]\n")
		fmt.Fprintf(&b, "  put_text(text_literal(\"hex_encode %d\")); put_sep(); put_u64(u64(hexn)); put_u8s(hexenc); put_nl()\n", i)
		b.WriteString("  hexback: [32]u8\n  hexbn: u32 = 0\n  true ? { d: [*]u8 = span(&hexback)\n    hexbn = encoding.encoding_value(encoding.hex_decode(d, hexenc)) }\n")
		b.WriteString("  hexbv: []u8 = view(&hexback)\n")
		fmt.Fprintf(&b, "  put_text(text_literal(\"hex_decode %d\")); put_sep(); put_u64(u64(hexbn)); put_u8s(hexbv[u32(0):hexbn]); put_nl()\n", i)
		b.WriteString("  b64: [64]u8\n  b64n: u32 = 0\n  true ? { d: [*]u8 = span(&b64)\n    b64n = encoding.encoding_value(encoding.base64_encode(d, view(&src), false, true)) }\n")
		b.WriteString("  b64v: []u8 = view(&b64)\n  b64enc: []u8 = b64v[u32(0):b64n]\n")
		fmt.Fprintf(&b, "  put_text(text_literal(\"base64_encode %d\")); put_sep(); put_u64(u64(b64n)); put_u8s(b64enc); put_nl()\n", i)
		b.WriteString("  b64back: [48]u8\n  b64bn: u32 = 0\n  true ? { d: [*]u8 = span(&b64back)\n    b64bn = encoding.encoding_value(encoding.base64_decode(d, b64enc, false)) }\n")
		b.WriteString("  b64bv: []u8 = view(&b64back)\n")
		fmt.Fprintf(&b, "  put_text(text_literal(\"base64_decode %d\")); put_sep(); put_u64(u64(b64bn)); put_u8s(b64bv[u32(0):b64bn]); put_nl()\n}\n", i)
	}
	// Random.
	b.WriteString("random_cases: (): () {\n")
	for i, seed := range c.seeds {
		fmt.Fprintf(&b, "  true ? {\n    states: [1]random.Xoshiro\n    states[0] = random.random_seed(u64(%d))\n    st: [*]random.Xoshiro = span(&states)\n", seed)
		fmt.Fprintf(&b, "    put_text(text_literal(\"random %d\"))\n    k: u32 = 0\n    while k < u32(8) { put_sep(); put_u64(random.random_next(st))\n      k = k + u32(1)\n    }\n    put_nl()\n  }\n", i)
	}
	b.WriteString("}\n")
	// Hash.
	for i, src := range c.hashInputs {
		fmt.Fprintf(&b, "hash_case_%d: (): () {\n  src: [%d]u8 = %s\n", i, len(src), oakU8Array(src))
		fmt.Fprintf(&b, "  put_text(text_literal(\"crc32c %d\")); put_sep(); put_u64(u64(hash.crc32c(view(&src)))); put_nl()\n", i)
		b.WriteString("  out: [32]u8\n  true ? { d: [*]u8 = span(&out)\n    _ = hash.sha256(view(&src), d) }\n")
		fmt.Fprintf(&b, "  put_text(text_literal(\"sha256 %d\")); put_u8s(view(&out)); put_nl()\n}\n", i)
	}
	// Floats: format the value, its fixed form, and the math functions.
	for i, bits := range c.f64Bits {
		fmt.Fprintf(&b, "f64_case_%d: (): () {\n  x: f64 = f64_bits_u64(u64(%d))\n", i, bits)
		b.WriteString("  txt: [40]u8\n  n: u32 = 0\n  true ? { d: [*]u8 = span(&txt)\n    n = float.float_written(float.float_format(d, x)) }\n")
		b.WriteString("  tv: []u8 = view(&txt)\n")
		fmt.Fprintf(&b, "  put_text(text_literal(\"float_format %d\")); put_sep(); put_u64(u64(n)); put_u8s(tv[u32(0):n]); put_nl()\n", i)
		b.WriteString("  fixed: [40]u8\n  m: u32 = 0\n  true ? { d: [*]u8 = span(&fixed)\n    m = float.float_written(float.float_format_fixed(d, x, u32(3))) }\n")
		b.WriteString("  fv: []u8 = view(&fixed)\n")
		fmt.Fprintf(&b, "  put_text(text_literal(\"float_format_fixed %d\")); put_sep(); put_u64(u64(m)); put_u8s(fv[u32(0):m]); put_nl()\n", i)
		for _, fn := range []string{"exp", "exp2", "log", "log2", "expm1", "log1p", "sin", "cos", "tan", "tanh", "atan"} {
			fmt.Fprintf(&b, "  put_text(text_literal(\"math_%s %d\")); put_f64(math.%s(x)); put_nl()\n", fn, i, fn)
		}
		b.WriteString("}\n")
	}
	for i, bits := range c.f32Bits {
		fmt.Fprintf(&b, "f32_case_%d: (): () {\n  x: f32 = f32_bits_u32(u32(%d))\n", i, bits)
		b.WriteString("  txt: [40]u8\n  n: u32 = 0\n  true ? { d: [*]u8 = span(&txt)\n    n = float.float_written(float.float_format_f32(d, x)) }\n")
		b.WriteString("  tv: []u8 = view(&txt)\n")
		fmt.Fprintf(&b, "  put_text(text_literal(\"float_format_f32 %d\")); put_sep(); put_u64(u64(n)); put_u8s(tv[u32(0):n]); put_nl()\n", i)
		fmt.Fprintf(&b, "  put_text(text_literal(\"math_exp_f32 %d\")); put_f32(math.exp_f32(x)); put_nl()\n", i)
		fmt.Fprintf(&b, "  put_text(text_literal(\"math_sin_f32 %d\")); put_f32(math.sin_f32(x)); put_nl()\n}\n", i)
	}
	for i, text := range c.floatTexts {
		fmt.Fprintf(&b, "parse_case_%d: (): () {\n", i)
		if len(text) == 0 {
			b.WriteString("  src: [1]u8\n  sv: []u8 = view(&src)\n  s: []u8 = sv[u32(0):u32(0)]\n")
		} else {
			fmt.Fprintf(&b, "  src: [%d]u8 = %s\n  s: []u8 = view(&src)\n", len(text), oakU8Array([]byte(text)))
		}
		b.WriteString("  r: Result[f64, float.FloatError] = float.float_parse(s)\n")
		fmt.Fprintf(&b, "  put_text(text_literal(\"float_parse %d\")); put_sep(); put_u64(u64(float.float_parse_failure(r))); put_f64(float.float_parse_value(r, 0.0)); put_nl()\n", i)
		b.WriteString("  r32: Result[f32, float.FloatError] = float.float_parse_f32(s)\n")
		fmt.Fprintf(&b, "  put_text(text_literal(\"float_parse_f32 %d\")); put_sep(); put_u64(u64(float.float_parse_failure_f32(r32))); put_f32(float.float_parse_value_f32(r32, 0.0)); put_nl()\n}\n", i)
	}
	for i, vec := range c.kernelVecs {
		fmt.Fprintf(&b, "kernel_case_%d: (): () {\n  bits: [%d]u32 = %s\n  xs: [%d]f32\n  ys: [%d]f32\n  wide: [%d]f64\n", i, len(vec), oakU32Array(vec), len(vec), len(vec), len(vec))
		fmt.Fprintf(&b, "  k: u32 = 0\n  while k < u32(%d) { xs[k] = f32_bits_u32(bits[k]); ys[k] = f32_bits_u32(bits[u32(%d) - k]); wide[k] = f64(xs[k])\n    k = k + u32(1)\n  }\n", len(vec), len(vec)-1)
		fmt.Fprintf(&b, "  put_text(text_literal(\"dot_f32 %d\")); put_f32(dot_f32(view(&xs), view(&ys))); put_nl()\n", i)
		fmt.Fprintf(&b, "  put_text(text_literal(\"sum_f32 %d\")); put_f32(sum_f32(view(&xs))); put_nl()\n", i)
		fmt.Fprintf(&b, "  put_text(text_literal(\"sum_f64 %d\")); put_f64(sum_f64(view(&wide))); put_nl()\n", i)
		fmt.Fprintf(&b, "  put_text(text_literal(\"max_abs_f32 %d\")); put_f32(max_abs_f32(view(&xs))); put_nl()\n", i)
		fmt.Fprintf(&b, "  put_text(text_literal(\"widen_mean %d\")); put_f64(widen_mean(view(&xs))); put_nl()\n", i)
		fmt.Fprintf(&b, "  put_text(text_literal(\"quantize_u8 %d\")); put_sep(); put_u64(u64(quantize_u8(xs[0], f32_bits_u32(u32(1056964608))))); put_nl()\n", i)
		b.WriteString("  true ? { ysp: [*]f32 = span(&ys)\n    axpy_f32(xs[0], view(&xs), ysp) }\n")
		fmt.Fprintf(&b, "  put_text(text_literal(\"axpy_f32 %d\"))\n  j: u32 = 0\n  while j < u32(%d) { put_f32(ys[j])\n    j = j + u32(1)\n  }\n  put_nl()\n}\n", i, len(vec))
	}
	for i, pair := range c.mathPairs {
		fmt.Fprintf(&b, "pair_case_%d: (): () {\n  x: f64 = f64_bits_u64(u64(%d))\n  y: f64 = f64_bits_u64(u64(%d))\n", i, pair[0], pair[1])
		fmt.Fprintf(&b, "  put_text(text_literal(\"math_pow %d\")); put_f64(math.pow(x, y)); put_nl()\n", i)
		fmt.Fprintf(&b, "  put_text(text_literal(\"math_atan2 %d\")); put_f64(math.atan2(y, x)); put_nl()\n}\n", i)
	}
	// Text: UTF-8 validation, the count, and a decode scan that follows
	// `next` until the end or the first error.
	b.WriteString(`text_ok: (r: Result[u32, strings.TextError]): u32 = r ? | .Ok(v) => u32(0) | .Err(e) => u32(1)
text_count_value: (r: Result[u32, strings.TextError]): u32 = r ? | .Ok(v) => v | .Err(e) => u32(0)
scan_text: (src: []u8): () {
  at: u32 = 0
  more: Bool = true
  steps: u32 = 0
  while more && steps < u32(64) {
    r: Result[strings.TextScalar, strings.TextError] = strings.utf8_decode(src, at)
    r ? | .Ok(item) => { put_sep(); put_u64(u64(item.value)); put_sep(); put_u64(u64(item.next))
      at = item.next
      at >= len(src) ? { more = false } }
      | .Err(e) => { put_sep(); put_u64(u64(999)); more = false }
    steps = steps + u32(1)
  }
}
`)
	for i, src := range c.textInputs {
		fmt.Fprintf(&b, "text_case_%d: (): () {\n  src: [%d]u8 = %s\n  s: []u8 = view(&src)\n", i, len(src), oakU8Array(src))
		fmt.Fprintf(&b, "  put_text(text_literal(\"utf8_validate %d\")); put_sep(); put_u64(strings.utf8_validate(s) ? u64(1) | u64(0)); put_nl()\n", i)
		fmt.Fprintf(&b, "  r: Result[u32, strings.TextError] = strings.utf8_count(s)\n")
		fmt.Fprintf(&b, "  put_text(text_literal(\"utf8_count %d\")); put_sep(); put_u64(u64(text_ok(r))); put_sep(); put_u64(u64(text_count_value(r))); put_nl()\n", i)
		fmt.Fprintf(&b, "  put_text(text_literal(\"utf8_scan %d\")); scan_text(s); put_nl()\n}\n", i)
	}
	for i, src := range c.graphInputs {
		fmt.Fprintf(&b, "grapheme_case_%d: (): () {\n  src: [%d]u8 = %s\n  s: []u8 = view(&src)\n", i, len(src), oakU8Array(src))
		fmt.Fprintf(&b, "  put_text(text_literal(\"grapheme %d\"))\n  at: u32 = 0\n  steps: u32 = 0\n  while at < len(s) && steps < u32(64) { at = grapheme.grapheme_next(s, at); put_sep(); put_u64(u64(at))\n    steps = steps + u32(1)\n  }\n  put_nl()\n}\n", i)
	}
	for i, src := range c.normInputs {
		fmt.Fprintf(&b, "norm_case_%d: (): () {\n  src: [%d]u8 = %s\n  s: []u8 = view(&src)\n", i, len(src), oakU8Array(src))
		b.WriteString("  out: [96]u8\n  n: u32 = 0\n  true ? { d: [*]u8 = span(&out)\n    n = normalize.normalize_written(normalize.normalize_nfc(d, s)) }\n  ov: []u8 = view(&out)\n")
		fmt.Fprintf(&b, "  put_text(text_literal(\"normalize_nfc %d\")); put_sep(); put_u64(u64(n)); put_u8s(ov[u32(0):n]); put_nl()\n", i)
		b.WriteString("  out2: [96]u8\n  m: u32 = 0\n  true ? { d: [*]u8 = span(&out2)\n    m = normalize.normalize_written(normalize.normalize_nfd(d, s)) }\n  ov2: []u8 = view(&out2)\n")
		fmt.Fprintf(&b, "  put_text(text_literal(\"normalize_nfd %d\")); put_sep(); put_u64(u64(m)); put_u8s(ov2[u32(0):m]); put_nl()\n", i)
		fmt.Fprintf(&b, "  put_text(text_literal(\"normalize_is_nfc %d\")); put_sep(); put_u64(normalize.normalize_is_nfc(s) ? u64(1) | u64(0)); put_nl()\n}\n", i)
	}
	b.WriteString(`put_range: (r: url.UrlRange): () {
  put_sep(); put_u64(r.present ? u64(1) | u64(0)); put_sep(); put_u64(u64(r.start)); put_sep(); put_u64(u64(r.end))
}
put_url: (r: Result[url.Url, url.UrlError]): () {
  r ? | .Ok(u) => { put_sep(); put_u64(u64(0)); put_range(u.scheme); put_range(u.userinfo); put_range(u.host); put_range(u.port); put_range(u.path); put_range(u.query); put_range(u.fragment) }
    | .Err(e) => { put_sep(); put_u64(u64(1)) }
}
`)
	for i, src := range c.urlInputs {
		fmt.Fprintf(&b, "url_case_%d: (): () {\n  src: [%d]u8 = %s\n  s: []u8 = view(&src)\n", i, len(src), oakU8Array([]byte(src)))
		fmt.Fprintf(&b, "  put_text(text_literal(\"url_parse %d\")); put_url(url.url_parse(s)); put_nl()\n}\n", i)
	}
	for i, src := range c.pathInputs {
		if len(src) == 0 {
			fmt.Fprintf(&b, "path_case_%d: (): () {\n  src: [1]u8\n  sv: []u8 = view(&src)\n  s: []u8 = sv[u32(0):u32(0)]\n", i)
		} else {
			fmt.Fprintf(&b, "path_case_%d: (): () {\n  src: [%d]u8 = %s\n  s: []u8 = view(&src)\n", i, len(src), oakU8Array([]byte(src)))
		}
		b.WriteString("  out: [32]u8\n  n: u32 = 0\n  true ? { d: [*]u8 = span(&out)\n    n = path.path_written(path.path_clean(d, s)) }\n  ov: []u8 = view(&out)\n")
		fmt.Fprintf(&b, "  put_text(text_literal(\"path_clean %d\")); put_sep(); put_u64(u64(n)); put_u8s(ov[u32(0):n]); put_nl()\n}\n", i)
	}
	b.WriteString("main: (): i32 {\n")
	for i := range c.sortInputs {
		fmt.Fprintf(&b, "  sort_case_%d()\n", i)
	}
	b.WriteString("  varint_cases()\n")
	for i := range c.bytesInputs {
		fmt.Fprintf(&b, "  bytes_case_%d()\n", i)
	}
	b.WriteString("  random_cases()\n")
	for i := range c.hashInputs {
		fmt.Fprintf(&b, "  hash_case_%d()\n", i)
	}
	for i := range c.f64Bits {
		fmt.Fprintf(&b, "  f64_case_%d()\n", i)
	}
	for i := range c.f32Bits {
		fmt.Fprintf(&b, "  f32_case_%d()\n", i)
	}
	for i := range c.floatTexts {
		fmt.Fprintf(&b, "  parse_case_%d()\n", i)
	}
	for i := range c.kernelVecs {
		fmt.Fprintf(&b, "  kernel_case_%d()\n", i)
	}
	for i := range c.mathPairs {
		fmt.Fprintf(&b, "  pair_case_%d()\n", i)
	}
	for i := range c.textInputs {
		fmt.Fprintf(&b, "  text_case_%d()\n", i)
	}
	for i := range c.graphInputs {
		fmt.Fprintf(&b, "  grapheme_case_%d()\n", i)
	}
	for i := range c.normInputs {
		fmt.Fprintf(&b, "  norm_case_%d()\n", i)
	}
	for i := range c.urlInputs {
		fmt.Fprintf(&b, "  url_case_%d()\n", i)
	}
	for i := range c.pathInputs {
		fmt.Fprintf(&b, "  path_case_%d()\n", i)
	}
	b.WriteString("  0\n}\n")
	return b.String()
}

// leanProgram is the driver over the extracted modules producing the same
// lines. Every extracted function is fuel-indexed; the fuel is far above
// any loop bound here, so `none` prints as a visible disagreement.
func (c *faithfulCorpus) leanProgram() string {
	var b strings.Builder
	b.WriteString(`import Oak.Stdlib.SortU32Extracted
import Oak.Stdlib.VarintExtracted
import Oak.Stdlib.EncodingExtracted
import Oak.Stdlib.RandomExtracted
import Oak.Stdlib.HashExtracted
import Oak.Stdlib.FloatExtracted
import Oak.Stdlib.FloatKernelsExtracted
import Oak.Stdlib.MathExtracted
import Oak.Stdlib.StringsExtracted
import Oak.Stdlib.GraphemeExtracted
import Oak.Stdlib.NormalizeExtracted
import Oak.Stdlib.UrlExtracted
import Oak.Stdlib.PathExtracted

set_option maxRecDepth 65536

def fuel : Nat := 1000000

def showU32s (xs : Array UInt32) : String :=
  String.join (xs.toList.map (fun v => " " ++ toString v.toNat))

def showU8s (xs : Array UInt8) : String :=
  String.join (xs.toList.map (fun v => " " ++ toString v.toNat))

def showSort (name : String) (r : Option (Unit × Array UInt32)) : String :=
  match r with
  | some (_, xs) => name ++ showU32s xs
  | none => name ++ " none"

def varintWritten (r : Oak.Stdlib.Varint.Result_u32_VarintError) : UInt32 :=
  match r with
  | .Ok n => n
  | .Err _ => 0

def varintValue (r : Oak.Stdlib.Varint.Result_VarintValue_VarintError) : Oak.Stdlib.Varint.VarintValue :=
  match r with
  | .Ok v => v
  | .Err _ => { value := 0, next := 0 }

def encodingValue (r : Oak.Stdlib.Encoding.Result_u32_EncodingError) : UInt32 :=
  match r with
  | .Ok n => n
  | .Err _ => 0

def varintLines (i : Nat) (v : UInt64) : IO Unit := do
  match Oak.Stdlib.Varint.varint_encode (Array.replicate 10 (0 : UInt8)) 0 v fuel with
  | none => IO.println s!"varint_encode {i} none"; IO.println s!"varint_decode {i} none"
  | some (r, buf) =>
    let n := varintWritten r
    let encoded := buf.extract 0 n.toNat
    IO.println s!"varint_encode {i} {n.toNat}{showU8s encoded}"
    match Oak.Stdlib.Varint.varint_decode encoded 0 fuel with
    | none => IO.println s!"varint_decode {i} none"
    | some d =>
      let back := varintValue d
      IO.println s!"varint_decode {i} {back.value.toNat} {back.next.toNat}"

def bytesLines (i : Nat) (src : Array UInt8) : IO Unit := do
  match Oak.Stdlib.Encoding.hex_encode (Array.replicate 64 (0 : UInt8)) src false fuel with
  | none => IO.println s!"hex_encode {i} none"; IO.println s!"hex_decode {i} none"
  | some (r, hex) =>
    let n := encodingValue r
    let enc := hex.extract 0 n.toNat
    IO.println s!"hex_encode {i} {n.toNat}{showU8s enc}"
    match Oak.Stdlib.Encoding.hex_decode (Array.replicate 32 (0 : UInt8)) enc fuel with
    | none => IO.println s!"hex_decode {i} none"
    | some (r2, back) =>
      let m := encodingValue r2
      IO.println s!"hex_decode {i} {m.toNat}{showU8s (back.extract 0 m.toNat)}"
  match Oak.Stdlib.Encoding.base64_encode (Array.replicate 64 (0 : UInt8)) src false true fuel with
  | none => IO.println s!"base64_encode {i} none"; IO.println s!"base64_decode {i} none"
  | some (r, b64) =>
    let n := encodingValue r
    let enc := b64.extract 0 n.toNat
    IO.println s!"base64_encode {i} {n.toNat}{showU8s enc}"
    match Oak.Stdlib.Encoding.base64_decode (Array.replicate 48 (0 : UInt8)) enc false fuel with
    | none => IO.println s!"base64_decode {i} none"
    | some (r2, back) =>
      let m := encodingValue r2
      IO.println s!"base64_decode {i} {m.toNat}{showU8s (back.extract 0 m.toNat)}"

def randomLine (i : Nat) (seed : UInt64) : IO Unit := do
  match Oak.Stdlib.Random.random_seed seed fuel with
  | none => IO.println s!"random {i} none"
  | some st =>
    let mut state : Array Oak.Stdlib.Random.Xoshiro := #[st]
    let mut line := s!"random {i}"
    for _ in [0:8] do
      match Oak.Stdlib.Random.random_next state fuel with
      | none => line := line ++ " none"
      | some (v, st') =>
        line := line ++ " " ++ toString v.toNat
        state := st'
    IO.println line

def hashLines (i : Nat) (src : Array UInt8) : IO Unit := do
  match Oak.Stdlib.Hash.crc32c src fuel with
  | none => IO.println s!"crc32c {i} none"
  | some v => IO.println s!"crc32c {i} {v.toNat}"
  match Oak.Stdlib.Hash.sha256 src (Array.replicate 32 (0 : UInt8)) fuel with
  | none => IO.println s!"sha256 {i} none"
  | some (_, out) => IO.println s!"sha256 {i}{showU8s out}"

def bitsF64 (x : Float) : Nat := if x.isNaN then 9221120237041090560 else x.toBits.toNat
def bitsF32 (x : Float32) : Nat := if x.isNaN then 2143289344 else x.toBits.toNat
def showF64 (r : Option Float) : String := match r with | some x => " " ++ toString (bitsF64 x) | none => " none"
def showF32 (r : Option Float32) : String := match r with | some x => " " ++ toString (bitsF32 x) | none => " none"

def floatWritten (r : Oak.Stdlib.Float.Result_u32_FloatError) : UInt32 :=
  match r with
  | .Ok n => n
  | .Err _ => 0

def floatCode (e : Oak.Stdlib.Float.FloatError) : Nat :=
  match e with
  | .InvalidSyntax => 1
  | .OutOfRange => 2
  | .DestinationTooSmall => 3

def f64Lines (i : Nat) (bits : UInt64) : IO Unit := do
  let x := Float.ofBits bits
  match Oak.Stdlib.Float.float_format (Array.replicate 40 (0 : UInt8)) x fuel with
  | none => IO.println s!"float_format {i} none"
  | some (r, txt) =>
    let n := floatWritten r
    IO.println s!"float_format {i} {n.toNat}{showU8s (txt.extract 0 n.toNat)}"
  match Oak.Stdlib.Float.float_format_fixed (Array.replicate 40 (0 : UInt8)) x 3 fuel with
  | none => IO.println s!"float_format_fixed {i} none"
  | some (r, txt) =>
    let n := floatWritten r
    IO.println s!"float_format_fixed {i} {n.toNat}{showU8s (txt.extract 0 n.toNat)}"
  IO.println s!"math_exp {i}{showF64 (Oak.Stdlib.Math.exp x fuel)}"
  IO.println s!"math_exp2 {i}{showF64 (Oak.Stdlib.Math.exp2 x fuel)}"
  IO.println s!"math_log {i}{showF64 (Oak.Stdlib.Math.log x fuel)}"
  IO.println s!"math_log2 {i}{showF64 (Oak.Stdlib.Math.log2 x fuel)}"
  IO.println s!"math_expm1 {i}{showF64 (Oak.Stdlib.Math.expm1 x fuel)}"
  IO.println s!"math_log1p {i}{showF64 (Oak.Stdlib.Math.log1p x fuel)}"
  IO.println s!"math_sin {i}{showF64 (Oak.Stdlib.Math.sin x fuel)}"
  IO.println s!"math_cos {i}{showF64 (Oak.Stdlib.Math.cos x fuel)}"
  IO.println s!"math_tan {i}{showF64 (Oak.Stdlib.Math.tan x fuel)}"
  IO.println s!"math_tanh {i}{showF64 (Oak.Stdlib.Math.tanh x fuel)}"
  IO.println s!"math_atan {i}{showF64 (Oak.Stdlib.Math.atan x fuel)}"

def f32Lines (i : Nat) (bits : UInt32) : IO Unit := do
  let x := Float32.ofBits bits
  match Oak.Stdlib.Float.float_format_f32 (Array.replicate 40 (0 : UInt8)) x fuel with
  | none => IO.println s!"float_format_f32 {i} none"
  | some (r, txt) =>
    let n := floatWritten r
    IO.println s!"float_format_f32 {i} {n.toNat}{showU8s (txt.extract 0 n.toNat)}"
  IO.println s!"math_exp_f32 {i}{showF32 (Oak.Stdlib.Math.exp_f32 x fuel)}"
  IO.println s!"math_sin_f32 {i}{showF32 (Oak.Stdlib.Math.sin_f32 x fuel)}"

def parseLines (i : Nat) (src : Array UInt8) : IO Unit := do
  match Oak.Stdlib.Float.float_parse src fuel with
  | none => IO.println s!"float_parse {i} none"
  | some (.Ok v) => IO.println s!"float_parse {i} 0 {bitsF64 v}"
  | some (.Err e) => IO.println s!"float_parse {i} {floatCode e} {bitsF64 0.0}"
  match Oak.Stdlib.Float.float_parse_f32 src fuel with
  | none => IO.println s!"float_parse_f32 {i} none"
  | some (.Ok v) => IO.println s!"float_parse_f32 {i} 0 {bitsF32 v}"
  | some (.Err e) => IO.println s!"float_parse_f32 {i} {floatCode e} {bitsF32 (0.0 : Float32)}"

def kernelLines (i : Nat) (xs : Array Float32) : IO Unit := do
  let ys := xs.reverse
  let wide := xs.map (fun v => v.toFloat)
  IO.println s!"dot_f32 {i}{showF32 (Oak.Stdlib.FloatKernels.dot_f32 xs ys fuel)}"
  IO.println s!"sum_f32 {i}{showF32 (Oak.Stdlib.FloatKernels.sum_f32 xs fuel)}"
  IO.println s!"sum_f64 {i}{showF64 (Oak.Stdlib.FloatKernels.sum_f64 wide fuel)}"
  IO.println s!"max_abs_f32 {i}{showF32 (Oak.Stdlib.FloatKernels.max_abs_f32 xs fuel)}"
  IO.println s!"widen_mean {i}{showF64 (Oak.Stdlib.FloatKernels.widen_mean xs fuel)}"
  match Oak.Stdlib.FloatKernels.quantize_u8 (xs.getD 0 0.0) (Float32.ofBits 1056964608) fuel with
  | none => IO.println s!"quantize_u8 {i} none"
  | some q => IO.println s!"quantize_u8 {i} {q.toNat}"
  match Oak.Stdlib.FloatKernels.axpy_f32 (xs.getD 0 0.0) xs ys fuel with
  | none => IO.println s!"axpy_f32 {i} none"
  | some (_, out) => IO.println (s!"axpy_f32 {i}" ++ String.join (out.toList.map (fun v => " " ++ toString (bitsF32 v))))

def pairLines (i : Nat) (xb yb : UInt64) : IO Unit := do
  let x := Float.ofBits xb
  let y := Float.ofBits yb
  IO.println s!"math_pow {i}{showF64 (Oak.Stdlib.Math.pow x y fuel)}"
  IO.println s!"math_atan2 {i}{showF64 (Oak.Stdlib.Math.atan2 y x fuel)}"

def textLines (i : Nat) (src : Array UInt8) : IO Unit := do
  match Oak.Stdlib.Strings.utf8_validate src fuel with
  | none => IO.println s!"utf8_validate {i} none"
  | some ok => IO.println s!"utf8_validate {i} {if ok then 1 else 0}"
  match Oak.Stdlib.Strings.utf8_count src fuel with
  | none => IO.println s!"utf8_count {i} none"
  | some (.Ok v) => IO.println s!"utf8_count {i} 0 {v.toNat}"
  | some (.Err _) => IO.println s!"utf8_count {i} 1 0"
  let mut line := s!"utf8_scan {i}"
  let mut pos : UInt32 := 0
  let mut more := true
  let mut steps := 0
  while more && steps < 64 do
    match Oak.Stdlib.Strings.utf8_decode src pos fuel with
    | none => line := line ++ " none"; more := false
    | some (.Ok item) =>
      line := line ++ s!" {item.value.toNat} {item.next.toNat}"
      pos := item.next
      if pos.toNat >= src.size then more := false
    | some (.Err _) => line := line ++ " 999"; more := false
    steps := steps + 1
  IO.println line

def graphemeLine (i : Nat) (src : Array UInt8) : IO Unit := do
  let mut line := s!"grapheme {i}"
  let mut pos : UInt32 := 0
  let mut steps := 0
  while pos.toNat < src.size && steps < 64 do
    match Oak.Stdlib.Grapheme.grapheme_next src pos fuel with
    | none => line := line ++ " none"; pos := src.size.toUInt32
    | some next => line := line ++ s!" {next.toNat}"; pos := next
    steps := steps + 1
  IO.println line

def normWritten (r : Oak.Stdlib.Normalize.Result_u32_NormalizeError) : UInt32 :=
  match r with
  | .Ok n => n
  | .Err _ => 0

def normLines (i : Nat) (src : Array UInt8) : IO Unit := do
  match Oak.Stdlib.Normalize.normalize_nfc (Array.replicate 96 (0 : UInt8)) src fuel with
  | none => IO.println s!"normalize_nfc {i} none"
  | some (r, out) =>
    let n := normWritten r
    IO.println s!"normalize_nfc {i} {n.toNat}{showU8s (out.extract 0 n.toNat)}"
  match Oak.Stdlib.Normalize.normalize_nfd (Array.replicate 96 (0 : UInt8)) src fuel with
  | none => IO.println s!"normalize_nfd {i} none"
  | some (r, out) =>
    let n := normWritten r
    IO.println s!"normalize_nfd {i} {n.toNat}{showU8s (out.extract 0 n.toNat)}"
  match Oak.Stdlib.Normalize.normalize_is_nfc src fuel with
  | none => IO.println s!"normalize_is_nfc {i} none"
  | some ok => IO.println s!"normalize_is_nfc {i} {if ok then 1 else 0}"

def showRange (r : Oak.Stdlib.Url.UrlRange) : String :=
  s!" {if r.present then 1 else 0} {r.start.toNat} {r.end_.toNat}"

def urlLine (i : Nat) (src : Array UInt8) : IO Unit := do
  match Oak.Stdlib.Url.url_parse src fuel with
  | none => IO.println s!"url_parse {i} none"
  | some (.Ok u) => IO.println (s!"url_parse {i} 0" ++ showRange u.scheme ++ showRange u.userinfo ++ showRange u.host ++ showRange u.port ++ showRange u.path ++ showRange u.query ++ showRange u.fragment)
  | some (.Err _) => IO.println s!"url_parse {i} 1"

def pathWritten (r : Oak.Stdlib.Path.Result_u32_PathError) : UInt32 :=
  match r with
  | .Ok n => n
  | .Err _ => 0

def pathLine (i : Nat) (src : Array UInt8) : IO Unit := do
  match Oak.Stdlib.Path.path_clean (Array.replicate 32 (0 : UInt8)) src fuel with
  | none => IO.println s!"path_clean {i} none"
  | some (r, out) =>
    let n := pathWritten r
    IO.println s!"path_clean {i} {n.toNat}{showU8s (out.extract 0 n.toNat)}"

def main : IO Unit := do
`)
	for i, items := range c.sortInputs {
		arr := leanU32Array(items)
		fmt.Fprintf(&b, "  IO.println (showSort \"sort_heap %d\" (Oak.Stdlib.SortU32.sort_u32_heap %s fuel))\n", i, arr)
		fmt.Fprintf(&b, "  IO.println (showSort \"sort_span %d\" (Oak.Stdlib.SortU32.sort_u32_span %s fuel))\n", i, arr)
		fmt.Fprintf(&b, "  IO.println (showSort \"sort_insertion %d\" (Oak.Stdlib.SortU32.sort_u32_insertion %s fuel))\n", i, arr)
	}
	for i, v := range c.varintValues {
		fmt.Fprintf(&b, "  varintLines %d (%d : UInt64)\n", i, v)
	}
	for i, src := range c.bytesInputs {
		fmt.Fprintf(&b, "  bytesLines %d %s\n", i, leanU8Array(src))
	}
	for i, seed := range c.seeds {
		fmt.Fprintf(&b, "  randomLine %d (%d : UInt64)\n", i, seed)
	}
	for i, src := range c.hashInputs {
		fmt.Fprintf(&b, "  hashLines %d %s\n", i, leanU8Array(src))
	}
	for i, bits := range c.f64Bits {
		fmt.Fprintf(&b, "  f64Lines %d (%d : UInt64)\n", i, bits)
	}
	for i, bits := range c.f32Bits {
		fmt.Fprintf(&b, "  f32Lines %d (%d : UInt32)\n", i, bits)
	}
	for i, text := range c.floatTexts {
		fmt.Fprintf(&b, "  parseLines %d %s\n", i, leanU8Array([]byte(text)))
	}
	for i, vec := range c.kernelVecs {
		fmt.Fprintf(&b, "  kernelLines %d %s\n", i, leanF32Array(vec))
	}
	for i, pair := range c.mathPairs {
		fmt.Fprintf(&b, "  pairLines %d (%d : UInt64) (%d : UInt64)\n", i, pair[0], pair[1])
	}
	for i, src := range c.textInputs {
		fmt.Fprintf(&b, "  textLines %d %s\n", i, leanU8Array(src))
	}
	for i, src := range c.graphInputs {
		fmt.Fprintf(&b, "  graphemeLine %d %s\n", i, leanU8Array(src))
	}
	for i, src := range c.normInputs {
		fmt.Fprintf(&b, "  normLines %d %s\n", i, leanU8Array(src))
	}
	for i, src := range c.urlInputs {
		fmt.Fprintf(&b, "  urlLine %d %s\n", i, leanU8Array([]byte(src)))
	}
	for i, src := range c.pathInputs {
		fmt.Fprintf(&b, "  pathLine %d %s\n", i, leanU8Array([]byte(src)))
	}
	return b.String()
}
