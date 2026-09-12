package compiler

import (
	"bufio"
	"fmt"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
	"unicode/utf8"
)

// normalizeByteArray renders a byte slice as an Oak fixed array binding.
func normalizeByteArray(name string, data []byte) string {
	var b strings.Builder
	fmt.Fprintf(&b, "  %s: [%d]u8 = [%d]u8{", name, len(data), len(data))
	for i, v := range data {
		if i > 0 {
			b.WriteString(", ")
		}
		b.WriteString(strconv.Itoa(int(v)))
	}
	b.WriteString("}\n")
	return b.String()
}

// oakNormalizeCheck emits a check that `form` of `input` is exactly `want`,
// adding `code` to `fail` on the first mismatch.
func oakNormalizeCheck(name string, form string, input, want []byte, code int) string {
	var b strings.Builder
	b.WriteString(normalizeByteArray(name+"_in", input))
	b.WriteString(normalizeByteArray(name+"_want", want))
	fmt.Fprintf(&b, "  fail == u32(0) && !normalize_conf_check(%s, view(&%s_in), view(&%s_want)) ? { fail = u32(%d) }\n", form, name, name, code)
	return b.String()
}

// normalizeHelpers is the shared Oak prologue: one check that writes a form
// into caller storage and compares it with the expected bytes.
const normalizeHelpers = `
normalize_conf_check: (form: u32, input: []u8, want: []u8): Bool {
  out: [256]u8
  n: u32 = 0
  ok: Bool = true
  true ? {
    dst: [*]u8 = span(&out)
    result: Result[u32, NormalizeError] = normalize_form(dst, input, form)
    ok = normalize_ok(result)
    n = normalize_written(result)
  }
  whole: []u8 = view(&out)
  ok && n == len(want) && bytes_equal(whole[u32(0):n], want)
}
`

func TestE2EStdlibNormalize(t *testing.T) {
	type tc struct {
		form  string
		input string
		want  string
	}
	r := func(values ...rune) string { return string(values) }
	cases := []tc{
		// é: composed to decomposed and back.
		{"NORMALIZE_NFD", r(0x00E9), r('e', 0x0301)},
		{"NORMALIZE_NFC", r('e', 0x0301), r(0x00E9)},
		{"NORMALIZE_NFC", r(0x00E9), r(0x00E9)},
		// Hangul syllables: 각 (LVT) and 가 (LV) decompose to jamo and recompose.
		{"NORMALIZE_NFD", r(0xAC01), r(0x1100, 0x1161, 0x11A8)},
		{"NORMALIZE_NFC", r(0x1100, 0x1161, 0x11A8), r(0xAC01)},
		{"NORMALIZE_NFC", r(0x1100, 0x1161), r(0xAC00)},
		// ANGSTROM SIGN is a singleton: NFD gives A + ring, NFC the letter Å (U+00C5).
		{"NORMALIZE_NFD", r(0x212B), r('A', 0x030A)},
		{"NORMALIZE_NFC", r(0x212B), r(0x00C5)},
		// Composition exclusion: U+0958 decomposes and must not recompose.
		{"NORMALIZE_NFD", r(0x0958), r(0x0915, 0x093C)},
		{"NORMALIZE_NFC", r(0x0958), r(0x0915, 0x093C)},
		// Canonical ordering: cedilla (202) before acute (230) whatever the input
		// order; composition then reaches past the cedilla to make á.
		{"NORMALIZE_NFD", r('a', 0x0301, 0x0327), r('a', 0x0327, 0x0301)},
		{"NORMALIZE_NFC", r('a', 0x0301, 0x0327), r(0x00E1, 0x0327)},
		// Blocking: a second acute (230) is blocked by the first (230 ≥ 230); a
		// mark below (220) does not block the acute.
		{"NORMALIZE_NFC", r('a', 0x0301, 0x0301), r(0x00E1, 0x0301)},
		{"NORMALIZE_NFC", r('a', 0x0316, 0x0301), r(0x00E1, 0x0316)},
		// Compatibility: ﬁ ligature and superscript two; NFD leaves them alone.
		{"NORMALIZE_NFKD", r(0xFB01), "fi"},
		{"NORMALIZE_NFKC", r(0x00B2), "2"},
		{"NORMALIZE_NFD", r(0xFB01), r(0xFB01)},
		// ASCII is a fixed point of every form; so is the empty text.
		{"NORMALIZE_NFKC", "hello, world", "hello, world"},
		{"NORMALIZE_NFD", "", ""},
	}
	var body strings.Builder
	for i, c := range cases {
		body.WriteString(oakNormalizeCheck(fmt.Sprintf("c%d", i), c.form, []byte(c.input), []byte(c.want), 100+i))
	}
	src := "import(std)\n" + normalizeHelpers + "main: (): i32 {\n  fail: u32 = 0\n" + body.String() + `
  // Quick checks and sizes.
  composed: [2]u8 = [2]u8{ 195, 169 }
  decomposed: [3]u8 = [3]u8{ 101, 204, 129 }
  fail == u32(0) && !(normalize_is_nfc(view(&composed)) && !normalize_is_nfd(view(&composed))) ? { fail = u32(200) }
  fail == u32(0) && !(normalize_is_nfd(view(&decomposed)) && !normalize_is_nfc(view(&decomposed))) ? { fail = u32(201) }
  fail == u32(0) && normalize_written(normalize_nfd_size(view(&composed))) != u32(3) ? { fail = u32(202) }
  fail == u32(0) && normalize_written(normalize_nfc_size(view(&decomposed))) != u32(2) ? { fail = u32(203) }
  // MAYBE path: a base followed by a combining mark that does compose is not NFC.
  fail == u32(0) && normalize_is_nfc(view(&decomposed)) ? { fail = u32(204) }
  // A short destination fails with DestinationTooSmall (code 2); invalid UTF-8 with InvalidEncoding (1).
  tiny: [1]u8
  true ? {
    d: [*]u8 = span(&tiny)
    fail == u32(0) && normalize_failure(normalize_nfd(d, view(&composed))) != u32(2) ? { fail = u32(205) }
  }
  broken: [2]u8 = [2]u8{ 195, 40 }
  big: [8]u8
  true ? {
    b: [*]u8 = span(&big)
    fail == u32(0) && normalize_failure(normalize_nfc(b, view(&broken))) != u32(1) ? { fail = u32(206) }
  }
  fail == u32(0) && normalize_is_nfc(view(&broken)) ? { fail = u32(207) }
  // ccc and composition lookups.
  fail == u32(0) && normalize_ccc(u32(769)) != u32(230) ? { fail = u32(208) }
  fail == u32(0) && normalize_compose_pair(u32(101), u32(769)) != u32(233) ? { fail = u32(209) }
  fail == u32(0) && normalize_compose_pair(u32(4352), u32(4449)) != u32(44032) ? { fail = u32(210) }
  fail == u32(0) ? { 42 } | { i32_bits_u32(fail) }
}
`
	code, abnormal := buildAndRun(t, "stdlib_normalize", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v): failing check code", code, abnormal)
	}
}

// normalizeConformanceCase is one line of NormalizationTest.txt: the five
// columns as UTF-8.
type normalizeConformanceCase struct {
	part    int
	columns [5][]byte
}

func readNormalizationTest(t *testing.T) []normalizeConformanceCase {
	path := filepath.Join("..", "stdlib", "testdata", "NormalizationTest-17.0.0.txt")
	file, err := os.Open(path)
	if err != nil {
		t.Fatal(err)
	}
	defer file.Close()
	var cases []normalizeConformanceCase
	part := -1
	scanner := bufio.NewScanner(file)
	scanner.Buffer(make([]byte, 1<<20), 1<<20)
	for scanner.Scan() {
		line := scanner.Text()
		if strings.HasPrefix(line, "@Part") {
			part, _ = strconv.Atoi(strings.TrimSpace(strings.Fields(line)[0][5:]))
			continue
		}
		if i := strings.IndexByte(line, '#'); i >= 0 {
			line = line[:i]
		}
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}
		fields := strings.Split(line, ";")
		if len(fields) < 5 {
			t.Fatalf("unexpected line shape: %q", line)
		}
		var c normalizeConformanceCase
		c.part = part
		for i := 0; i < 5; i++ {
			for _, hex := range strings.Fields(fields[i]) {
				value, err := strconv.ParseUint(hex, 16, 32)
				if err != nil {
					t.Fatalf("bad scalar %q in %q", hex, line)
				}
				c.columns[i] = utf8.AppendRune(c.columns[i], rune(value))
			}
		}
		cases = append(cases, c)
	}
	if err := scanner.Err(); err != nil {
		t.Fatal(err)
	}
	if len(cases) < 19000 {
		t.Fatalf("only %d conformance lines parsed", len(cases))
	}
	return cases
}

// normalizeConformanceProgram serializes cases as a byte table (five
// length-prefixed columns each) and checks the twelve invariants of
// NormalizationTest.txt for every case: NFC of c1, c2, c3 is c2; of c4, c5 is
// c4; NFD of c1, c2, c3 is c3; of c4, c5 is c5; NFKC of every column is c4;
// NFKD of every column is c5. A failure exits with 1 + the case index mod 200.
func normalizeConformanceProgram(cases []normalizeConformanceCase) string {
	var table []byte
	for _, c := range cases {
		for i := 0; i < 5; i++ {
			table = append(table, byte(len(c.columns[i])))
			table = append(table, c.columns[i]...)
		}
	}
	var b strings.Builder
	b.WriteString("import(std)\n")
	b.WriteString(normalizeHelpers)
	b.WriteString(normalizeByteArray("CONF_TABLE", table))
	fmt.Fprintf(&b, "CONF_CASES: u32 = %d\n", len(cases))
	b.WriteString(`
main: (): i32 {
  table: []u8 = view(&CONF_TABLE)
  starts: [5]u32
  lengths: [5]u32
  at: u32 = 0
  index: u32 = 0
  fail: u32 = 0
  while index < CONF_CASES && fail == u32(0) {
    column: u32 = 0
    while column < u32(5) {
      lengths[column] = u32(table[at])
      starts[column] = at + u32(1)
      at = at + u32(1) + lengths[column]
      column = column + u32(1)
    }
    c1: []u8 = table[starts[0]:starts[0] + lengths[0]]
    c2: []u8 = table[starts[1]:starts[1] + lengths[1]]
    c3: []u8 = table[starts[2]:starts[2] + lengths[2]]
    c4: []u8 = table[starts[3]:starts[3] + lengths[3]]
    c5: []u8 = table[starts[4]:starts[4] + lengths[4]]
    ok: Bool = normalize_conf_check(NORMALIZE_NFC, c1, c2) && normalize_conf_check(NORMALIZE_NFC, c2, c2) && normalize_conf_check(NORMALIZE_NFC, c3, c2)
    ok = ok && normalize_conf_check(NORMALIZE_NFC, c4, c4) && normalize_conf_check(NORMALIZE_NFC, c5, c4)
    ok = ok && normalize_conf_check(NORMALIZE_NFD, c1, c3) && normalize_conf_check(NORMALIZE_NFD, c2, c3) && normalize_conf_check(NORMALIZE_NFD, c3, c3)
    ok = ok && normalize_conf_check(NORMALIZE_NFD, c4, c5) && normalize_conf_check(NORMALIZE_NFD, c5, c5)
    ok = ok && normalize_conf_check(NORMALIZE_NFKC, c1, c4) && normalize_conf_check(NORMALIZE_NFKC, c2, c4) && normalize_conf_check(NORMALIZE_NFKC, c3, c4)
    ok = ok && normalize_conf_check(NORMALIZE_NFKC, c4, c4) && normalize_conf_check(NORMALIZE_NFKC, c5, c4)
    ok = ok && normalize_conf_check(NORMALIZE_NFKD, c1, c5) && normalize_conf_check(NORMALIZE_NFKD, c2, c5) && normalize_conf_check(NORMALIZE_NFKD, c3, c5)
    ok = ok && normalize_conf_check(NORMALIZE_NFKD, c4, c5) && normalize_conf_check(NORMALIZE_NFKD, c5, c5)
    // The quick checks agree with the columns: c2 is NFC, c3 is NFD, c4 is NFKC, c5 is NFKD.
    ok = ok && normalize_is_nfc(c2) && normalize_is_nfd(c3) && normalize_is_nfkc(c4) && normalize_is_nfkd(c5)
    !ok ? { fail = index + u32(1) }
    index = index + u32(1)
  }
  fail == u32(0) ? { 42 } | { i32_bits_u32((fail - u32(1)) % u32(200) + u32(1)) }
}
`)
	return b.String()
}

// TestE2EStdlibNormalizeConformance runs every line of the Unicode 17.0.0
// NormalizationTest.txt through the compiled normalizer in chunks.
func TestE2EStdlibNormalizeConformance(t *testing.T) {
	skipInShort(t)
	cases := readNormalizationTest(t)
	const chunkBytes = 96 * 1024
	start := 0
	chunk := 0
	for start < len(cases) {
		end := start
		size := 0
		for end < len(cases) {
			n := 5
			for i := 0; i < 5; i++ {
				n += len(cases[end].columns[i])
			}
			if size+n > chunkBytes && end > start {
				break
			}
			size += n
			end++
		}
		src := normalizeConformanceProgram(cases[start:end])
		code, abnormal := buildAndRun(t, fmt.Sprintf("stdlib_normalize_conformance_%d", chunk), src)
		if abnormal || code != 42 {
			index := start + code - 1
			for index < end && (index-start)%200 != code-1 {
				index++
			}
			t.Fatalf("chunk %d (cases %d..%d): exit=(%d,%v); first failing case is index %d mod 200 within the chunk", chunk, start, end, code, abnormal, code-1)
		}
		start = end
		chunk++
	}
	t.Logf("%d conformance lines in %d chunks", len(cases), chunk)
}

func TestE2EStdlibNormalizeQualified(t *testing.T) {
	src := `package main
import("normalize")
main: (): i32 {
  text: [3]u8 = [3]u8{ 101, 204, 129 }
  out: [4]u8
  n: u32 = 0
  true ? {
    dst: [*]u8 = span(&out)
    n = normalize.normalize_written(normalize.normalize_nfc(dst, view(&text)))
  }
  n == u32(2) && out[0] == u8(195) && out[1] == u8(169) && normalize.normalize_ccc(u32(769)) == u32(230) ? { 42 } | { 0 }
}
`
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/normalize_qualified\noak 0.1.0\n",
		"main.oak": src,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
