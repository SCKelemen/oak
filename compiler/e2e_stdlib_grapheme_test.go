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

// oakByteArray renders bytes as an Oak fixed-array literal of u8.
func graphemeByteArray(name string, data []byte) string {
	parts := make([]string, len(data))
	for i, b := range data {
		parts[i] = strconv.Itoa(int(b))
	}
	if len(data) == 0 {
		return fmt.Sprintf("  %s: [1]u8\n", name)
	}
	return fmt.Sprintf("  %s: [%d]u8 = [%d]u8{ %s }\n", name, len(data), len(data), strings.Join(parts, ", "))
}

// oakClusterCheck emits Oak that walks the clusters of `name` and compares
// the boundary chain with `ends` (byte offsets), failing with `code`.
func oakClusterCheck(name string, text []byte, ends []int, code int) string {
	var b strings.Builder
	b.WriteString(graphemeByteArray(name, text))
	b.WriteString("  true ? {\n")
	fmt.Fprintf(&b, "    v: []u8 = view(&%s)\n", name)
	if len(text) == 0 {
		b.WriteString("    empty: []u8 = v[u32(0):u32(0)]\n")
		fmt.Fprintf(&b, "    grapheme_count(empty) == u32(0) && grapheme_next(empty, u32(0)) == u32(0) ? { } | { fail = u32(%d) }\n", code)
	} else {
		b.WriteString("    pos: u32 = 0\n")
		for _, end := range ends {
			fmt.Fprintf(&b, "    pos = grapheme_next(v, pos)\n    pos == u32(%d) ? { } | { fail = u32(%d) }\n", end, code)
		}
		fmt.Fprintf(&b, "    grapheme_count(v) == u32(%d) ? { } | { fail = u32(%d) }\n", len(ends), code)
		for _, end := range ends {
			fmt.Fprintf(&b, "    grapheme_is_boundary(v, u32(%d)) ? { } | { fail = u32(%d) }\n", end, code)
		}
	}
	b.WriteString("  }\n")
	return b.String()
}

// clusterEnds encodes the scalar clusters as UTF-8 and returns the text and
// the byte offset at which each cluster ends.
func clusterEnds(clusters [][]rune) ([]byte, []int) {
	var text []byte
	var ends []int
	for _, cluster := range clusters {
		for _, r := range cluster {
			text = utf8.AppendRune(text, r)
		}
		ends = append(ends, len(text))
	}
	return text, ends
}

func TestE2EStdlibGrapheme(t *testing.T) {
	cases := []struct {
		name     string
		clusters [][]rune
	}{
		{"ascii", [][]rune{{'a'}, {'b'}, {'c'}}},
		{"crlf", [][]rune{{'a'}, {'\r', '\n'}, {'b'}, {'\n'}, {'\r'}}},
		{"control", [][]rune{{0x01}, {0x0301}, {'x', 0x0301}}},
		{"combining", [][]rune{{'e', 0x0301, 0x0323}, {'a'}}},
		{"hangul_jamo", [][]rune{{0x1100, 0x1161, 0x11A8}, {0x1100, 0x1161}, {0xAC00, 0x11A8}, {0xAC01, 0x11A8}, {0x1160}}},
		{"hangul_break", [][]rune{{0x11A8}, {0x1100}}},
		{"emoji_zwj_family", [][]rune{{0x1F468, 0x200D, 0x1F469, 0x200D, 0x1F467}, {'!'}}},
		{"emoji_modifier", [][]rune{{0x1F44B, 0x1F3FB}, {0x1F44B}}},
		{"flags", [][]rune{{0x1F1FA, 0x1F1F8}, {0x1F1EC, 0x1F1E7}, {0x1F1E6}, {'x'}}},
		{"flag_zwj_not_pictographic", [][]rune{{0x1F1FA, 0x1F1F8, 0x200D}, {0x1F1EC}}},
		{"devanagari_conjunct", [][]rune{{0x0915, 0x094D, 0x0937}, {0x0915}, {0x0937, 0x0903}}},
		{"devanagari_no_linker", [][]rune{{0x0915, 0x0902}, {0x0937}}},
		{"prepend", [][]rune{{0x0600, 'a', 0x0301}, {'b'}}},
		{"spacing_mark", [][]rune{{'k', 0x0903}, {'a'}}},
		{"zwj_then_letter", [][]rune{{0x1F600, 0x200D}, {'a'}}},
		{"pictographic_extend_zwj", [][]rune{{0x1F600, 0x0301, 0x200D, 0x1F601}, {'a'}}},
		{"empty", nil},
	}
	var body strings.Builder
	for i, c := range cases {
		text, ends := clusterEnds(c.clusters)
		body.WriteString(fmt.Sprintf("  // %s\n", c.name))
		body.WriteString(oakClusterCheck(fmt.Sprintf("t%d", i), text, ends, 100+i))
	}
	// Ill-formed UTF-8: each undecodable byte is its own cluster, a mark
	// after a well-formed base still attaches.
	invalid := []byte{0xFF, 'a', 0xCC, 0x81, 0xC0, 0xAF, 'b'}
	body.WriteString(oakClusterCheck("bad", invalid, []int{1, 4, 5, 6, 7}, 90))
	body.WriteString("  grapheme_is_boundary(view(&bad), u32(2)) ? { fail = u32(91) }\n")
	body.WriteString("  grapheme_is_boundary(view(&bad), u32(99)) ? { fail = u32(92) }\n")
	body.WriteString("  grapheme_class(u32(65)) == u32(0) && grapheme_gcb(grapheme_class(u32(13))) == GB_CR && grapheme_gcb(grapheme_class(u32(44033))) == GB_LVT ? { } | { fail = u32(93) }\n")
	body.WriteString("  grapheme_incb(grapheme_class(u32(2381))) == INCB_LINKER && grapheme_incb(grapheme_class(u32(2325))) == INCB_CONSONANT && grapheme_is_pictographic(grapheme_class(u32(128512))) ? { } | { fail = u32(94) }\n")
	body.WriteString("  grapheme_class(u32(1114112)) == u32(0) && grapheme_class(u32(4294967295)) == u32(0) ? { } | { fail = u32(95) }\n")
	src := "import(std)\nmain: (): i32 {\n  fail: u32 = 0\n" + body.String() + "  fail == u32(0) ? { 42 } | { i32_bits_u32(fail) }\n}\n"
	code, abnormal := buildAndRun(t, "stdlib_grapheme", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// TestE2EStdlibGraphemeConformance runs every line of the Unicode 17.0.0
// GraphemeBreakTest.txt through the compiled segmenter: the boundary chain
// must reproduce the ÷ marks exactly.
func TestE2EStdlibGraphemeConformance(t *testing.T) {
	path := filepath.Join("..", "stdlib", "testdata", "GraphemeBreakTest-17.0.0.txt")
	file, err := os.Open(path)
	if err != nil {
		t.Fatal(err)
	}
	defer file.Close()
	var body strings.Builder
	count := 0
	scanner := bufio.NewScanner(file)
	for scanner.Scan() {
		line := scanner.Text()
		if i := strings.IndexByte(line, '#'); i >= 0 {
			line = line[:i]
		}
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}
		fields := strings.Fields(line)
		if fields[0] != "÷" || fields[len(fields)-1] != "÷" {
			t.Fatalf("unexpected line shape: %q", line)
		}
		var text []byte
		var ends []int
		for i := 1; i < len(fields); i++ {
			switch fields[i] {
			case "÷":
				ends = append(ends, len(text))
			case "×":
			default:
				value, err := strconv.ParseUint(fields[i], 16, 32)
				if err != nil {
					t.Fatalf("bad scalar %q in %q", fields[i], line)
				}
				text = utf8.AppendRune(text, rune(value))
			}
		}
		body.WriteString(oakClusterCheck(fmt.Sprintf("c%d", count), text, ends, 1000+count))
		count++
	}
	if err := scanner.Err(); err != nil {
		t.Fatal(err)
	}
	if count < 700 {
		t.Fatalf("only %d conformance lines parsed", count)
	}
	src := "import(std)\nmain: (): i32 {\n  fail: u32 = 0\n" + body.String() + "  fail == u32(0) ? { 42 } | { i32_bits_u32(fail % u32(200) + u32(1)) }\n}\n"
	code, abnormal := buildAndRun(t, "stdlib_grapheme_conformance", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v): conformance line index mod 200 is exit-1 (%d lines)", code, abnormal, count)
	}
}

func TestE2EStdlibGraphemeQualified(t *testing.T) {
	src := `package main
import("grapheme")
main: (): i32 {
  text: [7]u8 = [7]u8{ 240, 159, 135, 186, 240, 159, 135 }
  flag: [8]u8 = [8]u8{ 240, 159, 135, 186, 240, 159, 135, 184 }
  first: u32 = grapheme.grapheme_next(view(&flag), u32(0))
  count: u32 = grapheme.grapheme_count(view(&text))
  first == u32(8) && count == u32(4) && grapheme.grapheme_gcb(grapheme.grapheme_class(u32(127482))) == grapheme.GB_REGIONAL_INDICATOR ? { 42 } | { 0 }
}
`
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/grapheme_qualified\noak 0.1.0\n",
		"main.oak": src,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
