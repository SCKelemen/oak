package compiler

import (
	"fmt"
	"strings"
	"testing"
)

// oakBytes spells a Go string as an Oak text literal, escaping everything
// outside printable ASCII as \xHH so multibyte rows survive verbatim.
func oakBytes(s string) string {
	var b strings.Builder
	b.WriteString(`text_literal("`)
	for i := 0; i < len(s); i++ {
		c := s[i]
		switch {
		case c == '\\':
			b.WriteString(`\\`)
		case c == '"':
			b.WriteString(`\"`)
		case c >= 32 && c < 127:
			b.WriteByte(c)
		default:
			fmt.Fprintf(&b, `\x%02X`, c)
		}
	}
	b.WriteString(`")`)
	return b.String()
}

// The tables below are Go's path_test.go and match_test.go rows.
var pathCleanRows = [][2]string{
	{"", "."}, {"abc", "abc"}, {"abc/def", "abc/def"}, {"a/b/c", "a/b/c"}, {".", "."}, {"..", ".."},
	{"../..", "../.."}, {"../../abc", "../../abc"}, {"/abc", "/abc"}, {"/", "/"},
	{"abc/", "abc"}, {"abc/def/", "abc/def"}, {"a/b/c/", "a/b/c"}, {"./", "."}, {"../", ".."},
	{"../../", "../.."}, {"/abc/", "/abc"},
	{"abc//def//ghi", "abc/def/ghi"}, {"//abc", "/abc"}, {"///abc", "/abc"}, {"//abc//", "/abc"}, {"abc//", "abc"},
	{"abc/./def", "abc/def"}, {"/./abc/def", "/abc/def"}, {"abc/.", "abc"},
	{"abc/def/ghi/../jkl", "abc/def/jkl"}, {"abc/def/../ghi/../jkl", "abc/jkl"}, {"abc/def/..", "abc"},
	{"abc/def/../..", "."}, {"/abc/def/../..", "/"}, {"abc/def/../../..", ".."}, {"/abc/def/../../..", "/"},
	{"abc/def/../../../ghi/jkl/../../../mno", "../../mno"},
	{"abc/./../def", "def"}, {"abc//./../def", "def"}, {"abc/../../././../def", "../../def"},
}

var pathJoinRows = [][3]string{
	{"", "", ""}, {"a", "", "a"}, {"a", "b", "a/b"}, {"", "b", "b"}, {"/", "a", "/a"}, {"/", "", "/"},
	{"a/", "b", "a/b"}, {"a/", "", "a"},
}

var pathExtRows = [][2]string{
	{"path.go", ".go"}, {"path.pb.go", ".go"}, {"a.dir/b", ""}, {"a.dir/b.go", ".go"}, {"a.dir/", ""},
}

// Go spells the base of "" as "."; the range form is empty there.
var pathBaseRows = [][2]string{
	{"", ""}, {".", "."}, {"/.", "."}, {"/", "/"}, {"////", "/"}, {"x/", "x"}, {"abc", "abc"},
	{"abc/def", "def"}, {"a/b/.x", ".x"}, {"a/b/c.", "c."}, {"a/b/c.x", "c.x"},
}

var pathDirRows = [][2]string{
	{"", "."}, {".", "."}, {"/.", "/"}, {"/", "/"}, {"////", "/"}, {"/foo", "/"}, {"x/", "x"},
	{"abc", "."}, {"abc/def", "abc"}, {"abc////def", "abc"}, {"a/b/.x", "a/b"}, {"a/b/c.", "a/b"}, {"a/b/c.x", "a/b"},
}

var pathIsAbsRows = []struct {
	path string
	abs  bool
}{
	{"", false}, {"/", true}, {"/usr/bin/gcc", true}, {"..", false}, {"/a/../bb", true}, {".", false}, {"./", false}, {"lala", false},
}

var pathSplitRows = [][3]string{
	{"a/b", "a/", "b"}, {"a/b/", "a/b/", ""}, {"a/", "a/", ""}, {"a", "", "a"}, {"/", "/", ""},
}

// code: 1 match, 0 mismatch, 2 bad pattern.
var pathMatchRows = []struct {
	pattern, name string
	code          int
}{
	{"abc", "abc", 1}, {"*", "abc", 1}, {"*c", "abc", 1}, {"a*", "a", 1}, {"a*", "abc", 1}, {"a*", "ab/c", 0},
	{"a*/b", "abc/b", 1}, {"a*/b", "a/c/b", 0}, {"a*b*c*d*e*/f", "axbxcxdxe/f", 1}, {"a*b*c*d*e*/f", "axbxcxdxexxx/f", 1},
	{"a*b*c*d*e*/f", "axbxcxdxe/xxx/f", 0}, {"a*b*c*d*e*/f", "axbxcxdxexxx/fff", 0},
	{"a*b?c*x", "abxbbxdbxebxczzx", 1}, {"a*b?c*x", "abxbbxdbxebxczzy", 0},
	{"ab[c]", "abc", 1}, {"ab[b-d]", "abc", 1}, {"ab[e-g]", "abc", 0}, {"ab[^c]", "abc", 0}, {"ab[^b-d]", "abc", 0}, {"ab[^e-g]", "abc", 1},
	{"a\\*b", "a*b", 1}, {"a\\*b", "ab", 0},
	{"a?b", "a☺b", 1}, {"a[^a]b", "a☺b", 1}, {"a???b", "a☺b", 0}, {"a[^a][^a][^a]b", "a☺b", 0},
	{"[a-ζ]*", "α", 1}, {"*[a-ζ]", "A", 0},
	{"a?b", "a/b", 0}, {"a*b", "a/b", 0},
	{"[\\]a]", "]", 1}, {"[\\-]", "-", 1}, {"[x\\-]", "x", 1}, {"[x\\-]", "-", 1}, {"[x\\-]", "z", 0},
	{"[\\-x]", "x", 1}, {"[\\-x]", "-", 1}, {"[\\-x]", "a", 0},
	{"[]a]", "]", 2}, {"[-]", "-", 2}, {"[x-]", "x", 2}, {"[x-]", "-", 2}, {"[x-]", "z", 2},
	{"[-x]", "x", 2}, {"[-x]", "-", 2}, {"[-x]", "a", 2}, {"\\", "a", 2}, {"[a-b-c]", "a", 2},
	{"[", "a", 2}, {"[^", "a", 2}, {"[^bc", "a", 2}, {"a[", "a", 2}, {"a[", "ab", 2}, {"a[", "x", 2}, {"a/b[", "x", 2},
	{"*x", "xxx", 1},
	// Bad patterns are reported even after an early mismatch (Go 1.16+).
	{"a/b[", "a/x", 2}, {"x[", "a", 2},
}

var pathGlobRows = []struct {
	pattern, name string
	code          int
}{
	{"**", "", 1}, {"**", "a", 1}, {"**", "a/b/c", 1}, {"**", "/a/b", 1},
	{"a/**/b", "a/b", 1}, {"a/**/b", "a/x/b", 1}, {"a/**/b", "a/x/y/b", 1}, {"a/**/b", "a/x/y", 0}, {"a/**/b", "b", 0},
	{"**/b", "b", 1}, {"**/b", "x/y/b", 1}, {"**/b", "x/y/c", 0},
	{"a/**", "a", 1}, {"a/**", "a/x", 1}, {"a/**", "a/x/y", 1}, {"a/**", "b/x", 0},
	{"/**/b", "/a/b", 1}, {"/**/b", "a/b", 0}, {"**/b", "/b", 1},
	{"a/*/c", "a/b/c", 1}, {"a/*/c", "a/b/x/c", 0}, {"a/**/*.go", "a/b/c/d.go", 1}, {"a/**/*.go", "a/d.go", 1}, {"a/**/*.go", "a/b/d.rs", 0},
	{"a**/b", "ab/b", 1}, {"a**/b", "a/x/b", 0},
	{"**/[", "a/b", 2}, {"a/**/b[", "a/b", 2},
	{"a/**/**/b", "a/b", 1}, {"a/**/**/b", "a/x/b", 1},
}

func TestE2EStdlibPath(t *testing.T) {
	var b strings.Builder
	b.WriteString(`
import(std)

check_clean: (src: []u8, want: []u8): () {
  buffer: [64]u8
  n: u32 = u32(0)
  true ? {
    dst: [*]u8 = span(&buffer)
    n = path_written(path_clean(dst, src))
  }
  whole: []u8 = view(&buffer)
  assert(n == len(want) && bytes_equal(whole[u32(0):n], want))
}

check_join: (a: []u8, b: []u8, want: []u8): () {
  buffer: [64]u8
  n: u32 = u32(0)
  true ? {
    dst: [*]u8 = span(&buffer)
    n = path_written(path_join(dst, a, b))
  }
  whole: []u8 = view(&buffer)
  assert(n == len(want) && bytes_equal(whole[u32(0):n], want))
}

check_dir: (src: []u8, want: []u8): () {
  buffer: [64]u8
  n: u32 = u32(0)
  true ? {
    dst: [*]u8 = span(&buffer)
    n = path_written(path_dir(dst, src))
  }
  whole: []u8 = view(&buffer)
  assert(n == len(want) && bytes_equal(whole[u32(0):n], want))
}

check_range: (src: []u8, part: PathRange, want: []u8): () {
  assert(part.start <= part.end && part.end <= len(src))
  assert(bytes_equal(src[part.start:part.end], want))
}

main: (): i32 {
`)
	for _, row := range pathCleanRows {
		fmt.Fprintf(&b, "  check_clean(%s, %s)\n", oakBytes(row[0]), oakBytes(row[1]))
	}
	for _, row := range pathJoinRows {
		fmt.Fprintf(&b, "  check_join(%s, %s, %s)\n", oakBytes(row[0]), oakBytes(row[1]), oakBytes(row[2]))
	}
	for _, row := range pathExtRows {
		fmt.Fprintf(&b, "  check_range(%s, path_ext(%s), %s)\n", oakBytes(row[0]), oakBytes(row[0]), oakBytes(row[1]))
	}
	for _, row := range pathBaseRows {
		fmt.Fprintf(&b, "  check_range(%s, path_base(%s), %s)\n", oakBytes(row[0]), oakBytes(row[0]), oakBytes(row[1]))
	}
	for _, row := range pathDirRows {
		fmt.Fprintf(&b, "  check_dir(%s, %s)\n", oakBytes(row[0]), oakBytes(row[1]))
	}
	for _, row := range pathIsAbsRows {
		fmt.Fprintf(&b, "  assert(path_is_abs(%s) == %v)\n", oakBytes(row.path), row.abs)
	}
	for i, row := range pathSplitRows {
		fmt.Fprintf(&b, "  parts%d: PathSplit = path_split(%s)\n", i, oakBytes(row[0]))
		fmt.Fprintf(&b, "  check_range(%s, parts%d.dir, %s)\n", oakBytes(row[0]), i, oakBytes(row[1]))
		fmt.Fprintf(&b, "  check_range(%s, parts%d.file, %s)\n", oakBytes(row[0]), i, oakBytes(row[2]))
	}
	for _, row := range pathMatchRows {
		fmt.Fprintf(&b, "  assert(path_match_code(%s, %s) == u32(%d))\n", oakBytes(row.pattern), oakBytes(row.name), row.code)
	}
	for _, row := range pathGlobRows {
		fmt.Fprintf(&b, "  assert(path_match_glob_code(%s, %s) == u32(%d))\n", oakBytes(row.pattern), oakBytes(row.name), row.code)
	}
	b.WriteString(`
  // Result wrappers and the component iterator.
  assert(path_matched(path_match(text_literal("a*"), text_literal("abc"))))
  assert(!path_matched(path_match(text_literal("a*"), text_literal("b"))))
  assert(path_match_failure(path_match(text_literal("["), text_literal("a"))) == u32(1))
  assert(path_match_failure(path_match_glob(text_literal("**/["), text_literal("a"))) == u32(1))
  assert(path_matched(path_match_glob(text_literal("**/*.oak"), text_literal("stdlib/path.oak"))))
  walk: []u8 = text_literal("//a/bb///c/")
  first: PathRange = option_or[PathRange](path_next_component(walk, u32(0)), path_range(u32(99), u32(99)))
  assert(first.start == u32(2) && first.end == u32(3))
  second: PathRange = option_or[PathRange](path_next_component(walk, first.end), path_range(u32(99), u32(99)))
  assert(second.start == u32(4) && second.end == u32(6))
  third: PathRange = option_or[PathRange](path_next_component(walk, second.end), path_range(u32(99), u32(99)))
  assert(third.start == u32(9) && third.end == u32(10))
  none: PathRange = option_or[PathRange](path_next_component(walk, third.end), path_range(u32(99), u32(99)))
  assert(none.start == u32(99))
  // Short destinations are rejected before the first store.
  small: [2]u8
  true ? {
    s: [*]u8 = span(&small)
    assert(path_failure(path_clean(s, text_literal("abc"))) == u32(2))
    assert(path_failure(path_join(s, text_literal("a"), text_literal("b"))) == u32(2))
    assert(path_failure(path_dir(s, text_literal("abc/d"))) == u32(2))
    assert(path_written(path_clean(s, text_literal(""))) == u32(1))
  }
  assert(small[0] == u8(46) && small[1] == u8(0))
  42
}
`)
	code, abnormal := buildAndRun(t, "stdlib_path", b.String())
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EStdlibPathQualified(t *testing.T) {
	src := `package main
import("path")
main: (): i32 {
  out: [16]u8
  n: u32 = u32(0)
  true ? {
    dst: [*]u8 = span(&out)
    n = path.path_written(path.path_clean(dst, text_literal("a//b/../c/")))
  }
  whole: []u8 = view(&out)
  assert(n == u32(3) && bytes_equal(whole[u32(0):n], text_literal("a/c")))
  ext: path.PathRange = path.path_ext(text_literal("x/y.oak"))
  assert(ext.start == u32(3) && ext.end == u32(7))
  path.path_matched(path.path_match_glob(text_literal("**/*.oak"), text_literal("x/y.oak"))) ? { 42 } | { 0 }
}
`
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/path_qualified\noak 0.1.0\n",
		"main.oak": src,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
