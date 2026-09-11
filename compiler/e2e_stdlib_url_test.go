package compiler

import (
	"fmt"
	"strings"
	"testing"
)

// RFC 3986 Appendix C: reference resolution against the base
// "http://a/b/c/d;p?q". Normal examples (§5.4.1) then abnormal ones (§5.4.2),
// with the strict-parser reading of "http:g".
// https://datatracker.ietf.org/doc/html/rfc3986#section-5.4
var urlResolutionCases = [][2]string{
	{"g:h", "g:h"},
	{"g", "http://a/b/c/g"},
	{"./g", "http://a/b/c/g"},
	{"g/", "http://a/b/c/g/"},
	{"/g", "http://a/g"},
	{"//g", "http://g"},
	{"?y", "http://a/b/c/d;p?y"},
	{"g?y", "http://a/b/c/g?y"},
	{"#s", "http://a/b/c/d;p?q#s"},
	{"g#s", "http://a/b/c/g#s"},
	{"g?y#s", "http://a/b/c/g?y#s"},
	{";x", "http://a/b/c/;x"},
	{"g;x", "http://a/b/c/g;x"},
	{"g;x?y#s", "http://a/b/c/g;x?y#s"},
	{"", "http://a/b/c/d;p?q"},
	{".", "http://a/b/c/"},
	{"./", "http://a/b/c/"},
	{"..", "http://a/b/"},
	{"../", "http://a/b/"},
	{"../g", "http://a/b/g"},
	{"../..", "http://a/"},
	{"../../", "http://a/"},
	{"../../g", "http://a/g"},
	{"../../../g", "http://a/g"},
	{"../../../../g", "http://a/g"},
	{"/./g", "http://a/g"},
	{"/../g", "http://a/g"},
	{"g.", "http://a/b/c/g."},
	{".g", "http://a/b/c/.g"},
	{"g..", "http://a/b/c/g.."},
	{"..g", "http://a/b/c/..g"},
	{"./../g", "http://a/b/g"},
	{"./g/.", "http://a/b/c/g/"},
	{"g/./h", "http://a/b/c/g/h"},
	{"g/../h", "http://a/b/c/h"},
	{"g;x=1/./y", "http://a/b/c/g;x=1/y"},
	{"g;x=1/../y", "http://a/b/c/y"},
	{"g?y/./x", "http://a/b/c/g?y/./x"},
	{"g?y/../x", "http://a/b/c/g?y/../x"},
	{"g#s/./x", "http://a/b/c/g#s/./x"},
	{"g#s/../x", "http://a/b/c/g#s/../x"},
	{"http:g", "http:g"},
}

const urlTestHelpers = `
check_resolve: (base: []u8, reference: []u8, want: []u8): Bool {
  buffer: [96]u8
  n: u32 = u32(0)
  true ? {
    dst: [*]u8 = span(&buffer)
    n = url_written(url_resolve(dst, base, reference))
  }
  got: []u8 = view(&buffer)
  n == len(want) && bytes_equal(got[u32(0):n], want)
}

check_dots: (path: []u8, want: []u8): Bool {
  buffer: [64]u8
  n: u32 = u32(0)
  true ? {
    dst: [*]u8 = span(&buffer)
    n = url_written(url_remove_dot_segments(dst, path))
  }
  got: []u8 = view(&buffer)
  n == len(want) && bytes_equal(got[u32(0):n], want)
}

range_is: (src: []u8, range: UrlRange, want: []u8): Bool = range.present && bytes_equal(src[range.start:range.end], want)

port_or: (item: Option[u32]): u32 = option_or[u32](item, u32(99999))
`

func TestE2EStdlibUrlParse(t *testing.T) {
	src := `import(std)
` + urlTestHelpers + `
main: (): i32 {
  // The example of §3, with every component.
  example: []u8 = text_literal("foo://example.com:8042/over/there?name=ferret#nose")
  assert(url_ok(url_parse(example)))
  parsed: Url = url_value(url_parse(example))
  want_scheme: []u8 = text_literal("foo")
  want_host: []u8 = text_literal("example.com")
  want_port: []u8 = text_literal("8042")
  want_path: []u8 = text_literal("/over/there")
  want_query: []u8 = text_literal("name=ferret")
  want_fragment: []u8 = text_literal("nose")
  assert(range_is(example, parsed.scheme, want_scheme))
  assert(parsed.has_authority && !parsed.userinfo.present)
  assert(range_is(example, parsed.host, want_host))
  assert(range_is(example, parsed.port, want_port))
  assert(port_or(url_port_number(example, parsed)) == u32(8042))
  assert(range_is(example, parsed.path, want_path))
  assert(range_is(example, parsed.query, want_query))
  assert(range_is(example, parsed.fragment, want_fragment))
  assert(!url_is_absolute(parsed) && !url_is_relative(parsed))
  // Query pairs.
  query: []u8 = example[parsed.query.start:parsed.query.end]
  fallback: UrlPair = UrlPair { key: url_absent(), value: url_absent(), next: u32(0) }
  pair: UrlPair = url_pair_or(url_query_next(query, u32(0)), fallback)
  want_key: []u8 = text_literal("name")
  want_value: []u8 = text_literal("ferret")
  assert(range_is(query, pair.key, want_key) && range_is(query, pair.value, want_value))
  assert(!url_pair_present(url_query_next(query, pair.next)))
  form: []u8 = text_literal("a=1&&flag&b=x%20y=z")
  first: UrlPair = url_pair_or(url_query_next(form, u32(0)), fallback)
  second: UrlPair = url_pair_or(url_query_next(form, first.next), fallback)
  third: UrlPair = url_pair_or(url_query_next(form, second.next), fallback)
  want_flag: []u8 = text_literal("flag")
  want_z: []u8 = text_literal("x%20y=z")
  assert(url_range_len(first.key) == u32(1) && url_range_len(first.value) == u32(1))
  assert(range_is(form, second.key, want_flag) && !second.value.present)
  assert(range_is(form, third.value, want_z) && !url_pair_present(url_query_next(form, third.next)))
  // Userinfo, an IPv6 literal, an IPvFuture literal, an empty port.
  user: []u8 = text_literal("https://user:pw@host.example/p")
  with_user: Url = url_value(url_parse(user))
  want_user: []u8 = text_literal("user:pw")
  want_user_host: []u8 = text_literal("host.example")
  assert(range_is(user, with_user.userinfo, want_user) && range_is(user, with_user.host, want_user_host) && !with_user.port.present)
  six: []u8 = text_literal("http://[2001:db8::1]:8080/x")
  with_six: Url = url_value(url_parse(six))
  want_six: []u8 = text_literal("[2001:db8::1]")
  assert(range_is(six, with_six.host, want_six) && port_or(url_port_number(six, with_six)) == u32(8080))
  future: []u8 = text_literal("http://[v1.fe80::a+en1]/")
  assert(url_ok(url_parse(future)))
  empty_port: []u8 = text_literal("http://a:/")
  with_empty: Url = url_value(url_parse(empty_port))
  assert(with_empty.port.present && url_range_len(with_empty.port) == u32(0) && port_or(url_port_number(empty_port, with_empty)) == u32(99999))
  big_port: []u8 = text_literal("http://a:70000/")
  assert(url_ok(url_parse(big_port)) && port_or(url_port_number(big_port, url_value(url_parse(big_port)))) == u32(99999))
  // No authority: mailto and urn keep everything after the scheme in the path.
  mail: []u8 = text_literal("mailto:John.Doe@example.com")
  with_mail: Url = url_value(url_parse(mail))
  want_mail_path: []u8 = text_literal("John.Doe@example.com")
  assert(!with_mail.has_authority && range_is(mail, with_mail.path, want_mail_path) && url_is_absolute(with_mail))
  urn: []u8 = text_literal("urn:example:animal:ferret:nose")
  with_urn: Url = url_value(url_parse(urn))
  want_urn_path: []u8 = text_literal("example:animal:ferret:nose")
  assert(range_is(urn, with_urn.path, want_urn_path) && !with_urn.query.present)
  // file:///x has an empty host but an authority.
  file: []u8 = text_literal("file:///etc/hosts")
  with_file: Url = url_value(url_parse(file))
  assert(with_file.has_authority && with_file.host.present && url_range_len(with_file.host) == u32(0))
  // Relative references.
  relative: []u8 = text_literal("../g?x#y")
  with_rel: Url = url_value(url_parse(relative))
  want_rel_path: []u8 = text_literal("../g")
  assert(url_is_relative(with_rel) && !with_rel.has_authority && range_is(relative, with_rel.path, want_rel_path))
  assert(url_range_len(with_rel.query) == u32(1) && url_range_len(with_rel.fragment) == u32(1))
  nothing: []u8 = text_literal("")
  assert(url_ok(url_parse(nothing)) && url_range_len(url_value(url_parse(nothing)).path) == u32(0))
  only_fragment: []u8 = text_literal("#top")
  assert(url_ok(url_parse(only_fragment)) && url_value(url_parse(only_fragment)).fragment.present)
  empty_query: []u8 = text_literal("http://a/p?")
  with_empty_query: Url = url_value(url_parse(empty_query))
  assert(with_empty_query.query.present && url_range_len(with_empty_query.query) == u32(0))
  // Rejections: each names its cause.
  bad_scheme: []u8 = text_literal("ht~tp://a/")
  assert(url_failure(url_parse(bad_scheme)) == u32(4))
  digit_scheme: []u8 = text_literal("1http://a/")
  assert(url_failure(url_parse(digit_scheme)) == u32(4))
  space: []u8 = text_literal("http://a/b c")
  assert(url_failure(url_parse(space)) == u32(4))
  bad_escape: []u8 = text_literal("http://a/%G1")
  assert(url_failure(url_parse(bad_escape)) == u32(5))
  short_escape: []u8 = text_literal("http://a/x?q=%4")
  assert(url_failure(url_parse(short_escape)) == u32(5))
  letters_port: []u8 = text_literal("http://a:8o80/")
  assert(url_failure(url_parse(letters_port)) == u32(3))
  unbalanced: []u8 = text_literal("http://[::1/")
  assert(url_failure(url_parse(unbalanced)) == u32(2))
  trailing: []u8 = text_literal("http://[::1]x/")
  assert(url_failure(url_parse(trailing)) == u32(2))
  bad_host: []u8 = text_literal("http://a%/")
  assert(url_failure(url_parse(bad_host)) == u32(2))
  fragment_hash: []u8 = text_literal("http://a/#a#b")
  assert(url_failure(url_parse(fragment_hash)) == u32(4))
  good_escape: []u8 = text_literal("http://a/%7Ex?%20#%2F")
  assert(url_ok(url_parse(good_escape)))
  // Dot segments (§5.2.4 examples).
  dots_a: []u8 = text_literal("/a/b/c/./../../g")
  dots_a_want: []u8 = text_literal("/a/g")
  assert(check_dots(dots_a, dots_a_want))
  dots_b: []u8 = text_literal("mid/content=5/../6")
  dots_b_want: []u8 = text_literal("mid/6")
  assert(check_dots(dots_b, dots_b_want))
  dots_c: []u8 = text_literal("/../../x/./y/..")
  dots_c_want: []u8 = text_literal("/x/")
  assert(check_dots(dots_c, dots_c_want))
  // A short destination is reported before anything is written.
  small: [3]u8
  true ? {
    s: [*]u8 = span(&small)
    assert(url_write_failure(url_remove_dot_segments(s, dots_a)) == u32(6))
    assert(url_write_failure(url_resolve(s, example, dots_a)) == u32(6))
  }
  assert(small[0] == u8(0) && small[1] == u8(0) && small[2] == u8(0))
  // Resolution needs an absolute base.
  resolve_buffer: [64]u8
  true ? {
    r: [*]u8 = span(&resolve_buffer)
    assert(url_write_failure(url_resolve(r, relative, dots_a)) == u32(1))
    assert(url_write_failure(url_resolve(r, example, space)) == u32(4))
  }
  42
}
`
	code, abnormal := buildAndRun(t, "stdlib_url_parse", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EStdlibUrlResolve(t *testing.T) {
	var src strings.Builder
	src.WriteString("import(std)\n")
	src.WriteString(urlTestHelpers)
	src.WriteString("\nmain: (): i32 {\n")
	src.WriteString("  base: []u8 = text_literal(\"http://a/b/c/d;p?q\")\n")
	for i, c := range urlResolutionCases {
		fmt.Fprintf(&src, "  r%d: []u8 = text_literal(%q)\n", i, c[0])
		fmt.Fprintf(&src, "  w%d: []u8 = text_literal(%q)\n", i, c[1])
		fmt.Fprintf(&src, "  assert(check_resolve(base, r%d, w%d))\n", i, i)
	}
	// Merging onto an authority-bearing base with an empty path inserts "/".
	src.WriteString("  bare: []u8 = text_literal(\"http://h\")\n")
	src.WriteString("  bare_ref: []u8 = text_literal(\"x/../y?q\")\n")
	src.WriteString("  bare_want: []u8 = text_literal(\"http://h/y?q\")\n")
	src.WriteString("  assert(check_resolve(bare, bare_ref, bare_want))\n")
	// A base without a "/" in its path: the reference replaces the path.
	src.WriteString("  flat: []u8 = text_literal(\"urn:x\")\n")
	src.WriteString("  flat_ref: []u8 = text_literal(\"y\")\n")
	src.WriteString("  flat_want: []u8 = text_literal(\"urn:y\")\n")
	src.WriteString("  assert(check_resolve(flat, flat_ref, flat_want))\n")
	src.WriteString("  42\n}\n")
	code, abnormal := buildAndRun(t, "stdlib_url_resolve", src.String())
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// The package view: `import("url")` exposes the declarations qualified.
func TestE2EStdlibUrlQualified(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": helloManifest,
		"main.oak": `package main

import("url")

main: (): i32 = {
  data: [9]u8
  data[0] = u8(104); data[1] = u8(116); data[2] = u8(116); data[3] = u8(112)
  data[4] = u8(58); data[5] = u8(47); data[6] = u8(47); data[7] = u8(97); data[8] = u8(47)
  src: []u8 = view(&data)
  result: Result[url.Url, url.UrlError] = url.url_parse(src)
  parsed: url.Url = url.url_value(result)
  url.url_ok(result) && parsed.has_authority && parsed.host.start == u32(7) && parsed.host.end == u32(8) && url.url_range_len(parsed.path) == u32(1) ? 42 | 1
}
`,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
