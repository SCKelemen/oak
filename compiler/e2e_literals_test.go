package compiler

import (
	"strings"
	"testing"
)

// The literals declaration (docs/spec/113-literals.md): the compiler
// projects a literal set into a Teddy scanner over the standard library
// kernel. The program checks the projected count, find, and which against
// a scalar reference written beside them, over generated text with the
// literals planted.
const literalsProgram = `
Http: literals = {
  "GET ", "POST ", "PUT ", "DELETE ",
  "Host: ", "User-Agent", "Content-Length", "Content-Type",
  "Accept: ", "Cookie: ", "HTTP/1.1", "Connection",
  "Referer: ", "Location: ", "Set-Cookie", "X-Forwarded"
}

scalar_count: (bytes: []u8): u32 {
  found: u32 = u32(0)
  pos: u32 = u32(0)
  while pos < len(bytes) {
    http_which(bytes, pos) < u32(16) ? {
      j: u32 = u32(0)
      while j < u32(16) {
        literals_teddy_literal_at(bytes, pos, view(&http_literal_bytes), view(&http_literal_starts), j) ? { found = found + u32(1) } | { }
        j = j + u32(1)
      }
    } | { }
    pos = pos + u32(1)
  }
  found
}

scalar_find: (bytes: []u8, start: u32): u32 {
  n: u32 = len(bytes)
  found: u32 = n
  pos: u32 = start
  while found == n && pos < n {
    http_which(bytes, pos) < u32(16) ? { found = pos } | { }
    pos = pos + u32(1)
  }
  found
}

main: (): u32 {
  text: [65536]u8
  seed: u32 = u32(12345)
  i: u32 = u32(0)
  while i < u32(65536) {
    seed = seed * u32(1664525) + u32(1013904223)
    text[i] = u8_trunc_u32(u32(32) + (seed >> u32(8)) % u32(95))
    i = i + u32(1)
  }
  k: u32 = u32(0)
  while k < u32(60) {
    j: u32 = k % u32(16)
    at: u32 = k * u32(1000) + (k * u32(37)) % u32(900)
    s: u32 = http_literal_starts[j]
    n: u32 = http_literal_starts[j + u32(1)] - s
    m: u32 = u32(0)
    while m < n {
      text[at + m] = http_literal_bytes[s + m]
      m = m + u32(1)
    }
    k = k + u32(1)
  }
  bytes: []u8 = view(&text)
  got: u32 = http_count(bytes)
  want: u32 = scalar_count(bytes)
  got != want || got < u32(60) ? { u32(1) } | {
    // every occurrence found in turn is the scalar walk's
    at: u32 = u32(0)
    walked: u32 = u32(0)
    ok: Bool = true
    while ok && at < len(bytes) {
      p: u32 = http_find(bytes, at)
      q: u32 = scalar_find(bytes, at)
      ok = p == q
      p < len(bytes) ? { walked = walked + u32(1) } | { }
      at = p + u32(1)
    }
    !ok ? { u32(2) } | walked != got ? { u32(3) } | http_which(bytes, u32(0) + u32(0)) != u32(16) && http_which(bytes, u32(0)) >= u32(16) ? { u32(4) } | { u32(0) }
  }
}
`

func TestE2ELiteralsDeclaration(t *testing.T) {
	exit, abnormal := buildAndRun(t, "literals_http", literalsProgram)
	if abnormal || exit != 0 {
		t.Fatalf("compiled: exit %d abnormal %v", exit, abnormal)
	}
}

func TestLiteralsDeclarationInterpreted(t *testing.T) {
	skipInShort(t)
	if got := interpretChecked(t, literalsProgram); got != 0 {
		t.Fatalf("interpreted: %d", got)
	}
}

func TestLiteralsDeclarationRejections(t *testing.T) {
	for _, tc := range []struct{ name, src, want string }{
		{"empty", "Empty: literals = { }\nmain: (): u32 = u32(0)\n", "OAK-M0304"},
		{"short", "Short: literals = { \"GET \", \"ok\" }\nmain: (): u32 = u32(0)\n", "OAK-M0304"},
		{"duplicate", "Dup: literals = { \"GET \", \"GET \" }\nmain: (): u32 = u32(0)\n", "OAK-M0304"},
		{"collision", "Http: literals = { \"GET \" }\nhttp_count: (bytes: []u8): u32 = u32(0)\nmain: (): u32 = u32(0)\n", "OAK-M0304"},
		{"type-collision", "Http: literals = { \"GET \" }\nHttpMatch: type = struct { z: u8 }\nmain: (): u32 = u32(0)\n", "OAK-M0304"},
		{"not-a-string", "Bad: literals = { 42 }\nmain: (): u32 = u32(0)\n", "string literals"},
	} {
		_, err := New().WithSource(tc.name+".oak", tc.src).Check().Get()
		if err == nil || !strings.Contains(err.Error(), tc.want) {
			t.Fatalf("%s: err = %v, want %s", tc.name, err, tc.want)
		}
	}
}

func TestLiteralsDeclarationExported(t *testing.T) {
	src := "pub Tokens: literals = { \"abc\", \"defg\" }\nmain: (): u32 = tokens_count(view(&text))\ntext: [8]u8 = [u8(97), u8(98), u8(99), u8(100), u8(101), u8(102), u8(103), u8(0)]\n"
	exit, abnormal := buildAndRun(t, "literals_pub", src)
	if abnormal || exit != 2 {
		t.Fatalf("exit %d abnormal %v, want 2", exit, abnormal)
	}
}

// The standard library module and the declaration in a module build: the
// kernel imported as `import("literals")` over a set built at run time
// agrees with a declaration of the same set, compiled through the loader.
const literalsModuleProgram = `package main
lits := import("literals")

Words: literals = { "alpha", "beta", "gamma" }

main: (): u32 {
  patterns: [14]u8 = [u8(97), u8(108), u8(112), u8(104), u8(97), u8(98), u8(101), u8(116), u8(97), u8(103), u8(97), u8(109), u8(109), u8(97)]
  starts: [4]u32 = [u32(0), u32(5), u32(9), u32(14)]
  tables: [96]u8
  lits.build(view(&patterns), view(&starts), u32(3), span(&tables))
  text: [200]u8
  i: u32 = u32(0)
  while i < u32(200) {
    text[i] = u8(46)
    i = i + u32(1)
  }
  // "beta" at 10, "alpha" at 100, "gamma" at 190
  text[10] = u8(98)
  text[11] = u8(101)
  text[12] = u8(116)
  text[13] = u8(97)
  k: u32 = u32(0)
  while k < u32(5) {
    text[u32(100) + k] = patterns[k]
    text[u32(190) + k] = patterns[u32(9) + k]
    k = k + u32(1)
  }
  bytes: []u8 = view(&text)
  runtime: u32 = lits.count(bytes, view(&patterns), view(&starts), u32(3), view(&tables))
  declared: u32 = words_count(bytes)
  first: u32 = words_find(bytes, u32(0))
  second: u32 = words_find(bytes, first + u32(1))
  which: u32 = words_which(bytes, u32(190))
  m: WordsMatch = words_match(bytes, u32(50))
  none: WordsMatch = words_match(bytes, u32(195))
  runtime == u32(3) && declared == u32(3) && first == u32(10) && second == u32(100) && which == u32(2) && m.at == u32(100) && m.which == u32(0) && none.at == u32(200) && none.which == u32(3) ? u32(42) | u32(1)
}
`

func TestE2EStdlibLiteralsModule(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": literalsModuleProgram})
	_, exit, abnormal := buildAndRunFrom(t, "stdlib_literals", New().WithPackageDir(root))
	if abnormal || exit != 42 {
		t.Fatalf("exit %d abnormal %v", exit, abnormal)
	}
}
