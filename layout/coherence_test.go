package layout

import (
	"testing"

	"github.com/SCKelemen/oak/token"
)

func TestCallableLayoutHeaderEquivalence(t *testing.T) {
	for name, header := range map[string]string{
		"declaration":                      "answer: (): u32",
		"arrow":                            "answer: () -> u32",
		"colonless":                        "answer() -> u32",
		"generic":                          "answer[T]: (x: T): T",
		"grouped parameters":               "answer: (x, y: u32): u32",
		"public":                           "pub answer: (): u32",
		"keyword compatibility":            "fn answer(): u32",
		"keyword generic compatibility":    "fn [T] answer(x: T): T",
		"method compatibility":             "fn (self: T) answer(): u32",
		"colon on next line":               "fn answer()\n: u32",
		"arrow on next line":               "fn answer()\n-> u32",
		"multiline declaration parameters": "answer: (\n  x: u32,\n  y: u32\n): u32",
		"multiline result":                 "answer: ()\n  ->\n  []u32",
		"record result":                    "answer: (): { x: u32 }",
		"function result":                  "answer: (): (u32) -> u32",
		"nested function result":           "answer: (): ((u32) -> u32) effects { }",
		"effects":                          "answer: (): u32 effects { }",
		"multiline effect clause":          "answer: (): u32\n  effects {\n    Host.Read\n  }",
		"forbids":                          "answer: (): u32 forbids { Memory.Allocate }",
		"laws":                             "answer: (x, y: u32): u32 laws { associative }",
		"dispatch":                         "answer: (): u32 dispatch { sve: native }",
		"clauses":                          "answer: (x, y: u32): u32 effects { } forbids { Host.Read } laws { associative } dispatch { sve: native }",
		"nullary theorem":                  "proof: theorem ()",
		"theorem":                          "proof: theorem (x: u8)",
		"kernel clause":                    "answer: (): () (kernel)",
	} {
		t.Run(name, func(t *testing.T) {
			layout := header + "\n  42\n"
			explicit := header + " {\n  42\n}\n"
			got := normalizedSignificant(layout)
			want := normalizedSignificant(explicit)
			assertKindsEqual(t, got, want)
			assertOriginalTokensEqual(t, sourceSignificant(layout), originalTokens(got))
			assertSyntheticBracesBalanced(t, got)
		})
	}
}

func TestExplicitBracesShieldEnclosingLayout(t *testing.T) {
	for name, source := range map[string][2]string{
		"explicit while in layout": {
			"fn f(): u32\n  while true {\nx := 1\n  }\n  2\n",
			"fn f(): u32 {\n  while true {\nx := 1\n  }\n  2\n}\n",
		},
		"explicit match in layout": {
			"f: (): u32\n  true ? {\nx: u32 = 1\n_ = x\n} | {}\n  2\n",
			"f: (): u32 {\n  true ? {\nx: u32 = 1\n_ = x\n} | {}\n  2\n}\n",
		},
		"layout while in explicit function": {
			"f: (): u32 {\nwhile true\n  x := 1\n2\n}\n",
			"f: (): u32 {\nwhile true {\n  x := 1\n}\n2\n}\n",
		},
		"explicit closing brace closes inner layout": {
			"f: (): u32 {\n  while true\n    break }\n",
			"f: (): u32 {\n  while true {\n    break } }\n",
		},
		"mixed nested bodies": {
			"f: (): u32\n  while true {\nwhile true\n  break\n}\n  2\n",
			"f: (): u32 {\n  while true {\nwhile true {\n  break\n}\n}\n  2\n}\n",
		},
		"braced data protects surrounding layout": {
			"f: (): u32\n  point := Point {\nx: 1,\ny: 2\n}\n  2\n",
			"f: (): u32 {\n  point := Point {\nx: 1,\ny: 2\n}\n  2\n}\n",
		},
	} {
		t.Run(name, func(t *testing.T) {
			got := normalizedSignificant(source[0])
			assertKindsEqual(t, got, normalizedSignificant(source[1]))
			assertOriginalTokensEqual(t, sourceSignificant(source[0]), originalTokens(got))
			assertSyntheticBracesBalanced(t, got)
		})
	}
}

func TestExplicitBodyOnFollowingLine(t *testing.T) {
	for _, header := range []string{"fn f(): u32", "f: (): u32", "while true", "unsafe"} {
		source := header + "\n{\n  42\n}\n"
		for _, tok := range normalizedSignificant(source) {
			if tok.Synthetic {
				t.Fatalf("explicit body after %q synthesized token %#v", header, tok)
			}
		}
	}
}

func TestNonLayoutCallableFormsStayUnchanged(t *testing.T) {
	for name, source := range map[string]string{
		"definition-less asm":                      "f: (): u32\ng: (): u32 = 42\n",
		"expression body":                          "f: (): u32 =\n  42\n",
		"next-line initializer":                    "f: (): u32\n= 42\n",
		"next-line fn initializer":                 "fn f(): u32\n  = 42\n",
		"fn expression body":                       "fn f(): u32 =\n  42\n",
		"fn bare expression":                       "fn f(): u32 42\nnext: u32 = 1\n",
		"function value":                           "f: (u32) -> u32 = other\n",
		"calls":                                    "f(1)\n  g(2)\n",
		"record argument":                          "f(Point { x: 1 })\n  g(2)\n",
		"slice argument":                           "f(xs[0:2])\n  g(2)\n",
		"quantifier":                               "forall (x: u8) { x == x }\n",
		"interface followed by declaration":        "Reader: interface = fn (self) read(buf: [*]u8) -> u32\nmain: (): i32 = 42\n",
		"prefix interface followed by declaration": "interface Reader: interface = fn (self) read(buf: [*]u8) -> u32\nmain: (): i32 = 42\n",
		"interface comments":                       "Reader: interface /* kind */ = // signature\n  fn (self) read(buf: [*]u8) -> u32\nmain: (): i32 = 42\n",
		"interface":                                "interface I: interface = fn (self) read() -> u32\n",
		"protocol unsafe marker":                   "P: protocol = {\n  initial A\n  step: A -> A via unsafe read(borrowed x)\n}\n",
	} {
		t.Run(name, func(t *testing.T) {
			got := normalizedSignificant(source)
			for _, tok := range got {
				if tok.Synthetic {
					t.Fatalf("unexpected synthetic token %#v", tok)
				}
			}
			assertOriginalTokensEqual(t, sourceSignificant(source), got)
		})
	}
}

func TestKeywordHeaderStillRequiresIndentedBody(t *testing.T) {
	for _, header := range []string{"fn f(): u32", "while true", "unsafe"} {
		found := false
		for _, tok := range normalizedSignificant(header + "\nx := 1\n") {
			found = found || tok.TokenKind == token.ILLEGAL
		}
		if !found {
			t.Errorf("%q must not silently accept an unindented body", header)
		}
	}
}

func TestLayoutCommentsAndIndentationPrefixes(t *testing.T) {
	for _, indent := range []string{"  ", "\t", "\t\t", " \t"} {
		source := "f: (): u32 // signature\n" + indent + "// comment\n\n" + indent + "/* body comment */\n" + indent + "x: u32 = 42\n" + indent + "x\n"
		explicit := "f: (): u32 { x: u32 = 42 x }\n"
		got := normalizedSignificant(source)
		assertKindsEqual(t, got, normalizedSignificant(explicit))
		assertOriginalTokensEqual(t, sourceSignificant(source), originalTokens(got))
		assertSyntheticBracesBalanced(t, got)
	}
}

func TestExplicitRecordFunctionFieldsNeverOpenLayoutBodies(t *testing.T) {
	for name, source := range map[string]string{
		"struct fields":                     "R: type = struct {\n  f: () -> u32\n    n: u32\n}\n",
		"semantic fields":                   "Sig: type = {\n  get: () -> u32\n    size: u32\n}\n",
		"multiple callable fields":          "R: type = struct {\n  f: () -> u32\n    g: (u32) -> u32\n}\n",
		"anonymous annotation":              "value: {\n  get: () -> u32\n    size: u32\n}\n",
		"array element annotation":          "value: [2]{\n  get: () -> u32\n    size: u32\n}\n",
		"callable result annotation":        "value: (u32) -> {\n  get: () -> u32\n    size: u32\n}\n",
		"parenthesized callable annotation": "value: ((u32) -> {\n  get: () -> u32\n    size: u32\n})\n",
		"nested record":                     "R: type = struct { inner: {\n  get: () -> u32\n    size: u32\n} }\n",
		"composed record":                   "R: type = Base & {\n  get: () -> u32\n    size: u32\n}\n",
		"ADT payload":                       "R: type = | Case: {\n  get: () -> u32\n    size: u32\n}\n",
	} {
		t.Run(name, func(t *testing.T) {
			got := normalizedSignificant(source)
			for _, tok := range got {
				if tok.Synthetic {
					t.Fatalf("record field introduced synthetic body token: %#v", tok)
				}
			}
			assertOriginalTokensEqual(t, sourceSignificant(source), got)
		})
	}
}

func TestTypeScopeDoesNotSuppressRealLocalCallable(t *testing.T) {
	for _, source := range [][2]string{
		{"f: (): u32 {\n  g: (): u32\n    42\n  g()\n}", "f: (): u32 { g: (): u32 { 42 } g() }"},
		{"f: (): u32\n  g: (): u32\n    42\n  g()\n", "f: (): u32 { g: (): u32 { 42 } g() }"},
		{"value := { field: true ? {\n  g: (): u32\n    42\n  g()\n} | 0 }", "value := { field: true ? { g: (): u32 { 42 } g() } | 0 }"},
	} {
		got := normalizedSignificant(source[0])
		assertKindsEqual(t, got, normalizedSignificant(source[1]))
		assertSyntheticBracesBalanced(t, got)
	}
}

func TestLegacyKernelNamedExpressionKeepsStatementBoundary(t *testing.T) {
	for _, body := range []string{"(kernel)", "(kernel + 1)", "(x + 1)"} {
		source := "fn f(kernel: u32): u32 " + body + "\nmain: (): i32 = 42\n"
		got := normalizedSignificant(source)
		for _, tok := range got {
			if tok.Synthetic {
				t.Fatalf("bare expression body %s synthesized a token: %#v", body, tok)
			}
		}
	}
	for _, header := range []string{"fn k(gid: u32): () (kernel)", "fn k(gid: u32): () (kernel) effects { }", "k: (gid: u32): () (kernel)"} {
		assertKindsEqual(t, normalizedSignificant(header+"\n  work()\n"), normalizedSignificant(header+" { work() }\n"))
	}
}
