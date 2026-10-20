package parser

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/scanner"
)

func TestIdentifierFirstAndMixedLayoutParseEquivalently(t *testing.T) {
	cases := map[string][2]string{
		"canonical":                           {"f: (): u32\n  x: u32 = 40\n  x + 2\n", "f: (): u32 { x: u32 = 40; x + 2 }"},
		"colonless":                           {"f(x: u32): u32\n  x + 2\n", "f(x: u32): u32 { x + 2 }"},
		"generic":                             {"f[T]: (x: T): T\n  x\n", "f[T]: (x: T): T { x }"},
		"keyword compatibility":               {"fn f(): u32\n  x: u32 = 40\n  x + 2\n", "fn f(): u32 { x: u32 = 40; x + 2 }"},
		"keyword multiline arrow":             {"fn f()\n-> u32\n  42\n", "fn f() -> u32 { 42 }"},
		"contextual word in body":             {"f: (): u32\n  effects := 40\n  effects + 2\n", "f: (): u32 { effects := 40; effects + 2 }"},
		"nullary theorem":                     {"proof: theorem ()\n  true\n", "proof: theorem () { true }"},
		"effects":                             {"f: (): u32 effects { }\n  42\n", "f: (): u32 effects { } { 42 }"},
		"brace body next line":                {"f: (): u32\n{\n42\n}\n", "f: (): u32 { 42 }"},
		"explicit inside layout":              {"fn f(): u32\n  while true {\nx := 1\nbreak\n}\n  42\n", "fn f(): u32 { while true { x := 1; break }; 42 }"},
		"layout inside explicit":              {"f: (): u32 {\nwhile true\n  break\n42\n}\n", "f: (): u32 { while true { break }; 42 }"},
		"closing explicit also closes layout": {"f: (): u32 {\n  while true\n    break }\n", "f: (): u32 { while true { break } }"},
		"nested declaration":                  {"f: (): u32\n  g: (x: u32)\n-> u32\neffects { }\n    x\n  g(42)\n", "f: (): u32 { g: (x: u32) -> u32 effects { } { x }; g(42) }"},
	}
	for name, pair := range cases {
		t.Run(name, func(t *testing.T) {
			parse := func(source string) *ast.Program {
				p := New(layout.New(scanner.New(source)))
				program := p.ParseProgram()
				if len(p.Errors()) != 0 {
					t.Fatalf("parse errors: %v\n%s", p.Errors(), source)
				}
				return program
			}
			got, want := parse(pair[0]), parse(pair[1])
			if len(got.Statements) != 1 || len(want.Statements) != 1 {
				t.Fatalf("function body escaped to top level: layout %d statements; explicit %d", len(got.Statements), len(want.Statements))
			}
			fn, ok := got.Statements[0].(*ast.FunctionStatement)
			if !ok || fn.Body == nil {
				t.Fatalf("layout did not attach a function body: %#v", got.Statements[0])
			}
			if got.String() != want.String() {
				t.Fatalf("layout and explicit trees differ:\nlayout: %s\nexplicit: %s", got.String(), want.String())
			}
		})
	}
}
