package parser

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/scanner"
)

// An extra closing brace is a syntax error at the brace, never a statement
// with no expression that the checker reports later without a position.
func TestUnbalancedClosingBraceIsAParseError(t *testing.T) {
	cases := map[string]struct {
		src       string
		line, col int
	}{
		"after a body":    {"f: (x: u32): u32 {\n  x\n} }\nmain: (): i32 = 0\n", 3, 3},
		"alone on a line": {"f: (x: u32): u32 {\n  x\n}\n}\nmain: (): i32 = 0\n", 4, 1},
		"after a ternary": {"f: (x: u32): u32 {\n  x > u32(1) ? { x } | {\n  u32(0) } }\n}\nmain: (): i32 = 0\n", 4, 1},
	}
	for name, c := range cases {
		p := New(layout.New(scanner.New(c.src)))
		program := p.ParseProgram()
		errs := p.Errors()
		if len(errs) == 0 {
			t.Fatalf("%s: no parse error for an extra closing brace", name)
		}
		if !strings.Contains(errs[0], "unexpected '}'") {
			t.Fatalf("%s: want the brace named, got %q", name, errs[0])
		}
		for _, stmt := range program.Statements {
			if stmt == nil {
				t.Fatalf("%s: a nil statement reached the program", name)
			}
		}
		diags := p.Diagnostics()
		if len(diags) == 0 || diags[0].Range.Start.Line+1 != c.line || diags[0].Range.Start.Character+1 != c.col {
			t.Fatalf("%s: want the error at %d:%d, got %+v", name, c.line, c.col, diags)
		}
	}
	balanced := "f: (x: u32): u32 {\n  x > u32(1) ? { x } | {\n  u32(0) }\n}\nmain: (): i32 = 0\n"
	p := New(layout.New(scanner.New(balanced)))
	p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatalf("balanced program: %v", errs)
	}
}
