package parser

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
)

// Inline ADT declarations need no leading pipe (docs/spec/10-syntax.md §6):
// `Case: type = Upper | Lower | Title` is canonical, payload-carrying first
// variants included; the leading pipe stays canonical in multiline layout.
func TestPipelessInlineADT(t *testing.T) {
	cases := map[string]struct {
		src      string
		variants int
	}{
		"bare variants":          {"Case: type = Upper | Lower | Title | Modifier | Other\n", 5},
		"with trailing comment":  {"NumberKind: type = Decimal | Letterlike | OtherNumeric // Nd Nl No\n", 3},
		"first variant payload":  {"Shape: type = Circle: i32 | Square: i32 | Empty\n", 3},
		"leading pipe still ok":  {"Case: type = | Upper | Lower\n", 2},
		"multiline leading pipe": {"Case: type =\n  | Upper\n  | Lower\n", 2},
	}
	for name, tc := range cases {
		p := New(scanner.New(tc.src))
		program := p.ParseProgram()
		if errs := p.Errors(); len(errs) > 0 {
			t.Errorf("%s: %v", name, errs)
			continue
		}
		found := 0
		for _, stmt := range program.Statements {
			if adt, ok := stmt.(*ast.ADTType); ok {
				found = len(adt.Variants)
			}
		}
		if found != tc.variants {
			t.Errorf("%s: got %d variants, want %d", name, found, tc.variants)
		} else {
			t.Log(name, "ok")
		}
	}
}
