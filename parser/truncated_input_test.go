package parser

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/token"
)

func TestTruncatedInputReportsParseError(t *testing.T) {
	cases := []struct {
		name, input, message string
		line, column         int
	}{
		{"unclosed function", "fn bad6(): i32 = {\n    x: i32 = 10", "missing closing brace", 1, 18},
		{"unclosed empty function", "fn f(): () = {", "missing closing brace", 1, 14},
		{"unclosed canonical function", "f: (): i32 {\n  10\n", "missing closing brace", 1, 12},
		{"unclosed nested block", "fn f(): i32 = {\n  while true {", "missing closing brace", 2, 14},
		{"unclosed string", `bad14: string = "hello`, "unclosed string literal", 1, 17},
		{"unclosed string after newline", "s := \"hello\n", "unclosed string literal", 1, 6},
		{"infix as prefix", "bad10: i32 = 5 ** 3", "unknown operator", 1, 17},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			for _, normalize := range []bool{false, true} {
				var src token.Source = scanner.New(tc.input)
				if normalize {
					src = layout.New(src)
				}
				p := New(src)
				p.ParseProgram()
				found := false
				for _, d := range p.Diagnostics() {
					if strings.Contains(d.Message, tc.message) && d.Range.Start.Line+1 == tc.line && d.Range.Start.Character+1 == tc.column {
						found = true
					}
				}
				if !found {
					t.Errorf("layout=%v: want %q at %d:%d, got %+v", normalize, tc.message, tc.line, tc.column, p.Diagnostics())
				}
			}
		})
	}
}

func TestInfixOnlyOperatorRequiresLeftOperand(t *testing.T) {
	for _, op := range []string{"+", "*", "/", "%", "==", "!=", "<", ">", "<=", ">=", "<<", ">>", "&&", "||", "|", "|>", "?"} {
		for _, input := range []string{op + " 3", "x := 5 * " + op + " 3"} {
			t.Run(input, func(t *testing.T) {
				p := New(scanner.New(input))
				p.ParseProgram()
				if !strings.Contains(strings.Join(p.Errors(), "\n"), "unknown operator") {
					t.Fatalf("want an invalid-prefix operator diagnostic, got %v", p.Errors())
				}
			})
		}
	}
}

func TestTruncatedInputPositiveControls(t *testing.T) {
	for name, input := range map[string]string{
		"empty source":             "",
		"empty function":           "fn f(): () = {}",
		"canonical empty function": "f: (): () {}",
		"empty record":             "x := {}",
		"nullary call":             "f()",
		"empty condition block":    "true ? {}",
		"closed function":          "fn bad6(): i32 = {\n    x: i32 = 10\n}",
		"legacy layout":            "fn f(): i32\n  x := 10\n  x",
		"canonical layout":         "f: (): i32\n  x := 10\n  x",
		"explicit in layout":       "fn f(): i32\n  while true { break }\n  10",
		"layout in explicit":       "fn f(): i32 {\n  while true\n    break\n  10\n}",
		"closed string at EOF":     `x := "hello"`,
		"empty string":             `x := ""`,
		"escaped quote":            `x := "hello\""`,
		"escaped backslash":        `x := "hello\\"`,
		"escaped NUL":              `x := "a\0b\x00c"`,
		"multiline string":         "x := \"hello\nworld\"",
		"prefix operators":         "x := -3; y := !false; z := ^3",
		"binary operators":         "a := 5 + 3; b := 5 - 3; c := 5 * 3; d := 5 / 3; e := 5 % 3; f := 5 & 3; g := 5 | 3; h := 5 ^ 3; i := 5 << 3; j := 5 >> 3",
		"comparison operators":     "a := 5 == 3; b := 5 != 3; c := 5 < 3; d := 5 > 3; e := 5 <= 3; f := 5 >= 3; g := true && false; h := true || false",
		"pipeline":                 "5 |> f",
		"pattern arms":             "x ? | 1 => 2 | _ => 3",
		"condition arms":           "true ? 1 | 2",
	} {
		t.Run(name, func(t *testing.T) {
			p := New(layout.New(scanner.New(input)))
			program := p.ParseProgram()
			if errs := p.Errors(); len(errs) != 0 {
				t.Fatalf("valid input: %v", errs)
			}
			if input != "" && len(program.Statements) == 0 {
				t.Fatal("nonempty input was silently dropped")
			}
			for _, stmt := range program.Statements {
				if expr, ok := stmt.(*ast.ExpressionStatement); ok && expr.Expression == nil {
					t.Fatal("valid expression was silently dropped")
				}
			}
		})
	}
}
