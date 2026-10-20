package parser

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/token"
)

func TestRequiredOperatorOperand(t *testing.T) {
	cases := []struct {
		input, operator string
		column          int
	}{}
	for _, op := range []string{"-", "!", "^", "&"} {
		cases = append(cases, struct {
			input, operator string
			column          int
		}{"x := " + op + " ; sentinel := 7", op, 6})
	}
	for _, op := range []string{"+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>", "==", "!=", "<", ">", "<=", ">=", "&&", "||", "|>"} {
		cases = append(cases, struct {
			input, operator string
			column          int
		}{"x := 1 " + op + " ; sentinel := 7", op, 8})
	}
	for _, tc := range cases {
		t.Run(tc.input, func(t *testing.T) {
			for _, normalize := range []bool{false, true} {
				var source token.Source = scanner.New(tc.input)
				if normalize {
					source = layout.New(source)
				}
				p := New(source)
				program := p.ParseProgram()
				found := false
				for _, d := range p.Diagnostics() {
					if d.Message == fmt.Sprintf("expected operand after %q", tc.operator) && d.Range.Start.Line == 0 && d.Range.Start.Character == tc.column-1 {
						found = true
					}
				}
				if !found {
					t.Errorf("layout=%v: missing positioned operand diagnostic: %v", normalize, p.Errors())
				}
				last, ok := program.Statements[len(program.Statements)-1].(*ast.VariableDeclaration)
				if !ok || last.Name.Value != "sentinel" {
					t.Fatalf("layout=%v: recovery lost following declaration", normalize)
				}
			}
		})
	}
}

func TestRequiredOperandNestedContexts(t *testing.T) {
	for _, input := range []string{
		"x: i32 = 1 |> ;", "fn f(): i32 { x: i32 = 1 |> ; x }",
		"f(1 + , 2)", "f(-)", "x := a[1 + ]", "x := a[1 + :2]",
		"x := [1 + , 2]", "x := {a: 1 + , b: 2}", "x := 1 + := 2",
		"fn f(): i32 { 1 + }", "fn f(): i32 { -; 7 }", "f: (): i32 = 1 + ;",
		"x := 1 + 2 |> ;", "x := -(1 |> ;) ;",
	} {
		t.Run(input, func(t *testing.T) {
			p := New(layout.New(scanner.New(input)))
			p.ParseProgram()
			if !strings.Contains(strings.Join(p.Errors(), "\n"), "expected operand after") {
				t.Fatalf("missing required-operand diagnostic: %v", p.Errors())
			}
		})
	}
}

func TestRequiredOperandPreservesOptionalForms(t *testing.T) {
	for _, input := range []string{
		"x := a[:]; sentinel := 7", "x := a[:2]; sentinel := 7", "x := a[1:]; sentinel := 7", "x := a[1:2]", "x := a[1 + 2:3 + 4]",
		"f()", "x := []", "x := {}", "fn f(): () {}", "fn f(): () { return }", "x: i32",
		"true ? {}", "true ? {} | {}", "x ? | 1 => {} | _ => {}", "x := 1 |> f", "x := 1 |> f(2)",
		"x := -1; y := !false; z := ^3", "x := 1 + 2 * 3", "x := \"a\" + \"b\"",
		"fn f(): i32\n  x: i32\n  x", "x := 1 /*\x00*/ + 2", "s := \"a\x00b\"; x := 1 + 2",
	} {
		t.Run(input, func(t *testing.T) {
			p := New(layout.New(scanner.New(input)))
			program := p.ParseProgram()
			if len(p.Errors()) != 0 {
				t.Fatalf("valid control: %v", p.Errors())
			}
			if len(program.Statements) == 0 {
				t.Fatal("valid source dropped")
			}
			_ = program.String()
		})
	}
}

func TestRequiredOperandKeepsExistingErrors(t *testing.T) {
	for _, tc := range []struct{ input, message string }{
		{"x := 1 +", "no prefix parse function defined for TokenKind EOF"},
		{"x := -", "no prefix parse function defined for TokenKind EOF"},
		{"x := 1 + * 2", "unknown operator"},
		{"x := 1 + \x00; sentinel := 7", "unexpected NUL character"},
		{`x := 1 + "unclosed`, "unclosed string literal"},
	} {
		t.Run(tc.input, func(t *testing.T) {
			p := New(layout.New(scanner.New(tc.input)))
			p.ParseProgram()
			if !strings.Contains(strings.Join(p.Errors(), "\n"), tc.message) {
				t.Fatalf("original operand error lost: want %q in %v", tc.message, p.Errors())
			}
		})
	}
}
