package parser

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/token"
)

func TestRequiredListItemAndRecordBoundaryDiagnostics(t *testing.T) {
	for _, tc := range []struct{ input, message, at string }{
		{"x := [1,2,]", "expected list item", "]"},
		{"x := [1,,2]", "expected list item", ",2"},
		{"x := [,1]", "expected list item", ",1"},
		{"x := [2]u8{1,2,}", "expected list item", "}"},
		{"x := []u8{1,2,}", "expected list item", "}"},
		{"x := f(1,)", "expected list item", ")"},
		{"x := f(,1)", "expected list item", ",1"},
		{"x := {a: }", "expected record field value", "}"},
		{"x := {a: ,b: 3}", "expected record field value", ",b"},
		{"x := {a: 1 2}", "expected ',' or '}' after record field value", "2"},
		{"x := {a: 1 2,b: 3}", "expected ',' or '}' after record field value", "2"},
		{"x := {a: 1 extra,b: 3}", "expected ',' or '}' after record field value", "extra"},
		{"x := )", "expected value expression after :=", ":="},
	} {
		t.Run(tc.input, func(t *testing.T) {
			for _, normalize := range []bool{false, true} {
				var source token.Source = scanner.New(tc.input + "; sentinel := 7")
				if normalize {
					source = layout.New(source)
				}
				p := New(source)
				program := p.ParseProgram()
				found := false
				for _, d := range p.Diagnostics() {
					if d.Message == tc.message && d.Range.Start.Line == 0 && d.Range.Start.Character == strings.Index(tc.input, tc.at) {
						found = true
					}
				}
				if !found {
					t.Errorf("layout=%v: missing positioned %q at %q: %v", normalize, tc.message, tc.at, p.Diagnostics())
				}
				if len(program.Statements) == 0 {
					t.Fatal("following declaration was lost")
				}
				last, ok := program.Statements[len(program.Statements)-1].(*ast.VariableDeclaration)
				if !ok || last == nil || last.Name.Value != "sentinel" || last.Value == nil || last.Value.String() != "7" {
					t.Fatalf("layout=%v: following declaration was lost: %#v", normalize, program.Statements)
				}
			}
		})
	}
}

func TestRecordBoundaryPreservesSupportedForms(t *testing.T) {
	for _, input := range []string{
		"x := {a: 1, b: 3}", "x := {a: 1, b: 3,}",
		"x := {,a: 1, b: 3}", "x := {a: 1,, b: 3}",
		"x := {\n a: 1,\n b: 3,\n}",
		"x := Pair {a: 1, b: 3}", "x := struct {a: 1, b: 3}",
	} {
		t.Run(input, func(t *testing.T) {
			for _, normalize := range []bool{false, true} {
				var source token.Source = scanner.New(input + "; sentinel := 7")
				if normalize {
					source = layout.New(source)
				}
				p := New(source)
				program := p.ParseProgram()
				if len(p.Errors()) != 0 {
					t.Fatalf("layout=%v: %v", normalize, p.Errors())
				}
				if len(program.Statements) != 2 {
					t.Fatalf("layout=%v: got %d statements", normalize, len(program.Statements))
				}
				decl, ok := program.Statements[0].(*ast.VariableDeclaration)
				if !ok || decl == nil {
					t.Fatalf("first declaration = %T", program.Statements[0])
				}
				record, ok := decl.Value.(*ast.RecordLiteral)
				if !ok || record == nil {
					t.Fatalf("initializer = %T", decl.Value)
				}
				fields := record.OrderedFields()
				if len(fields) != 2 || fields[0].Name != "a" || fields[0].Value.String() != "1" || fields[1].Name != "b" || fields[1].Value.String() != "3" {
					t.Fatalf("record lost fields: %#v", fields)
				}
				if record.EndToken.TokenKind != token.RBRACE {
					t.Fatalf("record ending = %v", record.EndToken)
				}
			}
		})
	}
}

func TestRequiredListFailuresPreserveExistingDiagnostics(t *testing.T) {
	for _, tc := range []struct{ input, message string }{
		{"x := [1 + ,2]", "expected operand after"},
		{"x := [1,", "no prefix parse function defined for TokenKind EOF"},
		{"x := [1,* 2]", "unknown operator"},
		{"x := [1,\x00]", "unexpected NUL character"},
		{`x := [1,"unclosed`, "unclosed string literal"},
	} {
		t.Run(tc.input, func(t *testing.T) {
			p := New(layout.New(scanner.New(tc.input)))
			p.ParseProgram()
			if !strings.Contains(strings.Join(p.Errors(), "\n"), tc.message) {
				t.Fatalf("original error lost: %v", p.Errors())
			}
			for _, message := range p.Errors() {
				if message == "expected list item" || message == "expected value expression after :=" {
					t.Fatalf("existing error obscured by redundant fallback: %v", p.Errors())
				}
			}
		})
	}
}

func TestRequiredListPreservesEmptyAndOptionalForms(t *testing.T) {
	for _, tc := range []struct {
		input string
		check func(ast.Expression) bool
	}{
		{"x := []", func(e ast.Expression) bool {
			a, ok := e.(*ast.ArrayLiteral)
			return ok && a != nil && len(a.Elements) == 0
		}},
		{"x := {}", func(e ast.Expression) bool {
			r, ok := e.(*ast.RecordLiteral)
			return ok && r != nil && len(r.OrderedFields()) == 0
		}},
		{"x := {,}", func(e ast.Expression) bool {
			r, ok := e.(*ast.RecordLiteral)
			return ok && r != nil && len(r.OrderedFields()) == 0
		}},
		{"x := f()", func(e ast.Expression) bool {
			c, ok := e.(*ast.InvocationExpression)
			return ok && c != nil && len(c.Arguments) == 0
		}},
		{"x := a[:]", func(e ast.Expression) bool {
			s, ok := e.(*ast.SliceExpression)
			return ok && s != nil && s.Low == nil && s.High == nil
		}},
	} {
		t.Run(tc.input, func(t *testing.T) {
			for _, normalize := range []bool{false, true} {
				var source token.Source = scanner.New(tc.input)
				if normalize {
					source = layout.New(source)
				}
				p := New(source)
				program := p.ParseProgram()
				if len(p.Errors()) != 0 || len(program.Statements) != 1 {
					t.Fatalf("layout=%v: %v", normalize, p.Errors())
				}
				decl, ok := program.Statements[0].(*ast.VariableDeclaration)
				if !ok || decl == nil || decl.Value == nil || !tc.check(decl.Value) {
					t.Fatalf("lost empty/optional initializer: %#v", decl)
				}
			}
		})
	}
}

func TestRecordBoundaryPreservesTypeMetadata(t *testing.T) {
	for _, tc := range []struct {
		input        string
		names, types []string
		extension    string
		metadata     bool
	}{
		{"Shape: type = {a,b: u8 c: u32,}", []string{"a", "b", "c"}, []string{"u8", "u8", "u32"}, "", false},
		{"Shape: type = {\na: u8\nb: u32\n}", []string{"a", "b"}, []string{"u8", "u32"}, "", false},
		{"Shape: type = {,a: u8,,b: u32,}", []string{"a", "b"}, []string{"u8", "u32"}, "", false},
		{"Row: type = {r | a: u8,b: u32}", []string{"a", "b"}, []string{"u8", "u32"}, "r", false},
		{`Stored: type = struct(packed, align: 8) { a,b(align: 4, json: {name: "key", omit: true}): u32 c: u8 }`, []string{"a", "b", "c"}, []string{"u32", "u32", "u8"}, "", true},
	} {
		t.Run(tc.input, func(t *testing.T) {
			for _, normalize := range []bool{false, true} {
				var source token.Source = scanner.New(tc.input)
				if normalize {
					source = layout.New(source)
				}
				p := New(source)
				program := p.ParseProgram()
				if len(p.Errors()) != 0 || len(program.Statements) != 1 {
					t.Fatalf("layout=%v: %v", normalize, p.Errors())
				}
				decl, ok := program.Statements[0].(*ast.ADTType)
				if !ok || decl == nil || len(decl.Variants) != 1 {
					t.Fatalf("lost product declaration: %#v", program.Statements[0])
				}
				record, ok := decl.Variants[0].Literal.(*ast.RecordLiteral)
				if !ok || record == nil {
					t.Fatalf("lost product shape: %#v", decl.Variants[0])
				}
				fields := record.OrderedFields()
				if len(fields) != len(tc.names) {
					t.Fatalf("lost fields: %#v", fields)
				}
				for i, field := range fields {
					if field.Name != tc.names[i] || field.Value == nil || field.Value.String() != tc.types[i] {
						t.Errorf("field %d = %#v", i, field)
					}
				}
				if tc.extension != "" && (record.Extension == nil || record.Extension.Value != tc.extension) {
					t.Fatalf("lost row extension: %#v", record.Extension)
				}
				if tc.metadata {
					if record.Token.TokenKind != token.STRUCT || record.Layout == nil || !record.Layout.Packed || record.Layout.Align != 8 {
						t.Fatalf("lost layout: %#v", record.Layout)
					}
					for _, field := range fields[:2] {
						if field.Align != 4 || len(field.Tags) != 1 || field.Tags[0].Name != "json" {
							t.Fatalf("lost grouped field metadata: %#v", field)
						}
						tags, ok := field.Tags[0].Value.(*ast.RecordLiteral)
						if !ok || tags == nil {
							t.Fatalf("lost record tag: %#v", field.Tags[0])
						}
						values := tags.OrderedFields()
						if len(values) != 2 || values[0].Name != "name" || values[0].Value.String() != "key" || values[1].Name != "omit" || values[1].Value.String() != "true" {
							t.Fatalf("lost record tag values: %#v", values)
						}
					}
				}
			}
		})
	}
}

func TestRequiredExpressionPreservesAdvancingLexicalDiagnostics(t *testing.T) {
	for _, input := range []string{"x: i32 = ;\x00; sentinel := 7", "x := 1 + ;\x00; sentinel := 7"} {
		p := New(layout.New(scanner.New(input)))
		p.ParseProgram()
		errors := p.Errors()
		if len(errors) != 1 || errors[0] != "unexpected NUL character outside string literal or comment" {
			t.Fatalf("lexical error changed or acquired redundant fallback: %v", errors)
		}
	}
}
