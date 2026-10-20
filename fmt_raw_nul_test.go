package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func TestFmtRejectsRawNULOutsideText(t *testing.T) {
	for name, input := range map[string]string{
		"start":  "\x00a := true",
		"middle": "a := true\x00b := false",
		"end":    "a := true\x00",
	} {
		for _, mode := range []string{"stdout", "-l", "-w"} {
			t.Run(name+"/"+mode, func(t *testing.T) {
				file := filepath.Join(t.TempDir(), name+".oak")
				if err := os.WriteFile(file, []byte(input), 0600); err != nil {
					t.Fatal(err)
				}
				args := []string{file}
				if mode != "stdout" {
					args = append([]string{mode}, args...)
				}
				if code, out := runCLI(t, fmtCommand, args); code != 1 || !strings.Contains(out, "unexpected NUL character") {
					t.Fatalf("raw NUL must fail the syntax guard: code=%d output=%q", code, out)
				}
				if got, err := os.ReadFile(file); err != nil || string(got) != input {
					t.Fatalf("invalid input was changed: %q, %v", got, err)
				}
			})
		}
	}
}

func TestFmtPreservesRawNULInsideText(t *testing.T) {
	for name, input := range map[string]string{
		"string":        "s := \"a\x00b\"; next := true",
		"line comment":  "//a\x00b\nnext := true",
		"block comment": "/*a\x00b*/next := true",
	} {
		t.Run(name, func(t *testing.T) {
			file := filepath.Join(t.TempDir(), "source.oak")
			if err := os.WriteFile(file, []byte(input), 0600); err != nil {
				t.Fatal(err)
			}
			if code, out := runCLI(t, fmtCommand, []string{"-w", file}); code != 0 {
				t.Fatalf("valid text NUL failed formatting: %d %s", code, out)
			}
			got, err := os.ReadFile(file)
			if err != nil || string(got) != input+"\n" {
				t.Fatalf("formatting changed content around NUL: %q, %v", got, err)
			}
			p := parser.New(layout.New(scanner.New(string(got))))
			program := p.ParseProgram()
			if len(p.Errors()) != 0 || len(program.Statements) == 0 {
				t.Fatalf("formatted input did not parse: %v", p.Errors())
			}
			last, ok := program.Statements[len(program.Statements)-1].(*ast.VariableDeclaration)
			if !ok || last.Name.Value != "next" {
				t.Fatal("formatting lost the suffix")
			}
			if name == "string" {
				value := program.Statements[0].(*ast.VariableDeclaration).Value.(*ast.StringLiteral).Value
				if value != "a\x00b" {
					t.Fatalf("decoded value changed: %q", value)
				}
			}
		})
	}
}
