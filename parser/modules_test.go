package parser

// Surface syntax of the module system (docs/spec/83-modules.md section 3):
// pub / pub(opaque) declaration modifiers, string import paths, binding and
// sealed import forms, package-qualified generic types and typed literals.

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
)

func parseModuleSource(t *testing.T, input string) *ast.Program {
	t.Helper()
	p := New(scanner.New(input))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatalf("parse errors: %v", errs)
	}
	return program
}

func parseModuleErrors(t *testing.T, input string) []string {
	t.Helper()
	p := New(scanner.New(input))
	p.ParseProgram()
	return p.Errors()
}

func TestParsePubModifiers(t *testing.T) {
	program := parseModuleSource(t, `package geometry

pub(opaque) Point: type = struct { x: i32, y: i32 }
pub Shape: type = Dot | Line: i32
pub make: (x: i32): Point = Point { x: x, y: x }
pub limit: i32 = 4
pub json: tag = { name: string }
hidden: (v: i32): i32 = v
pub fn (p: Point) norm(): i32 = 0
`)
	if len(program.Statements) != 8 {
		t.Fatalf("statements = %d", len(program.Statements))
	}
	point := program.Statements[1].(*ast.ADTType)
	if !point.Exported || !point.Opaque {
		t.Fatalf("pub(opaque) type flags = %+v", point)
	}
	shape := program.Statements[2].(*ast.ADTType)
	if !shape.Exported || shape.Opaque {
		t.Fatalf("pub type flags = %+v", shape)
	}
	if fn := program.Statements[3].(*ast.FunctionStatement); !fn.Exported || fn.Opaque {
		t.Fatalf("pub function flags = %+v", fn)
	}
	if decl := program.Statements[4].(*ast.VariableDeclaration); !decl.Exported {
		t.Fatalf("pub value flags = %+v", decl)
	}
	if tag := program.Statements[5].(*ast.TagDeclaration); !tag.Exported {
		t.Fatalf("pub tag flags = %+v", tag)
	}
	if fn := program.Statements[6].(*ast.FunctionStatement); fn.Exported {
		t.Fatalf("unmarked declaration must be private: %+v", fn)
	}
	if fn := program.Statements[7].(*ast.FunctionStatement); !fn.Exported || fn.Receiver == nil {
		t.Fatalf("pub method flags = %+v", fn)
	}
}

func TestParsePubRejectsMisuse(t *testing.T) {
	for name, input := range map[string]string{
		"opaque on function": "pub(opaque) f: (): i32 = 1\n",
		"unknown modifier":   "pub(secret) T: type = u8\n",
		"pub on statement":   "pub while true { }\n",
		"pub on import":      "pub x := import(\"a.b/c\")\n",
		"dangling pub":       "pub",
	} {
		if errs := parseModuleErrors(t, input); len(errs) == 0 {
			t.Fatalf("%s: accepted", name)
		}
	}
}

func TestParseImportForms(t *testing.T) {
	program := parseModuleSource(t, `package main

import("example.com/hello/geometry")
geo := import("example.com/hello/geometry")
h: { Key: type, hash: (Key) -> u64 } = import("example.com/hello/fnv")
import(std)
`)
	if len(program.Statements) != 5 {
		t.Fatalf("statements = %d", len(program.Statements))
	}
	plain := program.Statements[1].(*ast.ImportStatement)
	if plain.Path.Value != "example.com/hello/geometry" || plain.Alias != nil || plain.Signature != nil {
		t.Fatalf("statement import = %+v", plain)
	}
	bound := program.Statements[2].(*ast.ImportStatement)
	if bound.Alias == nil || bound.Alias.Value != "geo" || bound.Signature != nil {
		t.Fatalf("binding import = %+v", bound)
	}
	sealed := program.Statements[3].(*ast.ImportStatement)
	if sealed.Alias == nil || sealed.Alias.Value != "h" || sealed.Signature == nil {
		t.Fatalf("sealed import = %+v", sealed)
	}
	shape, isShape := sealed.Signature.(*ast.RecordLiteral)
	if !isShape || len(shape.FieldOrder) != 2 {
		t.Fatalf("signature shape = %#v", sealed.Signature)
	}
	if kind, ok := shape.FieldOrder[0].Value.(*ast.Identifier); !ok || kind.Value != "type" {
		t.Fatalf("type member = %#v", shape.FieldOrder[0].Value)
	}
	if _, ok := shape.FieldOrder[1].Value.(*ast.FunctionTypeExpression); !ok {
		t.Fatalf("function member = %#v", shape.FieldOrder[1].Value)
	}
	bootstrap := program.Statements[4].(*ast.ImportStatement)
	if bootstrap.Path.Value != "std" {
		t.Fatalf("bootstrap import = %+v", bootstrap)
	}
	if plain.String() != `import("example.com/hello/geometry")` || bound.String() != `geo := import("example.com/hello/geometry")` {
		t.Fatalf("String() = %q / %q", plain.String(), bound.String())
	}
}

func TestParseImportRejectsMalformedPaths(t *testing.T) {
	for name, input := range map[string]string{
		"multi import":   "import(\"a.b/c\", \"a.b/d\")\n",
		"integer path":   "import(7)\n",
		"missing parens": "import \"a.b/c\"\n",
	} {
		if errs := parseModuleErrors(t, input); len(errs) == 0 {
			t.Fatalf("%s: accepted", name)
		}
	}
}

func TestParseQualifiedGenericTypeAndLiteral(t *testing.T) {
	program := parseModuleSource(t, `package main

import("example.com/hello/ring")

buffer: ring.Ring[u8, 8] = ring.Ring { head: 0 }
`)
	decl := program.Statements[2].(*ast.VariableDeclaration)
	application, isApplication := decl.Type.(*ast.IndexExpression)
	if !isApplication {
		t.Fatalf("qualified generic type = %#v", decl.Type)
	}
	inner, isInner := application.Left.(*ast.IndexExpression)
	if !isInner {
		t.Fatalf("nested application = %#v", application.Left)
	}
	base, isBase := inner.Left.(*ast.Identifier)
	if !isBase || base.Value != "ring.Ring" {
		t.Fatalf("qualified base = %#v", inner.Left)
	}
	literal, isLiteral := decl.Value.(*ast.RecordLiteral)
	if !isLiteral || literal.TypeName == nil || literal.TypeName.Value != "ring.Ring" {
		t.Fatalf("qualified typed literal = %#v", decl.Value)
	}
}

// Layout-delimited and braced spellings agree for the new forms.
func TestParsePubLayoutEquivalence(t *testing.T) {
	braced := parseModuleSource(t, "pub f: (): i32 = { 1 }\n")
	if fn := braced.Statements[0].(*ast.FunctionStatement); !fn.Exported {
		t.Fatalf("braced pub lost: %+v", fn)
	}
}

func TestParseGenericPackagesSelectiveImportsAndSharing(t *testing.T) {
	program := parseModuleSource(t, `package ring[T, N: u32]

{ f, g } := import("example.com/x")
bytes := import("example.com/hello/pair")[u8, 3]
h: { Key: type = u64, hash: (Key) -> u64 } = import("example.com/hello/fnv")
`)
	clause := program.Statements[0].(*ast.PackageStatement)
	if len(clause.TypeParams) != 2 || clause.TypeParams[1].Name.Value != "N" {
		t.Fatalf("package params = %+v", clause.TypeParams)
	}
	selective := program.Statements[1].(*ast.ImportStatement)
	if len(selective.Names) != 2 || selective.Names[1].Value != "g" || selective.Alias != nil {
		t.Fatalf("selective import = %+v", selective)
	}
	generic := program.Statements[2].(*ast.ImportStatement)
	if len(generic.Arguments) != 2 || generic.Alias.Value != "bytes" {
		t.Fatalf("generic import = %+v", generic)
	}
	sealed := program.Statements[3].(*ast.ImportStatement)
	shape := sealed.Signature.(*ast.RecordLiteral)
	if shape.FieldOrder[0].Manifest == nil || shape.FieldOrder[1].Manifest != nil {
		t.Fatalf("shared type member not recorded: %+v", shape.FieldOrder)
	}
}
