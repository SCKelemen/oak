package parser

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
)

func TestParser_ArrayType_Slice(t *testing.T) {
	input := "arr: []i32 = [1, 2, 3]"

	lxr := scanner.New(input)
	p := New(lxr)
	program := p.ParseProgram()

	if len(p.Errors()) > 0 {
		t.Fatalf("unexpected errors: %v", p.Errors())
	}

	stmt := program.Statements[0].(*ast.VariableDeclaration)

	// Check that type expression is an IndexExpression representing []i32
	indexExpr, ok := stmt.Type.(*ast.IndexExpression)
	if !ok {
		t.Fatalf("expected *ast.IndexExpression for slice type, got %T", stmt.Type)
	}

	// For slices, Index should be an empty identifier
	ident, ok := indexExpr.Index.(*ast.Identifier)
	if !ok {
		t.Fatalf("expected *ast.Identifier for slice index, got %T", indexExpr.Index)
	}

	if ident.Value != "" {
		t.Errorf("expected empty identifier for slice, got %q", ident.Value)
	}
}

func TestParser_ArrayType_FixedSize(t *testing.T) {
	input := "arr: [10]i32"

	lxr := scanner.New(input)
	p := New(lxr)
	program := p.ParseProgram()

	if len(p.Errors()) > 0 {
		t.Fatalf("unexpected errors: %v", p.Errors())
	}

	stmt := program.Statements[0].(*ast.VariableDeclaration)

	// Check that type expression is an IndexExpression representing [10]i32
	indexExpr, ok := stmt.Type.(*ast.IndexExpression)
	if !ok {
		t.Fatalf("expected *ast.IndexExpression for array type, got %T", stmt.Type)
	}

	// For fixed-size arrays, Index should be an IntegerLiteral
	intLit, ok := indexExpr.Index.(*ast.IntegerLiteral)
	if !ok {
		t.Fatalf("expected *ast.IntegerLiteral for array size, got %T", indexExpr.Index)
	}

	if intLit.Value != 10 {
		t.Errorf("expected array size 10, got %d", intLit.Value)
	}
}

func TestParser_ArrayType_InFunctionParameter(t *testing.T) {
	input := "fn process(buf: [*]Byte, arr: [10]i32) -> () { }"

	lxr := scanner.New(input)
	p := New(lxr)
	program := p.ParseProgram()

	if len(p.Errors()) > 0 {
		t.Fatalf("unexpected errors: %v", p.Errors())
	}

	fn := program.Statements[0].(*ast.FunctionStatement)

	// Check first parameter: [*]Byte (pointer to byte array)
	if len(fn.Parameters) < 1 {
		t.Fatal("expected at least 1 parameter")
	}

	// Check second parameter: [10]i32 (fixed-size array)
	if len(fn.Parameters) < 2 {
		t.Fatal("expected at least 2 parameters")
	}

	param2Type := fn.Parameters[1].Type
	indexExpr, ok := param2Type.(*ast.IndexExpression)
	if !ok {
		t.Fatalf("expected *ast.IndexExpression for array type, got %T", param2Type)
	}

	intLit, ok := indexExpr.Index.(*ast.IntegerLiteral)
	if !ok {
		t.Fatalf("expected *ast.IntegerLiteral for array size, got %T", indexExpr.Index)
	}

	if intLit.Value != 10 {
		t.Errorf("expected array size 10, got %d", intLit.Value)
	}
}



