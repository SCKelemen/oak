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

func TestParser_ArrayType_WithUserDefinedTypes(t *testing.T) {
	tests := []struct {
		name  string
		input string
		check func(*testing.T, *ast.VariableDeclaration)
	}{
		{
			name:  "Slice with user type",
			input: "arr: []Byte",
			check: func(t *testing.T, stmt *ast.VariableDeclaration) {
				indexExpr, ok := stmt.Type.(*ast.IndexExpression)
				if !ok {
					t.Fatalf("expected *ast.IndexExpression, got %T", stmt.Type)
				}
				ident, ok := indexExpr.Left.(*ast.Identifier)
				if !ok {
					t.Fatalf("expected *ast.Identifier for element type, got %T", indexExpr.Left)
				}
				if ident.Value != "Byte" {
					t.Errorf("expected element type Byte, got %q", ident.Value)
				}
			},
		},
		{
			name:  "Fixed array with user type",
			input: "arr: [10]Byte",
			check: func(t *testing.T, stmt *ast.VariableDeclaration) {
				indexExpr, ok := stmt.Type.(*ast.IndexExpression)
				if !ok {
					t.Fatalf("expected *ast.IndexExpression, got %T", stmt.Type)
				}
				ident, ok := indexExpr.Left.(*ast.Identifier)
				if !ok {
					t.Fatalf("expected *ast.Identifier for element type, got %T", indexExpr.Left)
				}
				if ident.Value != "Byte" {
					t.Errorf("expected element type Byte, got %q", ident.Value)
				}
			},
		},
		{
			name:  "Span with user type",
			input: "buf: [*]Byte",
			check: func(t *testing.T, stmt *ast.VariableDeclaration) {
				indexExpr, ok := stmt.Type.(*ast.IndexExpression)
				if !ok {
					t.Fatalf("expected *ast.IndexExpression, got %T", stmt.Type)
				}
				ident, ok := indexExpr.Left.(*ast.Identifier)
				if !ok {
					t.Fatalf("expected *ast.Identifier for element type, got %T", indexExpr.Left)
				}
				if ident.Value != "Byte" {
					t.Errorf("expected element type Byte, got %q", ident.Value)
				}
				spanIdent, ok := indexExpr.Index.(*ast.Identifier)
				if !ok {
					t.Fatalf("expected *ast.Identifier for span marker, got %T", indexExpr.Index)
				}
				if spanIdent.Value != "*" {
					t.Errorf("expected span marker *, got %q", spanIdent.Value)
				}
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			lxr := scanner.New(tt.input)
			p := New(lxr)
			program := p.ParseProgram()

			if len(p.Errors()) > 0 {
				t.Fatalf("unexpected errors: %v", p.Errors())
			}

			if len(program.Statements) == 0 {
				t.Fatal("expected at least one statement")
			}

			stmt, ok := program.Statements[0].(*ast.VariableDeclaration)
			if !ok {
				t.Fatalf("expected *ast.VariableDeclaration, got %T", program.Statements[0])
			}

			tt.check(t, stmt)
		})
	}
}
