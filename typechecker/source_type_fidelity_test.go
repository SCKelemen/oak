package typechecker

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/token"
	"testing"
)

func sourceTypeForFidelity(t *testing.T, text string) ast.Expression {
	t.Helper()
	p := parser.New(scanner.New("f: (x: " + text + "): () = {}"))
	tree := p.ParseProgram()
	if len(p.Errors()) != 0 {
		t.Fatal(p.Errors())
	}
	return tree.Statements[0].(*ast.FunctionStatement).Parameters[0].Type
}

func TestTypeSubstitutionPreservesSourceConstructors(t *testing.T) {
	bindings := map[string]ast.Expression{"T": &ast.Identifier{Value: "u32"}}
	for original, want := range map[string]string{"[]T": "[]u32", "[* align 16]T": "[* align 16]u32", "[4]T": "[4]u32", "Pair[T, []u8]": "Pair[u32, []u8]"} {
		for name, substitute := range map[string]func(ast.Expression, map[string]ast.Expression) (ast.Expression, bool){"type": SubstituteTypeAST, "expression": substituteExpr} {
			t.Run(name+original, func(t *testing.T) {
				got, ok := substitute(sourceTypeForFidelity(t, original), bindings)
				if !ok || got.String() != want {
					t.Fatalf("substituted %s, want %s", got, want)
				}
				reparsed := sourceTypeForFidelity(t, got.String())
				if reparsed.String() != want {
					t.Fatalf("reparsed %s, want %s", reparsed, want)
				}
			})
		}
	}
}

func TestRegionErasurePreservesSourceConstructors(t *testing.T) {
	for original, want := range map[string]string{"View[u32, R]": "[]u32", "Span[u32, R]": "[*]u32", "Pair[u32, View[u8, R]]": "Pair[u32, []u8]"} {
		got, _ := eraseRegionType(sourceTypeForFidelity(t, original), map[string]bool{"R": true}, map[string]RegionRecord{})
		if got.String() != want {
			t.Fatalf("erased %s to %s, want %s", original, got, want)
		}
		sourceTypeForFidelity(t, got.String())
	}
}

func TestReifiedArrayTypeKeepsLengthAndShape(t *testing.T) {
	typ := &ArrayType{ElementType: &PrimitiveType{Name: "u32"}, Length: 4}
	got := typeExpressionFor(typ, token.Token{TokenKind: token.IDENT, Literal: "source_location"})
	if got.String() != "[4]u32" {
		t.Fatalf("reified array: %s", got)
	}
	sourceTypeForFidelity(t, got.String())
}

func TestReifiedViewKeepsAlignment(t *testing.T) {
	typ := &ArrayType{ElementType: &PrimitiveType{Name: "u32"}, IsSpan: true, Length: -1, Align: 16}
	got := typeExpressionFor(typ, token.Token{TokenKind: token.IDENT, Literal: "source_location"})
	if got.String() != "[* align 16]u32" {
		t.Fatalf("reified span: %s", got)
	}
	sourceTypeForFidelity(t, got.String())
}
