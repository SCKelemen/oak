package typechecker

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
)

// These tests deliberately share already-typed syntax between contexts. The
// sealing gate must validate each occurrence's callable permission even when
// a compiler transformation reuses an expression node.
func TestSealedConstructionCallableContexts(t *testing.T) {
	const source = `
Ready: type = struct { ready_: u8 }
Handle[S]: type = struct { id: u32 }
Foreign[S]: type = struct { id: u32 }
mint: (): Handle[Ready] = Handle { id: u32(0) }
move: (h: Handle[Ready]): Handle[Ready] = Handle { id: h.id }
outsider: (): Handle[Ready] = mint()
foreign: (h: Foreign[Ready]): Handle[Ready] = mint()
`
	for _, test := range []struct {
		name   string
		change func(map[string]*ast.FunctionStatement)
		want   int
	}{
		{"constructor and same-resource transition", func(_ map[string]*ast.FunctionStatement) {}, 0},
		{"missing designated name", func(f map[string]*ast.FunctionStatement) {
			f["mint"].Name = &ast.Identifier{Value: "different"}
			f["mint"].Body = f["outsider"].Body
		}, 1},
		{"bodyless designated constructor", func(f map[string]*ast.FunctionStatement) {
			f["mint"].Body = nil
		}, 1},
		{"foreign designated constructor", func(f map[string]*ast.FunctionStatement) {
			f["mint"].ExternSymbol = "foreign_mint"
		}, 1},
		{"assembly-backed designated constructor", func(f map[string]*ast.FunctionStatement) {
			f["mint"].AsmBacked = true
		}, 1},
		{"shared literal in another callable", func(f map[string]*ast.FunctionStatement) {
			f["outsider"].Body = f["mint"].Body
		}, 1},
		{"transition cannot mint a local even with shared tail syntax", func(f map[string]*ast.FunctionStatement) {
			literal := f["move"].Body
			f["move"].Body = &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
				&ast.VariableDeclaration{Name: &ast.Identifier{Value: "extra"}, Value: literal},
				&ast.ExpressionStatement{Expression: literal},
			}}}
		}, 1},
		{"nested closure cannot borrow constructor permission", func(f map[string]*ast.FunctionStatement) {
			literal := f["mint"].Body
			closure := &ast.FunctionLiteral{Body: &ast.BlockStatement{Statements: []ast.Statement{
				&ast.ExpressionStatement{Expression: literal},
			}}}
			f["mint"].Body = &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
				&ast.ExpressionStatement{Expression: closure},
				&ast.ExpressionStatement{Expression: literal},
			}}}
		}, 1},
		{"nested callable cannot spoof constructor name", func(f map[string]*ast.FunctionStatement) {
			local := *f["mint"]
			f["outsider"].Body = &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{&local}}}
		}, 1},
		{"same state of another nominal resource", func(f map[string]*ast.FunctionStatement) {
			f["foreign"].Body = f["mint"].Body
		}, 1},
	} {
		t.Run(test.name, func(t *testing.T) {
			tc := setupTypeChecker(source)
			program := parseProgram(source)
			tc.CheckProgram(program)
			if errs := tc.Errors(); len(errs) != 0 {
				t.Fatal(errs)
			}
			functions := make(map[string]*ast.FunctionStatement)
			for _, stmt := range program.Statements {
				if fn, ok := stmt.(*ast.FunctionStatement); ok {
					functions[fn.Name.Value] = fn
				}
			}
			test.change(functions)
			model := NewResourceModel()
			model.MarkResourceType("Handle")
			model.MarkResourceType("Foreign")
			model.MarkInitial("Handle", "Ready")
			model.MarkTypestate("Handle", 1)
			model.MarkSealedInitialConstructor("Handle", "mint")
			model.MarkOperation("mint", ResourceOperation{ReturnsFresh: true, Targets: []string{"Ready"}})
			alias := ResourceOperation{ReturnsAlias: true, AliasesArgument: 0, Consumes: []int{0}, Targets: []string{"Ready"}}
			model.MarkOperation("move", alias)
			model.MarkOperation("foreign", alias)
			tc.checkSealedResourceConstruction(program, model)
			got := 0
			for _, d := range tc.Diagnostics() {
				if d.Code == CodeResourceTypestateConstruction {
					got++
				}
			}
			if got != test.want {
				t.Fatalf("construction diagnostics = %d, want %d: %v", got, test.want, tc.Errors())
			}
		})
	}
}
