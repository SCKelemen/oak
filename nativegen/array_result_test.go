package nativegen

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
)

func TestArrayDeclarationResultStorage(t *testing.T) {
	for _, test := range []struct {
		name, typ string
		length    int64
		change    func(*generator)
		want      bool
	}{
		{name: "u32", typ: "u32", length: 8, want: true},
		{name: "i32", typ: "i32", length: 6, want: true},
		{name: "u64", typ: "u64", length: 3, want: true},
		{name: "i64", typ: "i64", length: 4, want: true},
		{name: "extent boundary", typ: "u32", length: 1020, want: true},
		{name: "oversized extent", typ: "u32", length: 1022},
		{name: "zero length", typ: "u32", length: 0},
		{name: "parked result", typ: "u32", length: 8, change: func(g *generator) { g.resultAreaReg = 24 }, want: true},
		{name: "rv64", typ: "u32", length: 8, change: func(g *generator) { g.rvLane = true }},
		{name: "unselected local", typ: "u32", length: 8, change: func(g *generator) { g.returnSlot = "other" }},
		{name: "no eligible local", typ: "u32", length: 8, change: func(g *generator) { g.returnSlot = "" }},
		{name: "no indirect result", typ: "u32", length: 8, change: func(g *generator) { g.resultIndirect = false }},
		{name: "different layout", typ: "u32", length: 8, change: func(g *generator) { g.resultRecord = g.arrayLayout(scalars["u64"], 4) }},
		{name: "small result", typ: "u32", length: 4},
		{name: "unrounded extent", typ: "u32", length: 5},
		{name: "narrow", typ: "u16", length: 16},
		{name: "float", typ: "f32", length: 8},
		{name: "missing body", typ: "u32", length: 8, change: func(g *generator) { g.fn = nil }},
	} {
		t.Run(test.name, func(t *testing.T) {
			elem := scalars[test.typ]
			g := &generator{layouts: map[string]*recordLayout{}, returnSlot: "out", resultIndirect: true, resultAreaReg: 8,
				fn: &ast.FunctionStatement{Body: &ast.BlockExpression{Block: &ast.BlockStatement{}}}}
			g.resultRecord = g.arrayLayout(elem, test.length)
			if test.change != nil {
				test.change(g)
			}
			arr := g.arrayDeclarationStorage("out", elem, test.length)
			if arr.inReg != test.want {
				t.Fatalf("result storage = %v, want %v", arr.inReg, test.want)
			}
			if test.want {
				if arr.reg != g.resultAreaReg || arr.offset != 0 || g.nslots != 0 || len(g.frameObjects) != 0 {
					t.Fatalf("result array acquired wrong base or frame backing: %+v, slots %d", arr, g.nslots)
				}
			} else {
				wantSlots := (test.length*int64(elem.bits/8) + 7) / 8
				if g.nslots != wantSlots || len(g.frameObjects) != 1 {
					t.Fatal("excluded array lost its ordinary frame allocation")
				}
			}
		})
	}
}

func TestArrayResultWholeAssignmentKeepsFrameStorage(t *testing.T) {
	assignment := func(name string, value ast.Expression) ast.Statement {
		return &ast.AssignmentStatement{Name: &ast.Identifier{Value: name}, Value: value}
	}
	for _, test := range []struct {
		name      string
		statement ast.Statement
		want      bool
	}{
		{name: "permutation", statement: assignment("out", permutationLiteral("out", 1, 0, 3, 2, 5, 4, 7, 6))},
		{name: "replacement", statement: assignment("out", &ast.Identifier{Value: "other"})},
		{name: "nested replacement", statement: &ast.WhileStatement{Body: &ast.BlockStatement{Statements: []ast.Statement{
			assignment("out", &ast.Identifier{Value: "other"}),
		}}}},
		{name: "unrelated replacement", statement: assignment("other", &ast.Identifier{Value: "out"}), want: true},
		{name: "element store", statement: &ast.IndexAssignmentStatement{
			Target: &ast.IndexExpression{Left: &ast.Identifier{Value: "out"}, Index: &ast.IntegerLiteral{Value: 0}},
			Value:  &ast.IntegerLiteral{Value: 42},
		}, want: true},
	} {
		t.Run(test.name, func(t *testing.T) {
			g := &generator{layouts: map[string]*recordLayout{}, returnSlot: "out", resultIndirect: true, resultAreaReg: 8,
				fn: &ast.FunctionStatement{Body: &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{test.statement}}}}}
			g.resultRecord = g.arrayLayout(scalars["u32"], 8)
			arr := g.arrayDeclarationStorage("out", scalars["u32"], 8)
			if arr.inReg != test.want {
				t.Fatalf("result storage = %v, want %v", arr.inReg, test.want)
			}
			if !test.want && (g.nslots != 4 || len(g.frameObjects) != 1) {
				t.Fatal("whole-assigned local did not retain one frame array")
			}
		})
	}
}

func TestArrayReturnSlotLocalExclusions(t *testing.T) {
	arrayType := func() ast.Expression {
		return &ast.IndexExpression{Left: &ast.Identifier{Value: "u32"}, Index: &ast.IntegerLiteral{Value: 8}}
	}
	for _, test := range []struct {
		name   string
		change func(*ast.FunctionStatement, *ast.BlockStatement)
		want   string
	}{
		{name: "unique local", want: "out"},
		{name: "returned parameter", change: func(fn *ast.FunctionStatement, block *ast.BlockStatement) {
			fn.Parameters = []*ast.FunctionParameter{{Name: &ast.Identifier{Value: "out"}, Type: arrayType()}}
		}},
		{name: "whole address", change: func(fn *ast.FunctionStatement, block *ast.BlockStatement) {
			block.Statements = append(block.Statements[:1], &ast.ExpressionStatement{Expression: &ast.PrefixExpression{Operator: "&", Right: &ast.Identifier{Value: "out"}}}, block.Statements[1])
		}},
		{name: "element address", change: func(fn *ast.FunctionStatement, block *ast.BlockStatement) {
			address := &ast.PrefixExpression{Operator: "&", Right: &ast.IndexExpression{Left: &ast.Identifier{Value: "out"}, Index: &ast.IntegerLiteral{Value: 0}}}
			block.Statements = append(block.Statements[:1], &ast.ExpressionStatement{Expression: address}, block.Statements[1])
		}},
		{name: "nested shadow", change: func(fn *ast.FunctionStatement, block *ast.BlockStatement) {
			shadow := &ast.BlockStatement{Statements: []ast.Statement{&ast.VariableDeclaration{Name: &ast.Identifier{Value: "out"}, Type: arrayType()}}}
			block.Statements = append(block.Statements[:1], shadow, block.Statements[1])
		}},
		{name: "different result", change: func(fn *ast.FunctionStatement, block *ast.BlockStatement) {
			fn.ReturnType = &ast.IndexExpression{Left: &ast.Identifier{Value: "u64"}, Index: &ast.IntegerLiteral{Value: 4}}
		}},
	} {
		t.Run(test.name, func(t *testing.T) {
			block := &ast.BlockStatement{Statements: []ast.Statement{
				&ast.VariableDeclaration{Name: &ast.Identifier{Value: "out"}, Type: arrayType()},
				&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "out"}},
			}}
			fn := &ast.FunctionStatement{ReturnType: arrayType(), Body: &ast.BlockExpression{Block: block}}
			if test.change != nil {
				test.change(fn, block)
			}
			if got := returnSlotLocal(fn); got != test.want {
				t.Fatalf("return slot = %q, want %q", got, test.want)
			}
		})
	}
}
