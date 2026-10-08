package nativegen

import (
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
)

// constantOperand folds expressions over named constants at the type's
// width: differences, complements, conversions, and shifts below the
// width; a shift at the width and a float type are not constants.
func TestConstantOperandFoldsNamedConstantExpressions(t *testing.T) {
	g := &generator{constants: map[string]asm.Constant{
		"page_size": {Type: "u64", Value: 16384},
		"entries":   {Type: "u32", Value: 2048},
		"lane":      {Type: "u32", Value: 7},
		"max8":      {Type: "u8", Value: 255},
	}}
	name := func(v string) ast.Expression { return &ast.Identifier{Value: v} }
	lit := func(v int64) ast.Expression { return &ast.IntegerLiteral{Value: v} }
	conv := func(to string, x ast.Expression) ast.Expression {
		return &ast.InvocationExpression{Function: &ast.Identifier{Value: to}, Arguments: []ast.Expression{x}}
	}
	infix := func(l ast.Expression, op string, r ast.Expression) ast.Expression {
		return &ast.InfixExpression{Left: l, Operator: op, Right: r}
	}
	not := func(x ast.Expression) ast.Expression { return &ast.PrefixExpression{Operator: "^", Right: x} }
	u64, u32 := scalars["u64"], scalars["u32"]
	cases := []struct {
		name string
		expr ast.Expression
		typ  scalar
		want uint64
		ok   bool
	}{
		{"named", name("page_size"), u64, 16384, true},
		{"low mask", infix(name("page_size"), "-", conv("u64", lit(1))), u64, 16383, true},
		{"high mask", not(infix(name("page_size"), "-", conv("u64", lit(1)))), u64, ^uint64(16383), true},
		{"conversion narrows", conv("u32", name("page_size")), u32, 16384, true},
		{"product wraps at the width", infix(name("entries"), "*", conv("u32", lit(1<<21))), u32, 0, true},
		{"shift below the width", infix(conv("u32", lit(1)), "<<", name("lane")), u32, 128, true},
		{"shift at the width is not folded", infix(conv("u64", lit(1)), "<<", conv("u64", lit(64))), u64, 0, false},
		{"compound conversion without checked width", conv("u64", infix(name("max8"), "+", conv("u8", lit(1)))), u64, 0, false},
		{"unknown name", infix(name("page_size"), "-", name("offset")), u64, 0, false},
		{"float type", name("page_size"), scalars["f64"], 0, false},
	}
	for _, c := range cases {
		got, ok := g.constantOperand(c.expr, c.typ)
		if ok != c.ok || (ok && got != c.want) {
			t.Errorf("%s: got (%d, %v), want (%d, %v)", c.name, got, ok, c.want, c.ok)
		}
	}
}

func TestAddSubImmediateUsesShiftedAArch64Field(t *testing.T) {
	g := &generator{}
	for _, test := range []struct {
		value uint64
		want  asm.Immediate
		ok    bool
	}{
		{0, asm.Immediate{}, true},
		{4095, asm.Immediate{Value: 4095}, true},
		{4096, asm.Immediate{Value: 1, Shift: 12}, true},
		{0xc000, asm.Immediate{Value: 12, Shift: 12}, true},
		{0xfff000, asm.Immediate{Value: 4095, Shift: 12}, true},
		{4097, asm.Immediate{}, false},
		{0x1000000, asm.Immediate{}, false},
	} {
		got, ok := g.addSubImmediate(test.value)
		if ok != test.ok || got != test.want {
			t.Errorf("%#x: got (%+v, %v), want (%+v, %v)", test.value, got, ok, test.want, test.ok)
		}
	}

	rv := &generator{rvLane: true}
	if _, ok := rv.addSubImmediate(0xc000); ok {
		t.Fatal("RV64 must not receive the AArch64 shifted-immediate spelling")
	}
}

func TestShiftedImmediateFlowsToCompareOperands(t *testing.T) {
	g := &generator{constants: map[string]asm.Constant{
		"entries": {Type: "u32", Value: 0xc000},
	}}
	want := asm.Immediate{Value: 12, Shift: 12}
	op, r, fixed, err := g.sourceOperand(&ast.Identifier{Value: "entries"}, scalars["u32"], "cmp")
	if err != nil || op != want || r != -1 || fixed {
		t.Fatalf("named compare operand: got (%+v, %d, %v, %v), want shifted immediate", op, r, fixed, err)
	}
	op, ok := g.simpleOperand(&ast.IntegerLiteral{Value: 0xc000}, scalars["u32"], true)
	if !ok || op != want {
		t.Fatalf("literal compare operand: got (%+v, %v), want shifted immediate", op, ok)
	}
}

func TestConstantGuardUsesShiftedAArch64Immediate(t *testing.T) {
	g := &generator{trap: "trap", flagsTo: map[string]string{}}
	if err := g.constantGuard(5, 0xc000); err != nil {
		t.Fatal(err)
	}
	if len(g.items) != 2 {
		t.Fatalf("constant guard emitted %d items, want cmp and branch", len(g.items))
	}
	compare, ok := g.items[0].(asm.Instruction)
	want := asm.Immediate{Value: 12, Shift: 12}
	if !ok || compare.Mnemonic != "cmp" || len(compare.Operands) != 2 || compare.Operands[1] != want {
		t.Fatalf("constant guard compare = %#v, want shifted immediate", g.items[0])
	}
}
