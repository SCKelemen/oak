package codegen

import (
	"encoding/json"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/lowering"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/typechecker"
)

const matchValueFixture = `Choice: type = First: u32 | Second
choose: (p: Choice): u32 = p ? | .First(value) => value | .Second => u32(0)
main: (): i32 = 42
`

func checkedMatchValueFixture(t *testing.T) (*CodeGenerator, *typechecker.TypeChecker, *ast.MatchExpression) {
	t.Helper()
	p := parser.New(layout.New(scanner.New(matchValueFixture)))
	program := p.ParseProgram()
	if len(p.Errors()) != 0 {
		t.Fatalf("parser: %v", p.Errors())
	}
	tc := typechecker.New(object.NewEnvironment())
	tc.CheckProgram(program)
	if len(tc.Errors()) != 0 {
		t.Fatalf("type checker: %v", tc.Errors())
	}
	var match *ast.MatchExpression
	for _, stmt := range program.Statements {
		if fn, ok := stmt.(*ast.FunctionStatement); ok && fn.Name.Value == "choose" {
			match, _ = fn.Body.(*ast.MatchExpression)
		}
	}
	if match == nil {
		t.Fatal("checked fixture has no root match")
	}
	cg := New("main", tc)
	if _, err := cg.Generate(lowering.LowerProgram(program, tc), tc); err != nil {
		t.Fatal(err)
	}
	cg.output.Reset()
	cg.localTypes = map[string]localContainer{"p": {kind: containerADT, adtName: "Choice"}}
	return cg, tc, match
}

func TestADTMatchSequencingDryRun(t *testing.T) {
	cg, tc, match := checkedMatchValueFixture(t)
	before, err := json.Marshal(match)
	if err != nil {
		t.Fatal(err)
	}
	seq, subject := cg.seqCounter, cg.scrutineeCounter
	for i := 0; i < 3; i++ {
		if !cg.needsSequencing(match, tc) {
			t.Fatal("ADT value must require statement sequencing")
		}
	}
	if cg.seqCounter != seq || cg.scrutineeCounter != subject || cg.output.Len() != 0 {
		t.Fatal("dry run changed emission state")
	}
	if _, ok := cg.sequence(match, tc).(*ast.Identifier); !ok {
		t.Fatal("sequenced match must yield a temporary")
	}
	after, err := json.Marshal(match)
	if err != nil || string(before) != string(after) {
		t.Fatal("sequencing changed the checked match AST")
	}
	if len(cg.globalErrors) != 0 || cg.seqTypeofFallbacks != 0 {
		t.Fatalf("checked lowering must not fall back: %v", cg.globalErrors)
	}
	for _, want := range []string{"u32 oak__seq_", "oak_Choice oak__scrutinee_", ".tag == oak_Choice_tag_First", ".payload.First", "unreachable: exhaustive match"} {
		if !strings.Contains(cg.output.String(), want) {
			t.Fatalf("lowering lacks %q:\n%s", want, cg.output.String())
		}
	}
}

func TestADTMatchValueFailsClosed(t *testing.T) {
	for _, test := range []struct {
		name string
		edit func(*CodeGenerator, *ast.MatchExpression)
		want string
	}{
		{"missing registered type", func(cg *CodeGenerator, _ *ast.MatchExpression) { delete(cg.adtTypes, "Choice") }, "registered checked resolution"},
		{"callable payload storage", func(cg *CodeGenerator, _ *ast.MatchExpression) {
			cg.adtTypes["Choice"].Variants[0].Payload = &ast.FunctionTypeExpression{Return: &ast.Identifier{Value: "u32"}}
		}, "callable or Unit ADT payload storage"},
		{"callable array payload storage", func(cg *CodeGenerator, _ *ast.MatchExpression) {
			cg.adtTypes["Choice"].Variants[0].Payload = &ast.IndexExpression{Left: &ast.FunctionTypeExpression{Return: &ast.Identifier{Value: "u32"}}, Index: &ast.IntegerLiteral{Value: 2}}
		}, "callable or Unit ADT payload storage"},
		{"unknown variant", func(_ *CodeGenerator, m *ast.MatchExpression) {
			m.Arms[0].Pattern = &ast.VariantPattern{Variant: &ast.Identifier{Value: "Missing"}}
		}, "unknown variant"},
		{"nested payload constraint", func(_ *CodeGenerator, m *ast.MatchExpression) {
			m.Arms[0].Pattern = &ast.VariantPattern{Variant: &ast.Identifier{Value: "First"}, Payload: &ast.LiteralPattern{Value: &ast.IntegerLiteral{Value: 7}}}
		}, "payload patterns are unsupported"},
		{"missing arm", func(_ *CodeGenerator, m *ast.MatchExpression) { m.Arms = m.Arms[:1] }, "non-exhaustive"},
		{"empty body", func(_ *CodeGenerator, m *ast.MatchExpression) { m.Arms[0].Body = nil }, "empty arm"},
	} {
		t.Run(test.name, func(t *testing.T) {
			cg, tc, match := checkedMatchValueFixture(t)
			test.edit(cg, match)
			cg.sequence(match, tc)
			if len(cg.globalErrors) != 1 || !strings.Contains(cg.globalErrors[0].Error(), test.want) || cg.output.Len() != 0 {
				t.Fatalf("expected bounded refusal %q, errors=%v C=%q", test.want, cg.globalErrors, cg.output.String())
			}
		})
	}
	t.Run("missing checker", func(t *testing.T) {
		cg, _, match := checkedMatchValueFixture(t)
		cg.sequence(match, nil)
		if len(cg.globalErrors) != 1 || cg.output.Len() != 0 {
			t.Fatalf("missing metadata must not emit C: %v", cg.globalErrors)
		}
	})
	t.Run("fragment bypass", func(t *testing.T) {
		cg, tc, match := checkedMatchValueFixture(t)
		cg.emitMatchExpressionInline(match, tc)
		if len(cg.globalErrors) != 1 || !strings.Contains(cg.globalErrors[0].Error(), "unsequenced ADT") || cg.output.Len() != 0 {
			t.Fatalf("fragment bypass must not emit placeholder C: %v", cg.globalErrors)
		}
	})
	t.Run("unsupported carrier", func(t *testing.T) {
		function := &typechecker.FunctionType{ReturnType: &typechecker.PrimitiveType{Name: "u32"}}
		callableArray := &typechecker.ArrayType{ElementType: function, Length: 2}
		for _, typ := range []typechecker.Type{
			nil, &typechecker.UnitType{},
			&typechecker.ArrayType{ElementType: &typechecker.UnitType{}, Length: 2},
			callableArray,
			&typechecker.ArrayType{ElementType: callableArray, Length: 2},
			&typechecker.FunctionType{ReturnType: callableArray},
		} {
			if _, ok := sequenceTypeExpression(typ); ok {
				t.Fatalf("unsupported carrier %T was accepted", typ)
			}
		}
		if _, ok := sequenceTypeExpression(&typechecker.FunctionType{ReturnType: &typechecker.UnitType{}}); !ok {
			t.Fatal("a callable returning Unit has a valid C function-pointer carrier")
		}
	})
}

// Direct value operands cannot generally carry escaping control flow in the
// current parser/evaluator. This emitter control isolates the necessary C
// property: arm blocks add scopes, never a loop/switch that captures break.
func TestADTMatchValueArmPreservesBreak(t *testing.T) {
	cg, tc, match := checkedMatchValueFixture(t)
	match.Arms[0].Body = &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
		&ast.BreakStatement{},
		&ast.ExpressionStatement{Expression: &ast.IntegerLiteral{Value: 42}},
	}}}
	cg.sequence(match, tc)
	output := cg.output.String()
	if len(cg.globalErrors) != 0 || !strings.Contains(output, "break;") || !strings.Contains(output, " = 42;") {
		t.Fatalf("arm exit lowering failed: %v\n%s", cg.globalErrors, output)
	}
	for _, forbidden := range []string{"switch (", "while (", "for (", "return "} {
		if strings.Contains(output, forbidden) {
			t.Fatalf("arm exit acquired %q:\n%s", forbidden, output)
		}
	}
}
