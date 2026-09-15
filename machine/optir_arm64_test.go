package machine

import (
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/optir"
)

func TestLowerOptIRArm64DestroysSSAEdgesAndPassesSeam(t *testing.T) {
	u32 := &ast.Identifier{Value: "u32"}
	boolean := &ast.Identifier{Value: "Bool"}
	declaration := &ast.FunctionStatement{
		Name: &ast.Identifier{Value: "choose"},
		Parameters: []*ast.FunctionParameter{
			{Name: &ast.Identifier{Value: "flag"}, Type: boolean},
			{Name: &ast.Identifier{Value: "x"}, Type: u32},
		},
		ReturnType: u32,
	}
	template := &asm.Function{
		Name: "choose", Arch: asm.ArchArm64, Signature: declaration, Fallback: true,
		Bindings: []asm.Binding{{Register: w(0), Param: "flag"}, {Register: w(1), Param: "x"}},
	}
	cfg := optir.CFG{
		Name: "choose", Entry: 0, Results: []optir.Type{"u32"},
		Blocks: []optir.Block{
			{ID: 0, Parameters: []optir.Value{{ID: 1, Type: optir.TypeBool, Name: "flag"}, {ID: 2, Type: "u32", Name: "x"}}, Terminator: optir.Terminator{
				Kind: optir.TerminatorCondBranch, Condition: 1,
				True: optir.Edge{Target: 1}, False: optir.Edge{Target: 2},
			}},
			{ID: 1, Operations: []optir.Operation{
				{Code: optir.OpConstInt, Results: []optir.Value{{ID: 3, Type: "u32"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "1"}}},
				{Code: optir.OpIntAdd, Results: []optir.Value{{ID: 4, Type: "u32"}}, Operands: []optir.ValueID{2, 3}},
			}, Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 3, Arguments: []optir.ValueID{4}}}},
			{ID: 2, Operations: []optir.Operation{
				{Code: optir.OpConstInt, Results: []optir.Value{{ID: 5, Type: "u32"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "2"}}},
				{Code: optir.OpIntAdd, Results: []optir.Value{{ID: 6, Type: "u32"}}, Operands: []optir.ValueID{2, 5}},
			}, Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 3, Arguments: []optir.ValueID{6}}}},
			{ID: 3, Parameters: []optir.Value{{ID: 7, Type: "u32", Name: "result"}}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{7}}},
		},
	}
	lowered, err := LowerOptIRArm64(cfg, template)
	if err != nil {
		t.Fatal(err)
	}
	if findings := asm.Check(lowered, declaration, map[string]bool{"choose": true}); len(findings) != 0 {
		t.Fatalf("selected body fails seam check: %v\n%s", findings, text(lowered.Items))
	}
	branches, labels := 0, 0
	for _, item := range lowered.Items {
		switch item := item.(type) {
		case asm.Label:
			labels++
		case asm.Instruction:
			if item.Mnemonic == "b" || item.Mnemonic == "cbnz" {
				branches++
			}
		}
	}
	if branches < 4 || labels < 4 {
		t.Fatalf("SSA control flow was not selected: %d branches, %d labels\n%s", branches, labels, text(lowered.Items))
	}
}

func TestLowerOptIRArm64RefusesEffects(t *testing.T) {
	decl := &ast.FunctionStatement{Name: &ast.Identifier{Value: "f"}, ReturnType: &ast.Identifier{Value: "u32"}}
	template := &asm.Function{Name: "f", Signature: decl}
	cfg := optir.CFG{Name: "f", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
		ID:         0,
		Operations: []optir.Operation{{Code: optir.OpCall, Results: []optir.Value{{ID: 1, Type: "u32"}}, Effects: []optir.Effect{optir.EffectCall}, Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "g"}}}},
		Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{1}},
	}}}
	if _, err := LowerOptIRArm64(cfg, template); err == nil {
		t.Fatal("effectful OptIR operation reached native selection")
	}
}

func TestLowerOptIRArm64RefusesIncompleteTemplate(t *testing.T) {
	cfg := optir.CFG{Name: "f", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
		ID:         0,
		Operations: []optir.Operation{{Code: optir.OpConstInt, Results: []optir.Value{{ID: 1, Type: "u32"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "0"}}}},
		Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{1}},
	}}}
	if _, err := LowerOptIRArm64(cfg, &asm.Function{Signature: &ast.FunctionStatement{}}); err == nil {
		t.Fatal("incomplete assembler template reached native selection")
	}
}
