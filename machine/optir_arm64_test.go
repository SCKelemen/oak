package machine

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/optir"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
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
	boolNormalized := false
	for _, item := range lowered.Items {
		switch item := item.(type) {
		case asm.Label:
			labels++
		case asm.Instruction:
			if item.Mnemonic == "b" || item.Mnemonic == "cbnz" {
				branches++
			}
			if item.Mnemonic == "and" && len(item.Operands) == 3 {
				destination, destinationOK := item.Operands[0].(asm.Register)
				source, sourceOK := item.Operands[1].(asm.Register)
				mask, maskOK := item.Operands[2].(asm.Immediate)
				boolNormalized = boolNormalized || destinationOK && sourceOK && maskOK && destination.Num == 0 && source.Num == 0 && mask.Value == 1
			}
		}
	}
	if branches < 4 || labels < 4 {
		t.Fatalf("SSA control flow was not selected: %d branches, %d labels\n%s", branches, labels, text(lowered.Items))
	}
	if !boolNormalized {
		t.Fatalf("Bool ABI input was not normalized before its branch:\n%s", text(lowered.Items))
	}
}

func TestLowerOptIRArm64NormalizesNarrowIntegers(t *testing.T) {
	tests := []struct {
		typ        string
		constant   string
		result     string
		normalizer string
	}{
		{typ: "u8", constant: "255", result: "u32", normalizer: "uxtb"},
		{typ: "i8", constant: "-1", result: "i32", normalizer: "sxtb"},
		{typ: "u16", constant: "65535", result: "u32", normalizer: "uxth"},
		{typ: "i16", constant: "-1", result: "i32", normalizer: "sxth"},
	}
	for _, test := range tests {
		t.Run(test.typ, func(t *testing.T) {
			parameterType := &ast.Identifier{Value: test.typ}
			resultType := &ast.Identifier{Value: test.result}
			declaration := &ast.FunctionStatement{
				Name:       &ast.Identifier{Value: "narrow"},
				Parameters: []*ast.FunctionParameter{{Name: &ast.Identifier{Value: "x"}, Type: parameterType}},
				ReturnType: resultType,
			}
			template := &asm.Function{
				Name: "narrow", Arch: asm.ArchArm64, Signature: declaration, Fallback: true,
				Bindings: []asm.Binding{{Register: w(0), Param: "x"}},
			}
			cfg := optir.CFG{
				Name: "narrow", Entry: 0, Results: []optir.Type{optir.Type(test.result)},
				Blocks: []optir.Block{{
					ID: 0, Parameters: []optir.Value{{ID: 1, Type: optir.Type(test.typ), Name: "x"}},
					Operations: []optir.Operation{
						{Code: optir.OpConstInt, Results: []optir.Value{{ID: 2, Type: optir.Type(test.typ)}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: test.constant}}},
						{Code: optir.OpIntAdd, Results: []optir.Value{{ID: 3, Type: optir.Type(test.typ)}}, Operands: []optir.ValueID{1, 2}},
						{Code: optir.OpCastInt, Results: []optir.Value{{ID: 4, Type: optir.Type(test.result)}}, Operands: []optir.ValueID{3}},
					},
					Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{4}},
				}},
			}
			lowered, err := LowerOptIRArm64(cfg, template)
			if err != nil {
				t.Fatal(err)
			}
			if findings := asm.Check(lowered, declaration, map[string]bool{"narrow": true}); len(findings) != 0 {
				t.Fatalf("selected body fails seam check: %v\n%s", findings, text(lowered.Items))
			}
			body := text(lowered.Items)
			if count := strings.Count(body, test.normalizer+" "); count < 3 {
				t.Fatalf("%s representation was not normalized at the ABI, arithmetic, and cast boundaries (%d):\n%s", test.typ, count, body)
			}
		})
	}
}

func TestLowerOptIRArm64VerifiesSignedNarrowBranchAndEdges(t *testing.T) {
	parsed := parser.New(layout.New(scanner.New(`
narrow_branch: (x: i8): i32 = {
  y: i8 = x + i8(10)
  z: i8 = y < i8(0) ? y | i8(0)
  i32(z)
}
`)))
	program := parsed.ParseProgram()
	if errs := parsed.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	declaration, ok := program.Statements[0].(*ast.FunctionStatement)
	if !ok {
		t.Fatalf("parsed declaration is %T", program.Statements[0])
	}
	template := &asm.Function{
		Name: "narrow_branch", Arch: asm.ArchArm64, Signature: declaration, Fallback: true,
		Bindings: []asm.Binding{{Register: w(0), Param: "x"}},
	}
	cfg := optir.CFG{
		Name: "narrow_branch", Entry: 0, Results: []optir.Type{"i32"},
		Blocks: []optir.Block{
			{ID: 0, Parameters: []optir.Value{{ID: 1, Type: "i8", Name: "x"}}, Operations: []optir.Operation{
				{Code: optir.OpConstInt, Results: []optir.Value{{ID: 2, Type: "i8"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "10"}}},
				{Code: optir.OpIntAdd, Results: []optir.Value{{ID: 3, Type: "i8"}}, Operands: []optir.ValueID{1, 2}},
				{Code: optir.OpConstInt, Results: []optir.Value{{ID: 4, Type: "i8"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "0"}}},
				{Code: optir.OpLess, Results: []optir.Value{{ID: 5, Type: optir.TypeBool}}, Operands: []optir.ValueID{3, 4}},
			}, Terminator: optir.Terminator{Kind: optir.TerminatorCondBranch, Condition: 5, True: optir.Edge{Target: 1}, False: optir.Edge{Target: 2}}},
			{ID: 1, Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 3, Arguments: []optir.ValueID{3}}}},
			{ID: 2, Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 3, Arguments: []optir.ValueID{4}}}},
			{ID: 3, Parameters: []optir.Value{{ID: 6, Type: "i8", Name: "z"}}, Operations: []optir.Operation{
				{Code: optir.OpCastInt, Results: []optir.Value{{ID: 7, Type: "i32"}}, Operands: []optir.ValueID{6}},
			}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{7}}},
		},
	}
	lowered, err := LowerOptIRArm64(cfg, template)
	if err != nil {
		t.Fatal(err)
	}
	if findings := asm.Check(lowered, declaration, map[string]bool{"narrow_branch": true}); len(findings) != 0 {
		t.Fatalf("selected body fails seam check: %v\n%s", findings, text(lowered.Items))
	}
	if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("selected body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, text(lowered.Items))
	}
	body := text(lowered.Items)
	signedComparison := false
	for _, item := range lowered.Items {
		instruction, isInstruction := item.(asm.Instruction)
		if !isInstruction || instruction.Mnemonic != "cset" || len(instruction.Operands) != 2 {
			continue
		}
		condition, isCondition := instruction.Operands[1].(asm.Condition)
		signedComparison = isCondition && condition.Code == "lt"
	}
	if !signedComparison || strings.Contains(body, "mov x") {
		t.Fatalf("signed narrow comparison/edge lowering has the wrong shape:\n%s", body)
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
