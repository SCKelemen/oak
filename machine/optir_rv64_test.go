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

func TestLowerOptIRRV64DestroysSSAEdgesAndVerifies(t *testing.T) {
	declaration := optIRRV64Declaration(t, `
choose: (flag: Bool, x: u32): u32 = flag ? x + u32(1) | x + u32(2)
`)
	template := &asm.Function{
		Name: "choose", Arch: asm.ArchRV64, Signature: declaration, Fallback: true,
		Bindings: []asm.Binding{{Register: optIRRV64Register(10), Param: "flag"}, {Register: optIRRV64Register(11), Param: "x"}},
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
	lowered, err := LowerOptIRRV64(cfg, template)
	if err != nil {
		t.Fatal(err)
	}
	if findings := asm.Check(lowered, declaration, map[string]bool{"choose": true}); len(findings) != 0 {
		t.Fatalf("selected body fails seam check: %v\n%s", findings, text(lowered.Items))
	}
	if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("selected body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, text(lowered.Items))
	}
	branches, labels := 0, 0
	boolNormalized := false
	for _, item := range lowered.Items {
		switch item := item.(type) {
		case asm.Label:
			labels++
		case asm.Instruction:
			if item.Mnemonic == "j" || item.Mnemonic == "bnez" {
				branches++
			}
			if item.Mnemonic == "andi" && len(item.Operands) == 3 {
				destination, destinationOK := item.Operands[0].(asm.Register)
				source, sourceOK := item.Operands[1].(asm.Register)
				mask, maskOK := item.Operands[2].(asm.Immediate)
				boolNormalized = boolNormalized || destinationOK && sourceOK && maskOK && destination.Num == 10 && source.Num == 10 && mask.Value == 1
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

func TestLowerOptIRRV64PreservesWCanonicalizationWhenWideningU32(t *testing.T) {
	declaration := optIRRV64Declaration(t, `
widen: (x: u32): u64 = u64(x + u32(1))
`)
	template := &asm.Function{
		Name: "widen", Arch: asm.ArchRV64, Signature: declaration, Fallback: true,
		Bindings: []asm.Binding{{Register: optIRRV64Register(10), Param: "x"}},
	}
	cfg := optir.CFG{Name: "widen", Entry: 0, Results: []optir.Type{"u64"}, Blocks: []optir.Block{{
		ID: 0, Parameters: []optir.Value{{ID: 1, Type: "u32", Name: "x"}},
		Operations: []optir.Operation{
			{Code: optir.OpConstInt, Results: []optir.Value{{ID: 2, Type: "u32"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "1"}}},
			{Code: optir.OpIntAdd, Results: []optir.Value{{ID: 3, Type: "u32"}}, Operands: []optir.ValueID{1, 2}},
			{Code: optir.OpCastInt, Results: []optir.Value{{ID: 4, Type: "u64"}}, Operands: []optir.ValueID{3}},
		},
		Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{4}},
	}}}
	lowered, err := LowerOptIRRV64(cfg, template)
	if err != nil {
		t.Fatal(err)
	}
	if findings := asm.Check(lowered, declaration, nil); len(findings) != 0 {
		t.Fatalf("selected body fails seam check: %v\n%s", findings, text(lowered.Items))
	}
	if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("selected body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, text(lowered.Items))
	}
	body := text(lowered.Items)
	if !strings.Contains(body, "addw ") || !strings.Contains(body, "slli ") || !strings.Contains(body, "srli ") {
		t.Fatalf("u32 arithmetic/widening did not preserve the RV64 W-value convention:\n%s", body)
	}
	shift32 := 0
	for _, item := range lowered.Items {
		instruction, ok := item.(asm.Instruction)
		if !ok || instruction.Mnemonic != "slli" && instruction.Mnemonic != "srli" || len(instruction.Operands) != 3 {
			continue
		}
		immediate, ok := instruction.Operands[2].(asm.Immediate)
		if ok && immediate.Value == 32 {
			shift32++
		}
	}
	if shift32 != 2 {
		t.Fatalf("u32-to-u64 widening has %d half-clearing shifts, want 2:\n%s", shift32, body)
	}
}

func TestLowerOptIRRV64NormalizesSignedNarrowArithmetic(t *testing.T) {
	declaration := optIRRV64Declaration(t, `
narrow: (x: i8): i32 = i32(x + i8(1))
`)
	template := &asm.Function{
		Name: "narrow", Arch: asm.ArchRV64, Signature: declaration, Fallback: true,
		Bindings: []asm.Binding{{Register: optIRRV64Register(10), Param: "x"}},
	}
	cfg := optir.CFG{Name: "narrow", Entry: 0, Results: []optir.Type{"i32"}, Blocks: []optir.Block{{
		ID: 0, Parameters: []optir.Value{{ID: 1, Type: "i8", Name: "x"}},
		Operations: []optir.Operation{
			{Code: optir.OpConstInt, Results: []optir.Value{{ID: 2, Type: "i8"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "1"}}},
			{Code: optir.OpIntAdd, Results: []optir.Value{{ID: 3, Type: "i8"}}, Operands: []optir.ValueID{1, 2}},
			{Code: optir.OpCastInt, Results: []optir.Value{{ID: 4, Type: "i32"}}, Operands: []optir.ValueID{3}},
		},
		Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{4}},
	}}}
	lowered, err := LowerOptIRRV64(cfg, template)
	if err != nil {
		t.Fatal(err)
	}
	if findings := asm.Check(lowered, declaration, nil); len(findings) != 0 {
		t.Fatalf("selected body fails seam check: %v\n%s", findings, text(lowered.Items))
	}
	if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("selected body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, text(lowered.Items))
	}
	body := text(lowered.Items)
	if strings.Count(body, "slli ") < 2 || strings.Count(body, "srai ") < 2 {
		t.Fatalf("signed narrow input/result were not normalized at both boundaries:\n%s", body)
	}
}

func TestLowerOptIRRV64UsesReservedScratchForWideConstant(t *testing.T) {
	declaration := optIRRV64Declaration(t, `
wide: (): u64 = u64(4294967296)
`)
	template := &asm.Function{Name: "wide", Arch: asm.ArchRV64, Signature: declaration, Fallback: true}
	cfg := optir.CFG{Name: "wide", Entry: 0, Results: []optir.Type{"u64"}, Blocks: []optir.Block{{
		ID:         0,
		Operations: []optir.Operation{{Code: optir.OpConstInt, Results: []optir.Value{{ID: 1, Type: "u64"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "4294967296"}}}},
		Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{1}},
	}}}
	lowered, err := LowerOptIRRV64(cfg, template)
	if err != nil {
		t.Fatal(err)
	}
	if findings := asm.Check(lowered, declaration, nil); len(findings) != 0 {
		t.Fatalf("selected body fails seam check: %v\n%s", findings, text(lowered.Items))
	}
	if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("selected body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, text(lowered.Items))
	}
	scratchClobbered := false
	for _, register := range lowered.Clobbers {
		scratchClobbered = scratchClobbered || register.Num == optIRRV64CopyScratch
	}
	if !scratchClobbered || !strings.Contains(text(lowered.Items), "t6") {
		t.Fatalf("wide constant did not use and declare reserved t6 scratch:\nclobbers=%v\n%s", lowered.Clobbers, text(lowered.Items))
	}
}

func TestLowerOptIRRV64RefusesEffectsAndWrongArchitecture(t *testing.T) {
	declaration := &ast.FunctionStatement{Name: &ast.Identifier{Value: "f"}, ReturnType: &ast.Identifier{Value: "u32"}}
	template := &asm.Function{Name: "f", Arch: asm.ArchRV64, Signature: declaration}
	cfg := optir.CFG{Name: "f", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
		ID:         0,
		Operations: []optir.Operation{{Code: optir.OpCall, Results: []optir.Value{{ID: 1, Type: "u32"}}, Effects: []optir.Effect{optir.EffectCall}, Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "g"}}}},
		Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{1}},
	}}}
	if _, err := LowerOptIRRV64(cfg, template); err == nil {
		t.Fatal("effectful OptIR operation reached RV64 selection")
	}
	template.Arch = asm.ArchArm64
	if _, err := LowerOptIRRV64(cfg, template); err == nil {
		t.Fatal("AArch64 template reached RV64 selection")
	}
}

func TestLowerOptIRRV64RefusesMixedSignCast(t *testing.T) {
	declaration := &ast.FunctionStatement{
		Name:       &ast.Identifier{Value: "bad_cast"},
		Parameters: []*ast.FunctionParameter{{Name: &ast.Identifier{Value: "x"}, Type: &ast.Identifier{Value: "i32"}}},
		ReturnType: &ast.Identifier{Value: "u64"},
	}
	template := &asm.Function{
		Name: "bad_cast", Arch: asm.ArchRV64, Signature: declaration,
		Bindings: []asm.Binding{{Register: optIRRV64Register(10), Param: "x"}},
	}
	cfg := optir.CFG{Name: "bad_cast", Entry: 0, Results: []optir.Type{"u64"}, Blocks: []optir.Block{{
		ID:         0,
		Parameters: []optir.Value{{ID: 1, Type: "i32", Name: "x"}},
		Operations: []optir.Operation{{Code: optir.OpCastInt, Results: []optir.Value{{ID: 2, Type: "u64"}}, Operands: []optir.ValueID{1}}},
		Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{2}},
	}}}
	if _, err := LowerOptIRRV64(cfg, template); err == nil || !strings.Contains(err.Error(), "value-preserving cast i32 to u64") {
		t.Fatalf("mixed-sign i32-to-u64 cast was not refused precisely: %v", err)
	}
	for _, valid := range [][2]optir.Type{{"u8", "u8"}, {"i8", "i64"}, {"u32", "u64"}, {"u32", "i64"}} {
		if !optIRRV64ValidWidening(valid[0], valid[1]) {
			t.Errorf("valid OptIR widening %s to %s refused", valid[0], valid[1])
		}
	}
	for _, invalid := range [][2]optir.Type{{"i8", "u16"}, {"u32", "i32"}, {"i64", "u64"}, {"u64", "i64"}} {
		if optIRRV64ValidWidening(invalid[0], invalid[1]) {
			t.Errorf("invalid OptIR widening %s to %s admitted", invalid[0], invalid[1])
		}
	}
}

func optIRRV64Declaration(t *testing.T, source string) *ast.FunctionStatement {
	t.Helper()
	parsed := parser.New(layout.New(scanner.New(source)))
	program := parsed.ParseProgram()
	if errs := parsed.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	declaration, ok := program.Statements[0].(*ast.FunctionStatement)
	if !ok {
		t.Fatalf("parsed declaration is %T", program.Statements[0])
	}
	return declaration
}
