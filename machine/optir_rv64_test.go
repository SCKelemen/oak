package machine

import (
	"fmt"
	"strconv"
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

func TestLowerOptIRRV64CallsKnownScalarCalleeAndVerifies(t *testing.T) {
	declarations := optIRRV64Declarations(t, `
inc: (x: i8): i8 = x + i8(1)
call_inc: (ignored: i8, x: i8): i8 = inc(x)
`)
	declaration, callee := declarations["call_inc"], declarations["inc"]
	template := &asm.Function{
		Name: "call_inc", Arch: asm.ArchRV64, Signature: declaration, Fallback: true,
		Bindings: []asm.Binding{{Register: optIRRV64Register(10), Param: "ignored"}, {Register: optIRRV64Register(11), Param: "x"}},
		Callees:  map[string]*ast.FunctionStatement{"inc": callee},
	}
	cfg := optir.CFG{Name: "call_inc", Entry: 0, Results: []optir.Type{"i8"}, Blocks: []optir.Block{{
		ID: 0, Parameters: []optir.Value{{ID: 1, Type: "i8", Name: "ignored"}, {ID: 2, Type: "i8", Name: "x"}},
		Operations: []optir.Operation{{
			Code: optir.OpCall, Results: []optir.Value{{ID: 3, Type: "i8"}}, Operands: []optir.ValueID{2}, Effects: []optir.Effect{optir.EffectCall},
			Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "inc"}},
		}},
		Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{3}},
	}}}
	lowered, err := LowerOptIRRV64(cfg, template)
	if err != nil {
		t.Fatal(err)
	}
	if lowered.Frame != 16 {
		t.Fatalf("call frame = %d, want 16", lowered.Frame)
	}
	if findings := asm.Check(lowered, declaration, map[string]bool{"inc": true}); len(findings) != 0 {
		t.Fatalf("selected call body fails seam check: %v\n%s", findings, text(lowered.Items))
	}
	if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("selected call body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, text(lowered.Items))
	}
	body := text(lowered.Items)
	for _, instruction := range []string{"addi sp, sp, #-16", "sd ra, [sp,#8]", "mv a0, a1", "call inc", "ld ra, [sp,#8]", "addi sp, sp, #16", "ret"} {
		if !strings.Contains(body, instruction) {
			t.Errorf("selected call body lacks %q:\n%s", instruction, body)
		}
	}
	if strings.Count(body, "slli ") < 2 || strings.Count(body, "srai ") < 2 {
		t.Errorf("i8 argument/result were not normalized at ABI boundaries:\n%s", body)
	}
	for _, register := range lowered.Clobbers {
		if register.Num == 1 {
			t.Errorf("restored ra was declared clobbered: %v", lowered.Clobbers)
		}
	}
}

func TestLowerOptIRRV64CallsKnownZeroArgumentCalleeAndVerifies(t *testing.T) {
	declarations := optIRRV64Declarations(t, `
answer: (): u32 = u32(42)
call_answer: (): u32 = answer()
`)
	declaration := declarations["call_answer"]
	template := &asm.Function{
		Name: "call_answer", Arch: asm.ArchRV64, Signature: declaration, Fallback: true,
		Callees: map[string]*ast.FunctionStatement{"answer": declarations["answer"]},
	}
	cfg := optir.CFG{Name: "call_answer", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
		ID: 0, Operations: []optir.Operation{{
			Code: optir.OpCall, Results: []optir.Value{{ID: 1, Type: "u32"}}, Effects: []optir.Effect{optir.EffectCall},
			Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "answer"}},
		}}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{1}},
	}}}
	lowered, err := LowerOptIRRV64(cfg, template)
	if err != nil {
		t.Fatal(err)
	}
	if findings := asm.Check(lowered, declaration, map[string]bool{"answer": true}); len(findings) != 0 {
		t.Fatalf("selected zero-argument call fails seam check: %v\n%s", findings, text(lowered.Items))
	}
	if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("selected zero-argument call verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, text(lowered.Items))
	}
}

func TestLowerOptIRRV64AllowsCallResultConsumedByNextCall(t *testing.T) {
	declarations := optIRRV64Declarations(t, `
inc: (x: u32): u32 = x + u32(1)
twice: (x: u32): u32 = inc(inc(x))
`)
	declaration := declarations["twice"]
	template := &asm.Function{
		Name: "twice", Arch: asm.ArchRV64, Signature: declaration, Fallback: true,
		Bindings: []asm.Binding{{Register: optIRRV64Register(10), Param: "x"}},
		Callees:  map[string]*ast.FunctionStatement{"inc": declarations["inc"]},
	}
	call := func(result, operand optir.ValueID) optir.Operation {
		return optir.Operation{
			Code: optir.OpCall, Results: []optir.Value{{ID: result, Type: "u32"}}, Operands: []optir.ValueID{operand}, Effects: []optir.Effect{optir.EffectCall},
			Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "inc"}},
		}
	}
	cfg := optir.CFG{Name: "twice", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
		ID: 0, Parameters: []optir.Value{{ID: 1, Type: "u32", Name: "x"}}, Operations: []optir.Operation{call(2, 1), call(3, 2)},
		Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{3}},
	}}}
	lowered, err := LowerOptIRRV64(cfg, template)
	if err != nil {
		t.Fatal(err)
	}
	if findings := asm.Check(lowered, declaration, map[string]bool{"inc": true}); len(findings) != 0 {
		t.Fatalf("selected call chain fails seam check: %v\n%s", findings, text(lowered.Items))
	}
	if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("selected call chain verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, text(lowered.Items))
	}
	if count := strings.Count(text(lowered.Items), "call inc"); count != 2 {
		t.Fatalf("selected call chain has %d calls, want 2:\n%s", count, text(lowered.Items))
	}
}

func TestLowerOptIRRV64UsesParallelCopiesForCallArguments(t *testing.T) {
	declarations := optIRRV64Declarations(t, `
subtract: (left: u32, right: u32): u32 = left - right
swapped: (x: u32, y: u32): u32 = subtract(y, x)
`)
	declaration := declarations["swapped"]
	template := &asm.Function{
		Name: "swapped", Arch: asm.ArchRV64, Signature: declaration, Fallback: true,
		Bindings: []asm.Binding{{Register: optIRRV64Register(10), Param: "x"}, {Register: optIRRV64Register(11), Param: "y"}},
		Callees:  map[string]*ast.FunctionStatement{"subtract": declarations["subtract"]},
	}
	cfg := optir.CFG{Name: "swapped", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
		ID: 0, Parameters: []optir.Value{{ID: 1, Type: "u32", Name: "x"}, {ID: 2, Type: "u32", Name: "y"}},
		Operations: []optir.Operation{{
			Code: optir.OpCall, Results: []optir.Value{{ID: 3, Type: "u32"}}, Operands: []optir.ValueID{2, 1}, Effects: []optir.Effect{optir.EffectCall},
			Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "subtract"}},
		}}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{3}},
	}}}
	lowered, err := LowerOptIRRV64(cfg, template)
	if err != nil {
		t.Fatal(err)
	}
	if findings := asm.Check(lowered, declaration, map[string]bool{"subtract": true}); len(findings) != 0 {
		t.Fatalf("selected swapped call fails seam check: %v\n%s", findings, text(lowered.Items))
	}
	if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("selected swapped call verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, text(lowered.Items))
	}
	body := text(lowered.Items)
	for _, move := range []string{"mv t6, a0", "mv a0, a1", "mv a1, t6"} {
		if !strings.Contains(body, move) {
			t.Errorf("call argument swap lacks %q:\n%s", move, body)
		}
	}
	scratchClobbered := false
	for _, register := range lowered.Clobbers {
		scratchClobbered = scratchClobbered || register.Num == optIRRV64CopyScratch
	}
	if !scratchClobbered {
		t.Errorf("call argument cycle did not declare t6 scratch: %v", lowered.Clobbers)
	}
}

func TestLowerOptIRRV64CallsWithEightScalarRegisterArgumentsAndVerifies(t *testing.T) {
	declarations := optIRRV64Declarations(t, `
eighth: (a: u32, b: u32, c: u32, d: u32, e: u32, f: u32, g: u32, h: u32): u32 = h
call_eighth: (a: u32, b: u32, c: u32, d: u32, e: u32, f: u32, g: u32, h: u32): u32 = eighth(a, b, c, d, e, f, g, h)
`)
	declaration := declarations["call_eighth"]
	template := &asm.Function{Name: "call_eighth", Arch: asm.ArchRV64, Signature: declaration, Fallback: true, Callees: map[string]*ast.FunctionStatement{"eighth": declarations["eighth"]}}
	parameters := make([]optir.Value, 8)
	operands := make([]optir.ValueID, 8)
	for index, name := range []string{"a", "b", "c", "d", "e", "f", "g", "h"} {
		id := optir.ValueID(index + 1)
		parameters[index] = optir.Value{ID: id, Type: "u32", Name: name}
		operands[index] = id
		template.Bindings = append(template.Bindings, asm.Binding{Register: optIRRV64Register(10 + index), Param: name})
	}
	cfg := optir.CFG{Name: "call_eighth", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
		ID: 0, Parameters: parameters, Operations: []optir.Operation{{
			Code: optir.OpCall, Results: []optir.Value{{ID: 9, Type: "u32"}}, Operands: operands, Effects: []optir.Effect{optir.EffectCall},
			Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "eighth"}},
		}}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{9}},
	}}}
	lowered, err := LowerOptIRRV64(cfg, template)
	if err != nil {
		t.Fatal(err)
	}
	if findings := asm.Check(lowered, declaration, map[string]bool{"eighth": true}); len(findings) != 0 {
		t.Fatalf("selected eight-argument call fails seam check: %v\n%s", findings, text(lowered.Items))
	}
	if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("selected eight-argument call verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, text(lowered.Items))
	}
}

func TestLowerOptIRRV64MaterializesVerifiedSpills(t *testing.T) {
	declaration := optIRRV64Declaration(t, `
spilled_sum: (): u32 = u32(20) + u32(22)
`)
	template := &asm.Function{Name: "spilled_sum", Arch: asm.ArchRV64, Signature: declaration, Fallback: true}
	cfg := optir.CFG{Name: "spilled_sum", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
		ID: 0, Operations: []optir.Operation{
			{Code: optir.OpConstInt, Results: []optir.Value{{ID: 1, Type: "u32"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "20"}}},
			{Code: optir.OpConstInt, Results: []optir.Value{{ID: 2, Type: "u32"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "22"}}},
			{Code: optir.OpIntAdd, Results: []optir.Value{{ID: 3, Type: "u32"}}, Operands: []optir.ValueID{1, 2}},
		}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{3}},
	}}}
	lowered, err := lowerOptIRRV64WithRegisters(cfg, template, []int{5})
	if err != nil {
		t.Fatal(err)
	}
	if lowered.Frame != 16 {
		t.Fatalf("spill frame = %d, want 16", lowered.Frame)
	}
	if findings := asm.Check(lowered, declaration, nil); len(findings) != 0 {
		t.Fatalf("spilled body fails seam check: %v\n%s", findings, text(lowered.Items))
	}
	if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("spilled body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, text(lowered.Items))
	}
	body := text(lowered.Items)
	for _, instruction := range []string{"addi sp, sp, #-16", "sw ", "lw ", "addi sp, sp, #16"} {
		if !strings.Contains(body, instruction) {
			t.Errorf("spilled body lacks %q:\n%s", instruction, body)
		}
	}
	spillScratch := false
	for _, register := range lowered.Clobbers {
		spillScratch = spillScratch || register.Num == optIRRV64SpillScratchA || register.Num == optIRRV64CopyScratch
	}
	if !spillScratch {
		t.Errorf("spill scratch is absent from clobbers: %v", lowered.Clobbers)
	}
}

func TestLowerOptIRRV64MaterializesProductionPressureAcrossSSAEdges(t *testing.T) {
	const values = 18
	var source strings.Builder
	source.WriteString("edge_pressure: (flag: Bool): u32 = flag ? (")
	for index := 1; index <= values; index++ {
		if index > 1 {
			source.WriteString(" + ")
		}
		fmt.Fprintf(&source, "u32(%d)", index)
	}
	source.WriteString(") | (")
	for index := 2; index <= values+1; index++ {
		if index > 2 {
			source.WriteString(" + ")
		}
		fmt.Fprintf(&source, "u32(%d)", index)
	}
	source.WriteString(")\n")
	declaration := optIRRV64Declaration(t, source.String())
	cfg := optIREdgePressureCFG(values)
	plan, err := optir.PlanRegisters(cfg, optIRRV64SpillRegisters, map[optir.ValueID]int{1: 10})
	if err != nil {
		t.Fatal(err)
	}
	spilledParameter := false
	for _, parameter := range cfg.Blocks[3].Parameters {
		_, spilledParameter = plan.Spills[parameter.ID]
		if spilledParameter {
			break
		}
	}
	if !spilledParameter {
		t.Fatalf("test plan has no spilled merge parameter: %+v", plan.Spills)
	}
	template := &asm.Function{
		Name: cfg.Name, Arch: asm.ArchRV64, Signature: declaration, Fallback: true,
		Bindings: []asm.Binding{{Register: optIRRV64Register(10), Param: "flag"}},
	}
	lowered, err := LowerOptIRRV64(cfg, template)
	if err != nil {
		t.Fatal(err)
	}
	body := text(lowered.Items)
	if lowered.Frame == 0 || !strings.Contains(body, "sw ") || !strings.Contains(body, "lw ") {
		t.Fatalf("edge lowering did not materialize spilled parallel copies:\n%s", body)
	}
	if findings := asm.Check(lowered, declaration, map[string]bool{cfg.Name: true}); len(findings) != 0 {
		t.Fatalf("spilled edge body fails seam check: %v\n%s", findings, body)
	}
	if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("spilled edge body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, body)
	}
}

func TestLowerOptIRRV64MaterializesNarrowSignedSpills(t *testing.T) {
	declaration := optIRRV64Declaration(t, `
spilled_narrow: (): i8 = i8(120) + i8(10)
`)
	template := &asm.Function{Name: "spilled_narrow", Arch: asm.ArchRV64, Signature: declaration, Fallback: true}
	cfg := optir.CFG{Name: "spilled_narrow", Entry: 0, Results: []optir.Type{"i8"}, Blocks: []optir.Block{{
		ID: 0, Operations: []optir.Operation{
			{Code: optir.OpConstInt, Results: []optir.Value{{ID: 1, Type: "i8"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "120"}}},
			{Code: optir.OpConstInt, Results: []optir.Value{{ID: 2, Type: "i8"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "10"}}},
			{Code: optir.OpIntAdd, Results: []optir.Value{{ID: 3, Type: "i8"}}, Operands: []optir.ValueID{1, 2}},
		}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{3}},
	}}}
	lowered, err := lowerOptIRRV64WithRegisters(cfg, template, []int{5})
	if err != nil {
		t.Fatal(err)
	}
	if findings := asm.Check(lowered, declaration, nil); len(findings) != 0 {
		t.Fatalf("narrow spilled body fails seam check: %v\n%s", findings, text(lowered.Items))
	}
	if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("narrow spilled body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, text(lowered.Items))
	}
	body := text(lowered.Items)
	if !strings.Contains(body, "sb ") || !strings.Contains(body, "lb ") || !strings.Contains(body, "srai ") {
		t.Fatalf("i8 spill lacks byte storage or canonical sign extension:\n%s", body)
	}
}

func TestLowerOptIRRV64ReloadsSpilledReturnValue(t *testing.T) {
	declaration := optIRRV64Declaration(t, `
spilled_return: (): u32 = u32(42)
`)
	cfg := optir.CFG{Name: "spilled_return", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
		ID: 0, Operations: []optir.Operation{
			{Code: optir.OpConstInt, Results: []optir.Value{{ID: 1, Type: "u32"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "42"}}},
			{Code: optir.OpConstInt, Results: []optir.Value{{ID: 2, Type: "u32"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "1"}}},
			{Code: optir.OpConstInt, Results: []optir.Value{{ID: 3, Type: "u32"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "2"}}},
			{Code: optir.OpIntAdd, Results: []optir.Value{{ID: 4, Type: "u32"}}, Operands: []optir.ValueID{2, 3}},
		}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{1}},
	}}}
	plan, err := optir.PlanRegisters(cfg, []int{5}, nil)
	if err != nil {
		t.Fatal(err)
	}
	if _, spilled := plan.Spills[1]; !spilled {
		t.Fatalf("test CFG did not spill returned value 1: %+v", plan)
	}
	lowered, err := lowerOptIRRV64WithRegisters(cfg, &asm.Function{Name: "spilled_return", Arch: asm.ArchRV64, Signature: declaration, Fallback: true}, []int{5})
	if err != nil {
		t.Fatal(err)
	}
	if findings := asm.Check(lowered, declaration, nil); len(findings) != 0 {
		t.Fatalf("spilled-return body fails seam check: %v\n%s", findings, text(lowered.Items))
	}
	if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("spilled-return body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, text(lowered.Items))
	}
	reloadedIntoResult := false
	for _, item := range lowered.Items {
		instruction, ok := item.(asm.Instruction)
		if !ok || instruction.Mnemonic != "lw" || len(instruction.Operands) == 0 {
			continue
		}
		register, ok := instruction.Operands[0].(asm.Register)
		reloadedIntoResult = reloadedIntoResult || ok && register.Num == 10
	}
	if !reloadedIntoResult {
		t.Fatalf("spilled return was not reloaded into a0:\n%s", text(lowered.Items))
	}
}

func TestLowerOptIRRV64MaterializesSpillsAcrossSSAEdgesAndRefusesLoopsAndCalls(t *testing.T) {
	branchDeclaration := optIRRV64Declaration(t, `
spilled_branch: (): i8 = true ? i8(120) | i8(-120)
`)
	branchCFG := optir.CFG{Name: "spilled_branch", Entry: 0, Results: []optir.Type{"i8"}, Blocks: []optir.Block{
		{ID: 0, Operations: []optir.Operation{
			{Code: optir.OpConstBool, Results: []optir.Value{{ID: 1, Type: optir.TypeBool}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "true"}}},
			{Code: optir.OpConstInt, Results: []optir.Value{{ID: 2, Type: "i8"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "120"}}},
			{Code: optir.OpConstInt, Results: []optir.Value{{ID: 3, Type: "i8"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "-120"}}},
		}, Terminator: optir.Terminator{Kind: optir.TerminatorCondBranch, Condition: 1, True: optir.Edge{Target: 1, Arguments: []optir.ValueID{2}}, False: optir.Edge{Target: 1, Arguments: []optir.ValueID{3}}}},
		{ID: 1, Parameters: []optir.Value{{ID: 4, Type: "i8", Name: "result"}}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{4}}},
	}}
	branchPlan, err := optir.PlanRegisters(branchCFG, []int{5}, nil)
	if err != nil {
		t.Fatal(err)
	}
	if _, spilled := branchPlan.Spills[1]; !spilled {
		t.Fatalf("test plan did not spill the Bool condition: %+v", branchPlan.Spills)
	}
	branchBody, err := lowerOptIRRV64WithRegisters(branchCFG, &asm.Function{Name: "spilled_branch", Arch: asm.ArchRV64, Signature: branchDeclaration}, []int{5})
	if err != nil {
		t.Fatal(err)
	}
	if findings := asm.Check(branchBody, branchDeclaration, nil); len(findings) != 0 {
		t.Fatalf("spilled branch body fails seam check: %v\n%s", findings, text(branchBody.Items))
	}
	if verdict := asm.Verify(branchBody, branchDeclaration, branchDeclaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("spilled branch body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, text(branchBody.Items))
	}
	branchText := text(branchBody.Items)
	if !strings.Contains(branchText, "sb ") || !strings.Contains(branchText, "lb ") || !strings.Contains(branchText, "lbu t5") {
		t.Fatalf("spilled branch lacks edge store/reload traffic:\n%s", branchText)
	}

	loopCFG := optir.CFG{Name: "spilled_loop", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{
		{ID: 0, Operations: []optir.Operation{
			{Code: optir.OpConstInt, Results: []optir.Value{{ID: 1, Type: "u32"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "1"}}},
			{Code: optir.OpConstInt, Results: []optir.Value{{ID: 2, Type: "u32"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "2"}}},
		}, Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 1, Arguments: []optir.ValueID{1, 2}}}},
		{ID: 1, Parameters: []optir.Value{{ID: 3, Type: "u32", Name: "x"}, {ID: 4, Type: "u32", Name: "y"}}, Operations: []optir.Operation{
			{Code: optir.OpIntAdd, Results: []optir.Value{{ID: 5, Type: "u32"}}, Operands: []optir.ValueID{3, 4}},
			{Code: optir.OpConstBool, Results: []optir.Value{{ID: 6, Type: optir.TypeBool}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "false"}}},
		}, Terminator: optir.Terminator{Kind: optir.TerminatorCondBranch, Condition: 6, True: optir.Edge{Target: 1, Arguments: []optir.ValueID{5, 4}}, False: optir.Edge{Target: 2, Arguments: []optir.ValueID{5}}}},
		{ID: 2, Parameters: []optir.Value{{ID: 7, Type: "u32", Name: "result"}}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{7}}},
	}}
	loopDeclaration := optIRRV64Declaration(t, `
spilled_loop: (): u32 = u32(3)
`)
	if _, err := lowerOptIRRV64WithRegisters(loopCFG, &asm.Function{Name: "spilled_loop", Arch: asm.ArchRV64, Signature: loopDeclaration}, []int{5}); err == nil || !strings.Contains(err.Error(), "cyclic control flow") {
		t.Fatalf("spilled loop refusal = %v", err)
	}

	declarations := optIRRV64Declarations(t, `
add: (x: u32, y: u32): u32 = x + y
spilled_call: (): u32 = add(u32(20), u32(22))
`)
	callCFG := optir.CFG{Name: "spilled_call", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
		ID: 0, Operations: []optir.Operation{
			{Code: optir.OpConstInt, Results: []optir.Value{{ID: 1, Type: "u32"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "20"}}},
			{Code: optir.OpConstInt, Results: []optir.Value{{ID: 2, Type: "u32"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "22"}}},
			{Code: optir.OpCall, Results: []optir.Value{{ID: 3, Type: "u32"}}, Operands: []optir.ValueID{1, 2}, Effects: []optir.Effect{optir.EffectCall}, Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "add"}}},
		}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{3}},
	}}}
	callTemplate := &asm.Function{Name: "spilled_call", Arch: asm.ArchRV64, Signature: declarations["spilled_call"], Callees: map[string]*ast.FunctionStatement{"add": declarations["add"]}}
	if _, err := lowerOptIRRV64WithRegisters(callCFG, callTemplate, []int{5}); err == nil || !strings.Contains(err.Error(), "refuses calls and effects") {
		t.Fatalf("spilled call refusal = %v", err)
	}
}

func TestLowerOptIRRV64RefusesCallsOutsideClosedScalarSubset(t *testing.T) {
	declarations := optIRRV64Declarations(t, `
inc: (x: u32): u32 = x + u32(1)
add: (x: u32, y: u32): u32 = x + y
caller: (x: u32, y: u32): u32 = inc(x) + y
`)
	call := func(callee string, operands []optir.ValueID) optir.Operation {
		return optir.Operation{
			Code: optir.OpCall, Results: []optir.Value{{ID: 3, Type: "u32"}}, Operands: operands, Effects: []optir.Effect{optir.EffectCall},
			Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: callee}},
		}
	}
	template := func() *asm.Function {
		return &asm.Function{
			Name: "caller", Arch: asm.ArchRV64, Signature: declarations["caller"],
			Bindings: []asm.Binding{{Register: optIRRV64Register(10), Param: "x"}, {Register: optIRRV64Register(11), Param: "y"}},
			Callees:  map[string]*ast.FunctionStatement{"inc": declarations["inc"], "add": declarations["add"]},
		}
	}
	base := func(operation optir.Operation) optir.CFG {
		return optir.CFG{Name: "caller", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
			ID: 0, Parameters: []optir.Value{{ID: 1, Type: "u32", Name: "x"}, {ID: 2, Type: "u32", Name: "y"}},
			Operations: []optir.Operation{operation}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{3}},
		}}}
	}
	for name, test := range map[string]struct {
		cfg  optir.CFG
		edit func(*asm.Function)
		want string
	}{
		"unknown callee": {cfg: base(call("missing", []optir.ValueID{1})), edit: func(*asm.Function) {}, want: "not a known direct Oak function"},
		"opaque callee": {
			cfg: base(call("inc", []optir.ValueID{1})), edit: func(template *asm.Function) {
				opaque := *template.Callees["inc"]
				opaque.Body = nil
				template.Callees["inc"] = &opaque
			}, want: "not a known direct Oak function",
		},
	} {
		t.Run(name, func(t *testing.T) {
			selectedTemplate := template()
			test.edit(selectedTemplate)
			if _, err := LowerOptIRRV64(test.cfg, selectedTemplate); err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("call refusal = %v, want containing %q", err, test.want)
			}
		})
	}

	liveAcross := base(call("inc", []optir.ValueID{1}))
	liveAcross.Blocks[0].Operations = append(liveAcross.Blocks[0].Operations, optir.Operation{
		Code: optir.OpIntAdd, Results: []optir.Value{{ID: 4, Type: "u32"}}, Operands: []optir.ValueID{3, 2},
	})
	liveAcross.Blocks[0].Terminator.Values = []optir.ValueID{4}
	if _, err := LowerOptIRRV64(liveAcross, template()); err == nil || !strings.Contains(err.Error(), "live across") {
		t.Fatalf("live-across call refusal = %v", err)
	}

	malformedEffect := base(call("inc", []optir.ValueID{1}))
	malformedEffect.Blocks[0].Operations[0].Effects = nil
	if _, err := LowerOptIRRV64(malformedEffect, template()); err == nil || !strings.Contains(err.Error(), "effect evidence") {
		t.Fatalf("malformed call-effect refusal = %v", err)
	}

	tooManyDeclarations := optIRRV64Declarations(t, `
nine: (a: u32, b: u32, c: u32, d: u32, e: u32, f: u32, g: u32, h: u32, i: u32): u32 = i
too_many: (): u32 = nine(u32(1), u32(2), u32(3), u32(4), u32(5), u32(6), u32(7), u32(8), u32(9))
`)
	var operations []optir.Operation
	var operands []optir.ValueID
	for index := 0; index < 9; index++ {
		id := optir.ValueID(index + 1)
		operands = append(operands, id)
		operations = append(operations, optir.Operation{
			Code: optir.OpConstInt, Results: []optir.Value{{ID: id, Type: "u32"}},
			Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: strconv.Itoa(index + 1)}},
		})
	}
	operations = append(operations, optir.Operation{
		Code: optir.OpCall, Results: []optir.Value{{ID: 10, Type: "u32"}}, Operands: operands, Effects: []optir.Effect{optir.EffectCall},
		Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "nine"}},
	})
	tooManyCFG := optir.CFG{Name: "too_many", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
		ID: 0, Operations: operations, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{10}},
	}}}
	tooManyTemplate := &asm.Function{
		Name: "too_many", Arch: asm.ArchRV64, Signature: tooManyDeclarations["too_many"],
		Callees: map[string]*ast.FunctionStatement{"nine": tooManyDeclarations["nine"]},
	}
	if _, err := LowerOptIRRV64(tooManyCFG, tooManyTemplate); err == nil || !strings.Contains(err.Error(), "more than eight") {
		t.Fatalf("nine-argument call refusal = %v", err)
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
	for _, declaration := range optIRRV64Declarations(t, source) {
		return declaration
	}
	t.Fatal("source contains no function declaration")
	return nil
}

func optIRRV64Declarations(t *testing.T, source string) map[string]*ast.FunctionStatement {
	t.Helper()
	parsed := parser.New(layout.New(scanner.New(source)))
	program := parsed.ParseProgram()
	if errs := parsed.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	declarations := map[string]*ast.FunctionStatement{}
	for _, statement := range program.Statements {
		declaration, ok := statement.(*ast.FunctionStatement)
		if !ok || declaration.Name == nil {
			t.Fatalf("parsed declaration is %T", statement)
		}
		declarations[declaration.Name.Value] = declaration
	}
	return declarations
}
