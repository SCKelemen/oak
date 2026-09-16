package machine

import (
	"fmt"
	"math"
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/optir"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func TestLowerOptIRArm64MaterializesVerifiedSpills(t *testing.T) {
	const values = 20
	var source strings.Builder
	source.WriteString("pressure: (x: u32): u32 = {\n")
	for index := 1; index <= values; index++ {
		fmt.Fprintf(&source, "  v%d: u32 = x + u32(%d)\n", index, index)
	}
	source.WriteString("  ")
	for index := 1; index <= values; index++ {
		if index > 1 {
			source.WriteString(" + ")
		}
		fmt.Fprintf(&source, "v%d", index)
	}
	source.WriteString("\n}\n")

	parsed := parser.New(layout.New(scanner.New(source.String())))
	program := parsed.ParseProgram()
	if errs := parsed.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	declaration, ok := program.Statements[0].(*ast.FunctionStatement)
	if !ok {
		t.Fatalf("parsed declaration is %T", program.Statements[0])
	}
	template := &asm.Function{
		Name: "pressure", Arch: asm.ArchArm64, Signature: declaration, Fallback: true,
		Bindings: []asm.Binding{{Register: w(0), Param: "x"}},
	}
	cfg := optIRPressureCFG(values)
	if _, err := optir.ColorRegisters(cfg, optIRArm64Registers, map[optir.ValueID]int{1: 0}); err == nil {
		t.Fatal("test CFG did not exceed the strict register pool")
	}
	lowered, err := LowerOptIRArm64(cfg, template)
	if err != nil {
		t.Fatal(err)
	}
	if lowered.Frame == 0 || lowered.Frame%16 != 0 || lowered.Frame > optIRArm64MaxSpillFrame {
		t.Fatalf("materialized spill frame = %d", lowered.Frame)
	}
	body := text(lowered.Items)
	if !strings.Contains(body, "str ") || !strings.Contains(body, "ldr ") {
		t.Fatalf("high-pressure lowering did not materialize spills:\n%s", body)
	}
	if findings := asm.Check(lowered, declaration, map[string]bool{"pressure": true}); len(findings) != 0 {
		t.Fatalf("spilled body fails seam check: %v\n%s", findings, body)
	}
	if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("spilled body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, body)
	}
}

func TestLowerOptIRArm64RematerializesConstantSpills(t *testing.T) {
	const values = 20
	var source strings.Builder
	source.WriteString("constant_pressure: (): u32 = ")
	for index := 1; index <= values; index++ {
		if index > 1 {
			source.WriteString(" + ")
		}
		fmt.Fprintf(&source, "u32(%d)", index)
	}
	source.WriteString("\n")
	parsed := parser.New(layout.New(scanner.New(source.String())))
	program := parsed.ParseProgram()
	if errs := parsed.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	declaration := program.Statements[0].(*ast.FunctionStatement)
	cfg := optIRConstantPressureCFG(values)
	registers, err := optir.PlanRegisters(cfg, optIRArm64SpillRegisters, nil)
	if err != nil {
		t.Fatal(err)
	}
	_, baselineFrame, err := optIRArm64LayoutSpills(registers.Slots)
	if err != nil || baselineFrame == 0 {
		t.Fatalf("test plan has no physical spill baseline: frame=%d err=%v", baselineFrame, err)
	}
	rematerialization, err := optir.AnalyzeRematerialization(cfg, optIRArm64SpillRegisters, nil, registers)
	if err != nil {
		t.Fatal(err)
	}
	if len(rematerialization.Decisions) == 0 {
		t.Fatalf("test plan has no rematerializable constants: %+v", registers.Spills)
	}
	lowered, err := LowerOptIRArm64(cfg, &asm.Function{Name: cfg.Name, Arch: asm.ArchArm64, Signature: declaration, Fallback: true})
	if err != nil {
		t.Fatal(err)
	}
	body := text(lowered.Items)
	if lowered.Frame >= baselineFrame || strings.Contains(body, "ldr ") || strings.Contains(body, "str ") {
		t.Fatalf("constant rematerialization did not remove the spill frame/traffic: baseline=%d lowered=%d\n%s", baselineFrame, lowered.Frame, body)
	}
	if findings := asm.Check(lowered, declaration, map[string]bool{cfg.Name: true}); len(findings) != 0 {
		t.Fatalf("rematerialized body fails seam check: %v\n%s", findings, body)
	}
	if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("rematerialized body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, body)
	}
}

func TestLowerOptIRArm64RematerializesCopyChains(t *testing.T) {
	const values = 20
	var source strings.Builder
	source.WriteString("copy_pressure: (): u32 = ")
	for index := 1; index <= values; index++ {
		if index > 1 {
			source.WriteString(" + ")
		}
		fmt.Fprintf(&source, "u32(%d)", index)
	}
	source.WriteString("\n")
	parsed := parser.New(layout.New(scanner.New(source.String())))
	program := parsed.ParseProgram()
	if errs := parsed.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	declaration := program.Statements[0].(*ast.FunctionStatement)
	cfg := optIRConstantCopyPressureCFG(values)
	registers, err := optir.PlanRegisters(cfg, optIRArm64SpillRegisters, nil)
	if err != nil {
		t.Fatal(err)
	}
	_, baselineFrame, err := optIRArm64LayoutSpills(registers.Slots)
	if err != nil || baselineFrame == 0 {
		t.Fatalf("test plan has no physical spill baseline: frame=%d err=%v", baselineFrame, err)
	}
	rematerialization, err := optir.AnalyzeRematerialization(cfg, optIRArm64SpillRegisters, nil, registers)
	if err != nil {
		t.Fatal(err)
	}
	copyDecision := false
	for _, decision := range rematerialization.Decisions {
		copyDecision = copyDecision || decision.Code == optir.OpCopy
	}
	if !copyDecision {
		t.Fatalf("test plan has no rematerializable copy: decisions=%+v spills=%+v", rematerialization.Decisions, registers.Spills)
	}
	lowered, err := LowerOptIRArm64(cfg, &asm.Function{Name: cfg.Name, Arch: asm.ArchArm64, Signature: declaration, Fallback: true})
	if err != nil {
		t.Fatal(err)
	}
	body := text(lowered.Items)
	if lowered.Frame >= baselineFrame {
		t.Fatalf("copy rematerialization did not reduce the spill frame: baseline=%d lowered=%d\n%s", baselineFrame, lowered.Frame, body)
	}
	if findings := asm.Check(lowered, declaration, map[string]bool{cfg.Name: true}); len(findings) != 0 {
		t.Fatalf("copy-rematerialized body fails seam check: %v\n%s", findings, body)
	}
	if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("copy-rematerialized body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, body)
	}
}

func TestOptIRArm64RematerializationRefusesExpensiveConstants(t *testing.T) {
	const values = 20
	cfg := optIRExpensiveConstantPressureCFG(values)
	allocation, err := optIRArm64Allocate(cfg, optIRTypes(cfg), nil)
	if err != nil {
		t.Fatal(err)
	}
	if len(allocation.rematerializations) != 0 {
		t.Fatalf("four-instruction constants were rematerialized for one use: %+v", allocation.rematerializations)
	}
	if allocation.frame == 0 {
		t.Fatal("conservatively retained expensive constants have no spill frame")
	}
}

func optIRConstantPressureCFG(values int) optir.CFG {
	block := optir.Block{ID: 0}
	terms := make([]optir.ValueID, 0, values)
	for index := 1; index <= values; index++ {
		value := optir.ValueID(index)
		block.Operations = append(block.Operations, optir.Operation{
			Code: optir.OpConstInt, Results: []optir.Value{{ID: value, Type: "u32"}},
			Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: fmt.Sprint(index)}},
		})
		terms = append(terms, value)
	}
	next, result := optir.ValueID(values+1), terms[0]
	for _, term := range terms[1:] {
		block.Operations = append(block.Operations, optir.Operation{
			Code: optir.OpIntAdd, Results: []optir.Value{{ID: next, Type: "u32"}}, Operands: []optir.ValueID{result, term},
		})
		result = next
		next++
	}
	block.Terminator = optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{result}}
	return optir.CFG{Name: "constant_pressure", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{block}}
}

func optIRConstantCopyPressureCFG(values int) optir.CFG {
	block := optir.Block{ID: 0}
	for index := 1; index <= values; index++ {
		block.Operations = append(block.Operations, optir.Operation{
			Code: optir.OpConstInt, Results: []optir.Value{{ID: optir.ValueID(index), Type: "u32"}},
			Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: fmt.Sprint(index)}},
		})
	}
	terms := make([]optir.ValueID, 0, values)
	for index := 1; index <= values; index++ {
		copy := optir.ValueID(values + index)
		block.Operations = append(block.Operations, optir.Operation{
			Code: optir.OpCopy, Results: []optir.Value{{ID: copy, Type: "u32"}}, Operands: []optir.ValueID{optir.ValueID(index)},
		})
		terms = append(terms, copy)
	}
	next, result := optir.ValueID(2*values+1), terms[0]
	for _, term := range terms[1:] {
		block.Operations = append(block.Operations, optir.Operation{
			Code: optir.OpIntAdd, Results: []optir.Value{{ID: next, Type: "u32"}}, Operands: []optir.ValueID{result, term},
		})
		result = next
		next++
	}
	block.Terminator = optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{result}}
	return optir.CFG{Name: "copy_pressure", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{block}}
}

func optIRExpensiveConstantPressureCFG(values int) optir.CFG {
	const base uint64 = 0x123456789abcdef0
	block := optir.Block{ID: 0}
	terms := make([]optir.ValueID, 0, values)
	for index := 0; index < values; index++ {
		value := optir.ValueID(index + 1)
		block.Operations = append(block.Operations, optir.Operation{
			Code: optir.OpConstInt, Results: []optir.Value{{ID: value, Type: "u64"}},
			Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: fmt.Sprint(base + uint64(index))}},
		})
		terms = append(terms, value)
	}
	next, result := optir.ValueID(values+1), terms[0]
	for _, term := range terms[1:] {
		block.Operations = append(block.Operations, optir.Operation{
			Code: optir.OpIntAdd, Results: []optir.Value{{ID: next, Type: "u64"}}, Operands: []optir.ValueID{result, term},
		})
		result = next
		next++
	}
	block.Terminator = optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{result}}
	return optir.CFG{Name: "expensive_constants", Entry: 0, Results: []optir.Type{"u64"}, Blocks: []optir.Block{block}}
}

func TestLowerOptIRArm64ComposesSpillsWithDirectCallFrame(t *testing.T) {
	const values = 20
	var source strings.Builder
	source.WriteString("inc_pressure: (x: u32): u32 = x + u32(1)\n")
	source.WriteString("call_pressure: (x: u32): u32 = {\n")
	for index := 1; index <= values; index++ {
		fmt.Fprintf(&source, "  v%d: u32 = x + u32(%d)\n", index, index)
	}
	source.WriteString("  inc_pressure(")
	for index := 1; index <= values; index++ {
		if index > 1 {
			source.WriteString(" + ")
		}
		fmt.Fprintf(&source, "v%d", index)
	}
	source.WriteString(")\n}\n")

	functions := parseOptIRArm64CallFunctions(t, source.String())
	callee, caller := functions["inc_pressure"], functions["call_pressure"]
	cfg := optIRPressureCFG(values)
	cfg.Name = "call_pressure"
	block := &cfg.Blocks[0]
	argument := block.Terminator.Values[0]
	result := optir.ValueID(3*values + 1)
	block.Operations = append(block.Operations, optir.Operation{
		Code: optir.OpCall, Results: []optir.Value{{ID: result, Type: "u32"}}, Operands: []optir.ValueID{argument},
		Effects: []optir.Effect{optir.EffectCall}, Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "inc_pressure"}},
	})
	block.Terminator.Values[0] = result
	if _, err := optir.ColorRegisters(cfg, optIRArm64Registers, map[optir.ValueID]int{1: 0}); err == nil {
		t.Fatal("test CFG did not exceed the strict register pool")
	}
	template := &asm.Function{
		Name: cfg.Name, Arch: asm.ArchArm64, Signature: caller, Fallback: true,
		Bindings: []asm.Binding{{Register: w(0), Param: "x"}},
		Callees:  map[string]*ast.FunctionStatement{"inc_pressure": callee},
	}
	lowered, err := LowerOptIRArm64(cfg, template)
	if err != nil {
		t.Fatal(err)
	}
	body := text(lowered.Items)
	if lowered.Frame <= 16 || lowered.Frame%16 != 0 || !strings.Contains(body, "bl inc_pressure") {
		t.Fatalf("spill/call frame was not composed: frame=%d\n%s", lowered.Frame, body)
	}
	if strings.Contains(body, "[sp,#-16]!") || strings.Contains(body, "[sp],#16") {
		t.Fatalf("spill/call body unexpectedly uses a second pre/post-index frame:\n%s", body)
	}
	if findings := asm.Check(lowered, caller, map[string]bool{"inc_pressure": true}); len(findings) != 0 {
		t.Fatalf("spill/call body fails seam check: %v\n%s", findings, body)
	}
	if verdict := asm.Verify(lowered, caller, caller.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("spill/call body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, body)
	}
}

func TestLowerOptIRArm64SpillsPreserveNarrowRepresentations(t *testing.T) {
	for _, test := range []struct {
		typ, store, load string
	}{
		{typ: "u8", store: "strb", load: "ldrb"},
		{typ: "i8", store: "strb", load: "ldrsb"},
		{typ: "u16", store: "strh", load: "ldrh"},
		{typ: "i16", store: "strh", load: "ldrsh"},
	} {
		t.Run(test.typ, func(t *testing.T) {
			const values = 18
			var source strings.Builder
			fmt.Fprintf(&source, "pressure_%s: (x: %s): %s = {\n", test.typ, test.typ, test.typ)
			for index := 1; index <= values; index++ {
				fmt.Fprintf(&source, "  v%d: %s = x + %s(%d)\n", index, test.typ, test.typ, index)
			}
			source.WriteString("  ")
			for index := 1; index <= values; index++ {
				if index > 1 {
					source.WriteString(" + ")
				}
				fmt.Fprintf(&source, "v%d", index)
			}
			source.WriteString("\n}\n")
			parsed := parser.New(layout.New(scanner.New(source.String())))
			program := parsed.ParseProgram()
			if errs := parsed.Errors(); len(errs) != 0 {
				t.Fatal(errs)
			}
			declaration := program.Statements[0].(*ast.FunctionStatement)
			cfg := optIRTypedPressureCFG("pressure_"+test.typ, optir.Type(test.typ), values)
			template := &asm.Function{
				Name: cfg.Name, Arch: asm.ArchArm64, Signature: declaration, Fallback: true,
				Bindings: []asm.Binding{{Register: w(0), Param: "x"}},
			}
			lowered, err := LowerOptIRArm64(cfg, template)
			if err != nil {
				t.Fatal(err)
			}
			body := text(lowered.Items)
			if !strings.Contains(body, test.store+" ") || !strings.Contains(body, test.load+" ") {
				t.Fatalf("%s spills do not use %s/%s:\n%s", test.typ, test.store, test.load, body)
			}
			if findings := asm.Check(lowered, declaration, map[string]bool{cfg.Name: true}); len(findings) != 0 {
				t.Fatalf("%s spilled body fails seam check: %v\n%s", test.typ, findings, body)
			}
			if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
				t.Fatalf("%s spilled body verdict = %s (%s)\n%s", test.typ, verdict.Kind, verdict.Message, body)
			}
		})
	}
}

func TestOptIRArm64SpillLayoutFailsClosed(t *testing.T) {
	var oversized []optir.SpillSlot
	for id := 1; id <= 511; id++ {
		oversized = append(oversized, optir.SpillSlot{ID: optir.SpillSlotID(id), WidthBytes: 8, AlignmentBytes: 8, Values: []optir.ValueID{optir.ValueID(id)}})
	}
	if _, _, err := optIRArm64LayoutSpills(oversized); err == nil || !strings.Contains(err.Error(), "spill frame needs") {
		t.Fatalf("oversized frame error = %v", err)
	}
	if _, _, err := optIRArm64LayoutSpills([]optir.SpillSlot{{ID: 1, WidthBytes: 3, AlignmentBytes: 3, Values: []optir.ValueID{1}}}); err == nil || !strings.Contains(err.Error(), "unsupported") {
		t.Fatalf("unsupported slot error = %v", err)
	}
	if _, ok := optIRCheckedAlign(math.MaxInt64, 16); ok {
		t.Fatal("overflowing frame alignment was accepted")
	}
}

func TestLowerOptIRArm64SpillsAcrossSSAEdges(t *testing.T) {
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
	parsed := parser.New(layout.New(scanner.New(source.String())))
	program := parsed.ParseProgram()
	if errs := parsed.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	declaration := program.Statements[0].(*ast.FunctionStatement)
	cfg := optIREdgePressureCFG(values)
	fixed := map[optir.ValueID]int{1: 0}
	plan, err := optir.PlanRegisters(cfg, optIRArm64SpillRegisters, fixed)
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
		Name: cfg.Name, Arch: asm.ArchArm64, Signature: declaration, Fallback: true,
		Bindings: []asm.Binding{{Register: w(0), Param: "flag"}},
	}
	lowered, err := LowerOptIRArm64(cfg, template)
	if err != nil {
		t.Fatal(err)
	}
	body := text(lowered.Items)
	if lowered.Frame == 0 || !strings.Contains(body, "str ") || !strings.Contains(body, "ldr ") {
		t.Fatalf("edge lowering did not materialize spilled parallel copies:\n%s", body)
	}
	if findings := asm.Check(lowered, declaration, map[string]bool{cfg.Name: true}); len(findings) != 0 {
		t.Fatalf("spilled edge body fails seam check: %v\n%s", findings, body)
	}
	if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("spilled edge body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, body)
	}
}

func optIREdgePressureCFG(values int) optir.CFG {
	entry := optir.Block{ID: 0, Parameters: []optir.Value{{ID: 1, Type: optir.TypeBool, Name: "flag"}}, Terminator: optir.Terminator{
		Kind: optir.TerminatorCondBranch, Condition: 1, True: optir.Edge{Target: 1}, False: optir.Edge{Target: 2},
	}}
	next := optir.ValueID(2)
	branch := func(id optir.BlockID, start int) optir.Block {
		block := optir.Block{ID: id}
		for index := 0; index < values; index++ {
			value := next
			next++
			block.Operations = append(block.Operations, optir.Operation{
				Code: optir.OpConstInt, Results: []optir.Value{{ID: value, Type: "u32"}},
				Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: fmt.Sprint(start + index)}},
			})
			block.Terminator.True.Arguments = append(block.Terminator.True.Arguments, value)
		}
		block.Terminator.Kind = optir.TerminatorBranch
		block.Terminator.True.Target = 3
		return block
	}
	left, right := branch(1, 1), branch(2, 2)
	merge := optir.Block{ID: 3}
	for index := 0; index < values; index++ {
		merge.Parameters = append(merge.Parameters, optir.Value{ID: optir.ValueID(100 + index), Type: "u32", Name: fmt.Sprintf("v%d", index+1)})
	}
	result := merge.Parameters[0].ID
	for _, parameter := range merge.Parameters[1:] {
		sum := optir.ValueID(200 + len(merge.Operations))
		merge.Operations = append(merge.Operations, optir.Operation{Code: optir.OpIntAdd, Results: []optir.Value{{ID: sum, Type: "u32"}}, Operands: []optir.ValueID{result, parameter.ID}})
		result = sum
	}
	merge.Terminator = optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{result}}
	return optir.CFG{Name: "edge_pressure", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{entry, left, right, merge}}
}

func optIRPressureCFG(values int) optir.CFG {
	return optIRTypedPressureCFG("pressure", "u32", values)
}

func optIRTypedPressureCFG(name string, typ optir.Type, values int) optir.CFG {
	cfg := optir.CFG{Name: name, Entry: 0, Results: []optir.Type{typ}}
	block := optir.Block{ID: 0, Parameters: []optir.Value{{ID: 1, Type: typ, Name: "x"}}}
	next := optir.ValueID(2)
	terms := make([]optir.ValueID, 0, values)
	for index := 1; index <= values; index++ {
		constant := next
		next++
		term := next
		next++
		block.Operations = append(block.Operations,
			optir.Operation{Code: optir.OpConstInt, Results: []optir.Value{{ID: constant, Type: typ}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: fmt.Sprint(index)}}},
			optir.Operation{Code: optir.OpIntAdd, Results: []optir.Value{{ID: term, Type: typ}}, Operands: []optir.ValueID{1, constant}},
		)
		terms = append(terms, term)
	}
	result := terms[0]
	for _, term := range terms[1:] {
		sum := next
		next++
		block.Operations = append(block.Operations, optir.Operation{Code: optir.OpIntAdd, Results: []optir.Value{{ID: sum, Type: typ}}, Operands: []optir.ValueID{result, term}})
		result = sum
	}
	block.Terminator = optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{result}}
	cfg.Blocks = []optir.Block{block}
	return cfg
}

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
	var labelOrder []string
	boolNormalized := false
	for _, item := range lowered.Items {
		switch item := item.(type) {
		case asm.Label:
			labels++
			if strings.HasPrefix(item.Name, "optir_b") {
				labelOrder = append(labelOrder, item.Name)
			}
		case asm.Instruction:
			if item.Mnemonic == "b" || item.Mnemonic == "cbz" || item.Mnemonic == "cbnz" {
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
	if branches != 2 || labels != 4 {
		t.Fatalf("SSA layout should need two branches and four labels, got %d branches, %d labels\n%s", branches, labels, text(lowered.Items))
	}
	if want := []string{"optir_b0", "optir_b1", "optir_b2", "optir_b3"}; !reflect.DeepEqual(labelOrder, want) {
		t.Fatalf("SSA diamond layout = %v, want %v\n%s", labelOrder, want, text(lowered.Items))
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

func TestLowerOptIRArm64VerifiesDirectScalarCall(t *testing.T) {
	functions := parseOptIRArm64CallFunctions(t, `
inc8: (x: u8): u8 = x + u8(1)
call_inc8: (x: u8): u8 = inc8(x)
`)
	callee, caller := functions["inc8"], functions["call_inc8"]
	template := &asm.Function{
		Name: "call_inc8", Arch: asm.ArchArm64, Signature: caller, Fallback: true,
		Bindings: []asm.Binding{{Register: w(0), Param: "x"}},
		Callees:  map[string]*ast.FunctionStatement{"inc8": callee},
	}
	cfg := optir.CFG{
		Name: "call_inc8", Entry: 0, Results: []optir.Type{"u8"},
		Blocks: []optir.Block{{
			ID: 0, Parameters: []optir.Value{{ID: 1, Type: "u8", Name: "x"}},
			Operations: []optir.Operation{{
				Code: optir.OpCall, Results: []optir.Value{{ID: 2, Type: "u8"}}, Operands: []optir.ValueID{1},
				Effects: []optir.Effect{optir.EffectCall}, Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "inc8"}},
			}},
			Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{2}},
		}},
	}
	lowered, err := LowerOptIRArm64(cfg, template)
	if err != nil {
		t.Fatal(err)
	}
	if findings := asm.Check(lowered, caller, map[string]bool{"inc8": true}); len(findings) != 0 {
		t.Fatalf("selected call body fails seam check: %v\n%s", findings, text(lowered.Items))
	}
	if verdict := asm.Verify(lowered, caller, caller.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("selected call body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, text(lowered.Items))
	}
	if lowered.Frame != 16 {
		t.Fatalf("call body frame = %d, want 16", lowered.Frame)
	}
	clobbersLink := false
	for _, register := range lowered.Clobbers {
		clobbersLink = clobbersLink || register.Num == 30
	}
	savesLink, restoresLink := false, false
	for _, item := range lowered.Items {
		instruction, ok := item.(asm.Instruction)
		if !ok || len(instruction.Operands) != 2 {
			continue
		}
		register, registerOK := instruction.Operands[0].(asm.Register)
		memory, memoryOK := instruction.Operands[1].(asm.Memory)
		if !registerOK || !memoryOK || register.Num != 30 || memory.Base.Class != asm.ClassSP {
			continue
		}
		savesLink = savesLink || instruction.Mnemonic == "str" && memory.Mode == asm.MemPreIndex && memory.Offset == -16
		restoresLink = restoresLink || instruction.Mnemonic == "ldr" && memory.Mode == asm.MemPostIndex && memory.Offset == 16
	}
	body := text(lowered.Items)
	if !clobbersLink || !savesLink || !restoresLink || !strings.Contains(body, "bl inc8") || !strings.Contains(body, "uxtb w0, w0") {
		t.Fatalf("direct call lacks its frame, ABI normalization, or link-register contract:\nclobbers=%v\n%s", lowered.Clobbers, body)
	}
}

func TestLowerOptIRArm64VerifiesDirectCallArgumentSwap(t *testing.T) {
	functions := parseOptIRArm64CallFunctions(t, `
subtract: (left: u32, right: u32): u32 = left - right
call_swapped: (x: u32, y: u32): u32 = subtract(y, x)
`)
	callee, caller := functions["subtract"], functions["call_swapped"]
	template := &asm.Function{
		Name: "call_swapped", Arch: asm.ArchArm64, Signature: caller, Fallback: true,
		Bindings: []asm.Binding{{Register: w(0), Param: "x"}, {Register: w(1), Param: "y"}},
		Callees:  map[string]*ast.FunctionStatement{"subtract": callee},
	}
	cfg := optir.CFG{
		Name: "call_swapped", Entry: 0, Results: []optir.Type{"u32"},
		Blocks: []optir.Block{{
			ID: 0, Parameters: []optir.Value{{ID: 1, Type: "u32", Name: "x"}, {ID: 2, Type: "u32", Name: "y"}},
			Operations: []optir.Operation{{
				Code: optir.OpCall, Results: []optir.Value{{ID: 3, Type: "u32"}}, Operands: []optir.ValueID{2, 1},
				Effects: []optir.Effect{optir.EffectCall}, Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "subtract"}},
			}},
			Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{3}},
		}},
	}
	lowered, err := LowerOptIRArm64(cfg, template)
	if err != nil {
		t.Fatal(err)
	}
	if findings := asm.Check(lowered, caller, map[string]bool{"subtract": true}); len(findings) != 0 {
		t.Fatalf("selected swapped call fails seam check: %v\n%s", findings, text(lowered.Items))
	}
	if verdict := asm.Verify(lowered, caller, caller.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("selected swapped call verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, text(lowered.Items))
	}
	body := text(lowered.Items)
	for _, instruction := range []string{"mov x17, x0", "mov w0, w1", "mov w1, w17", "bl subtract"} {
		if !strings.Contains(body, instruction) {
			t.Fatalf("swapped call lacks cycle-safe move %q:\n%s", instruction, body)
		}
	}
	scratchClobbered := false
	for _, register := range lowered.Clobbers {
		scratchClobbered = scratchClobbered || register.Num == optIRCopyScratch
	}
	if !scratchClobbered {
		t.Fatalf("swapped call did not declare x17 scratch: %v", lowered.Clobbers)
	}
}

func TestLowerOptIRArm64CallsWithEightScalarRegisterArgumentsAndVerifies(t *testing.T) {
	functions := parseOptIRArm64CallFunctions(t, `
eighth: (a: u32, b: u32, c: u32, d: u32, e: u32, f: u32, g: u32, h: u32): u32 = h
call_eighth: (a: u32, b: u32, c: u32, d: u32, e: u32, f: u32, g: u32, h: u32): u32 = eighth(a, b, c, d, e, f, g, h)
`)
	caller := functions["call_eighth"]
	template := &asm.Function{
		Name: "call_eighth", Arch: asm.ArchArm64, Signature: caller, Fallback: true,
		Callees: map[string]*ast.FunctionStatement{"eighth": functions["eighth"]},
	}
	parameters := make([]optir.Value, 8)
	operands := make([]optir.ValueID, 8)
	for index, name := range []string{"a", "b", "c", "d", "e", "f", "g", "h"} {
		id := optir.ValueID(index + 1)
		parameters[index] = optir.Value{ID: id, Type: "u32", Name: name}
		operands[index] = id
		template.Bindings = append(template.Bindings, asm.Binding{Register: w(index), Param: name})
	}
	cfg := optir.CFG{Name: "call_eighth", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
		ID: 0, Parameters: parameters, Operations: []optir.Operation{{
			Code: optir.OpCall, Results: []optir.Value{{ID: 9, Type: "u32"}}, Operands: operands, Effects: []optir.Effect{optir.EffectCall},
			Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "eighth"}},
		}}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{9}},
	}}}
	lowered, err := LowerOptIRArm64(cfg, template)
	if err != nil {
		t.Fatal(err)
	}
	if findings := asm.Check(lowered, caller, map[string]bool{"eighth": true}); len(findings) != 0 {
		t.Fatalf("selected eight-argument call fails seam check: %v\n%s", findings, text(lowered.Items))
	}
	if verdict := asm.Verify(lowered, caller, caller.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("selected eight-argument call verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, text(lowered.Items))
	}
}

func TestLowerOptIRArm64VerifiesZeroArgumentBoolCall(t *testing.T) {
	functions := parseOptIRArm64CallFunctions(t, `
truth: (): Bool = true
call_truth: (): Bool = truth()
`)
	callee, caller := functions["truth"], functions["call_truth"]
	template := &asm.Function{
		Name: "call_truth", Arch: asm.ArchArm64, Signature: caller, Fallback: true,
		Callees: map[string]*ast.FunctionStatement{"truth": callee},
	}
	cfg := optir.CFG{
		Name: "call_truth", Entry: 0, Results: []optir.Type{optir.TypeBool},
		Blocks: []optir.Block{{
			ID: 0,
			Operations: []optir.Operation{{
				Code: optir.OpCall, Results: []optir.Value{{ID: 1, Type: optir.TypeBool}},
				Effects: []optir.Effect{optir.EffectCall}, Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "truth"}},
			}},
			Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{1}},
		}},
	}
	lowered, err := LowerOptIRArm64(cfg, template)
	if err != nil {
		t.Fatal(err)
	}
	if findings := asm.Check(lowered, caller, map[string]bool{"truth": true}); len(findings) != 0 {
		t.Fatalf("selected zero-argument call fails seam check: %v\n%s", findings, text(lowered.Items))
	}
	if verdict := asm.Verify(lowered, caller, caller.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("selected zero-argument call verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, text(lowered.Items))
	}
	body := text(lowered.Items)
	if !strings.Contains(body, "bl truth") || !strings.Contains(body, "and w0, w0, #1") {
		t.Fatalf("zero-argument Bool call lacks result normalization:\n%s", body)
	}
}

func TestLowerOptIRArm64RefusesCallsOutsideClosedSlice(t *testing.T) {
	functions := parseOptIRArm64CallFunctions(t, `
inc8: (x: u8): u8 = x + u8(1)
inc32: (x: u32): u32 = x + u32(1)
nine: (a: u8, b: u8, c: u8, d: u8, e: u8, f: u8, g: u8, h: u8, i: u8): u8 = a
call_inc8: (x: u8): u8 = inc8(x)
call_nine: (): u8 = nine(u8(0), u8(1), u8(2), u8(3), u8(4), u8(5), u8(6), u8(7), u8(8))
`)
	baseCall := func() optir.Operation {
		return optir.Operation{
			Code: optir.OpCall, Results: []optir.Value{{ID: 2, Type: "u8"}}, Operands: []optir.ValueID{1},
			Effects: []optir.Effect{optir.EffectCall}, Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "inc8"}},
		}
	}
	lower := func(name string, declaration *ast.FunctionStatement, parameters []optir.Value, bindings []asm.Binding, operations []optir.Operation, result optir.ValueID, callees map[string]*ast.FunctionStatement) error {
		template := &asm.Function{Name: name, Arch: asm.ArchArm64, Signature: declaration, Bindings: bindings, Callees: callees}
		_, err := LowerOptIRArm64(optir.CFG{
			Name: name, Entry: 0, Results: []optir.Type{"u8"},
			Blocks: []optir.Block{{ID: 0, Parameters: parameters, Operations: operations, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{result}}}},
		}, template)
		return err
	}
	parameter := []optir.Value{{ID: 1, Type: "u8", Name: "x"}}
	binding := []asm.Binding{{Register: w(0), Param: "x"}}
	known := map[string]*ast.FunctionStatement{"inc8": functions["inc8"]}

	t.Run("unknown callee", func(t *testing.T) {
		if err := lower("call_inc8", functions["call_inc8"], parameter, binding, []optir.Operation{baseCall()}, 2, nil); err == nil || !strings.Contains(err.Error(), "known direct Oak callee") {
			t.Fatalf("unknown callee error = %v", err)
		}
	})
	t.Run("mismatched signature", func(t *testing.T) {
		call := baseCall()
		call.Attributes[0].Value = "inc32"
		if err := lower("call_inc8", functions["call_inc8"], parameter, binding, []optir.Operation{call}, 2, map[string]*ast.FunctionStatement{"inc32": functions["inc32"]}); err == nil || !strings.Contains(err.Error(), "Oak type") {
			t.Fatalf("mismatched callee error = %v", err)
		}
	})
	t.Run("nine arguments", func(t *testing.T) {
		operations := make([]optir.Operation, 0, 10)
		operands := make([]optir.ValueID, 0, 9)
		for index := 0; index < 9; index++ {
			id := optir.ValueID(index + 1)
			operands = append(operands, id)
			operations = append(operations, optir.Operation{
				Code: optir.OpConstInt, Results: []optir.Value{{ID: id, Type: "u8"}},
				Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: string(rune('0' + index))}},
			})
		}
		operations = append(operations, optir.Operation{
			Code: optir.OpCall, Results: []optir.Value{{ID: 10, Type: "u8"}}, Operands: operands,
			Effects: []optir.Effect{optir.EffectCall}, Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "nine"}},
		})
		if err := lower("call_nine", functions["call_nine"], nil, nil, operations, 10, map[string]*ast.FunctionStatement{"nine": functions["nine"]}); err == nil || !strings.Contains(err.Error(), "at most eight") {
			t.Fatalf("nine-argument call error = %v", err)
		}
	})
	t.Run("malformed effect", func(t *testing.T) {
		call := baseCall()
		call.Effects = nil
		if err := lower("call_inc8", functions["call_inc8"], parameter, binding, []optir.Operation{call}, 2, known); err == nil || !strings.Contains(err.Error(), "exactly the Control.Call effect") {
			t.Fatalf("malformed call effect error = %v", err)
		}
	})
	t.Run("extra attribute", func(t *testing.T) {
		call := baseCall()
		call.Attributes = append(call.Attributes, optir.Attribute{Name: optir.AttributeValue, Value: "not-call-metadata"})
		if err := lower("call_inc8", functions["call_inc8"], parameter, binding, []optir.Operation{call}, 2, known); err == nil || !strings.Contains(err.Error(), "exactly one callee") {
			t.Fatalf("extra call attribute error = %v", err)
		}
	})
	t.Run("live value", func(t *testing.T) {
		constant := optir.Operation{Code: optir.OpConstInt, Results: []optir.Value{{ID: 2, Type: "u8"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "7"}}}
		call := baseCall()
		call.Results[0].ID = 3
		add := optir.Operation{Code: optir.OpIntAdd, Results: []optir.Value{{ID: 4, Type: "u8"}}, Operands: []optir.ValueID{2, 3}}
		if err := lower("call_inc8", functions["call_inc8"], parameter, binding, []optir.Operation{constant, call, add}, 4, known); err == nil || !strings.Contains(err.Error(), "live across a call") {
			t.Fatalf("live-across call error = %v", err)
		}
	})
}

func parseOptIRArm64CallFunctions(t *testing.T, source string) map[string]*ast.FunctionStatement {
	t.Helper()
	parsed := parser.New(layout.New(scanner.New(source)))
	program := parsed.ParseProgram()
	if errs := parsed.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	functions := map[string]*ast.FunctionStatement{}
	for _, statement := range program.Statements {
		function, ok := statement.(*ast.FunctionStatement)
		if ok && function.Name != nil {
			functions[function.Name.Value] = function
		}
	}
	return functions
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
