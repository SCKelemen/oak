package machine

import (
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
add8: (x: u8, y: u8): u8 = x + y
call_inc8: (x: u8): u8 = inc8(x)
call_add8: (x: u8, y: u8): u8 = add8(x, y)
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
	t.Run("two arguments", func(t *testing.T) {
		call := baseCall()
		call.Operands = []optir.ValueID{1, 2}
		call.Results[0].ID = 3
		call.Attributes[0].Value = "add8"
		parameters := []optir.Value{{ID: 1, Type: "u8", Name: "x"}, {ID: 2, Type: "u8", Name: "y"}}
		bindings := []asm.Binding{{Register: w(0), Param: "x"}, {Register: w(1), Param: "y"}}
		if err := lower("call_add8", functions["call_add8"], parameters, bindings, []optir.Operation{call}, 3, map[string]*ast.FunctionStatement{"add8": functions["add8"]}); err == nil || !strings.Contains(err.Error(), "at most one") {
			t.Fatalf("multi-argument call error = %v", err)
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
