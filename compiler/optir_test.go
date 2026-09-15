package compiler

import (
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/optir"
)

func optIRFunction(module OptIRModule, name string) (OptIRFunction, bool) {
	for _, function := range module.Functions {
		if function.Name == name {
			return function, true
		}
	}
	return OptIRFunction{}, false
}

func optIRReturnedValue(function OptIRFunction) (optir.SCCPValue, bool) {
	for _, block := range function.CFG.Blocks {
		if block.Terminator.Kind == optir.TerminatorReturn && len(block.Terminator.Values) == 1 {
			return function.Constants.Value(block.Terminator.Values[0])
		}
	}
	return optir.SCCPValue{}, false
}

func TestCheckedOakProjectionBuildsStructuredScalarOptIR(t *testing.T) {
	source := `
constant: (): u32 = u32(40) + u32(2)
short: (): Bool = false && true

select: (flag: Bool): u32 {
  value: u32 = u32(1)
  flag ? {
    value = u32(2)
  } | {
    value = u32(3)
  }
  value
}

count: (n: u32): u32 {
  i: u32 = u32(0)
  while i < n {
    i = i + u32(1)
  }
  i
}

fixed: (): u32 {
  i: u32 = u32(0)
  while i < u32(4) {
    i = i + u32(1)
  }
  i
}

common: (x: u32): u32 {
  left: u32 = x + u32(1)
  right: u32 = x + u32(1)
  dead: u32 = x * u32(2)
  left + right
}

at: (values: []u32): u32 = values[u32(0)]
main: (): i32 = 0
`
	compilation := New().WithSource("optir.oak", source)
	first, err := compilation.OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	second, err := compilation.OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(first, second) {
		t.Fatalf("OptIR projection is not deterministic:\nfirst:  %#v\nsecond: %#v", first, second)
	}

	constant, ok := optIRFunction(first, "constant")
	if !ok {
		t.Fatalf("constant was not projected: %+v", first.Refusals)
	}
	returned, ok := optIRReturnedValue(constant)
	if !ok || returned.State != optir.LatticeConstant || returned.Constant.Integer != "42" {
		t.Fatalf("constant SCCP result = %+v", returned)
	}

	short, ok := optIRFunction(first, "short")
	if !ok {
		t.Fatalf("short was not projected: %+v", first.Refusals)
	}
	returned, ok = optIRReturnedValue(short)
	if !ok || returned.State != optir.LatticeConstant || returned.Constant.Kind != optir.ConstantBool || returned.Constant.Bool {
		t.Fatalf("short-circuit SCCP result = %+v", returned)
	}
	if len(short.Constants.Branches) != 1 || short.Constants.Branches[0].Taken {
		t.Fatalf("short-circuit executable branch = %+v", short.Constants.Branches)
	}

	selected, ok := optIRFunction(first, "select")
	if !ok {
		t.Fatalf("select was not projected: %+v", first.Refusals)
	}
	seenIf := false
	for _, node := range selected.Structured.Body.Nodes {
		seenIf = seenIf || node.If != nil
	}
	if !seenIf {
		t.Fatalf("select lost structured branch: %#v", selected.Structured)
	}

	counted, ok := optIRFunction(first, "count")
	if !ok {
		t.Fatalf("count was not projected: %+v", first.Refusals)
	}
	seenLoop := false
	for _, node := range counted.Structured.Body.Nodes {
		if node.While != nil {
			seenLoop = true
			if len(node.While.Initial) != 1 || len(node.While.Results) != 1 || len(node.While.Condition.Arguments) != 1 || len(node.While.Body.Arguments) != 1 {
				t.Fatalf("count loop-carried shape = %#v", node.While)
			}
		}
	}
	if !seenLoop {
		t.Fatalf("count lost structured loop: %#v", counted.Structured)
	}
	if len(counted.Loops.Loops) != 1 || len(counted.Loops.Loops[0].Inductions) != 1 || counted.Loops.Loops[0].Inductions[0].Step != "1" || counted.Loops.Loops[0].Inductions[0].HasExactTripCount {
		t.Fatalf("count loop analysis = %+v", counted.Loops)
	}

	fixed, ok := optIRFunction(first, "fixed")
	if !ok {
		t.Fatalf("fixed was not projected: %+v", first.Refusals)
	}
	if len(fixed.Loops.Loops) != 1 || len(fixed.Loops.Loops[0].Inductions) != 1 || !fixed.Loops.Loops[0].Inductions[0].HasExactTripCount || fixed.Loops.Loops[0].Inductions[0].ExactTripCount != "4" {
		t.Fatalf("fixed loop analysis = %+v", fixed.Loops)
	}

	common, ok := optIRFunction(first, "common")
	if !ok {
		t.Fatalf("common was not projected: %+v", first.Refusals)
	}
	if common.Simplification.CSE.EliminatedOperations != 2 || common.Simplification.DCE.EliminatedOperations != 2 {
		t.Fatalf("common CSE/DCE report = %+v", common.Simplification)
	}
	if len(common.Simplified.Blocks) != 1 || len(common.Simplified.Blocks[0].Operations) != 3 {
		t.Fatalf("common simplified CFG = %#v", common.Simplified)
	}

	if len(first.Refusals) != 1 || first.Refusals[0].Function != "at" || !strings.Contains(first.Refusals[0].Reason, "parameter values") {
		t.Fatalf("memory-subset refusals = %+v", first.Refusals)
	}
}

func TestCheckedOakProjectionIncludesConcreteGenericSpecialization(t *testing.T) {
	module, err := New().WithSource("optir_generic.oak", `
increment[T]: (x: u32, witness: T): u32 = x + u32(1)
main: (): i32 = i32_bits_u32(increment(u32(41), u8(0)))
`).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	seen := false
	for _, function := range module.Functions {
		if strings.HasPrefix(function.Name, "increment_") {
			seen = true
			if len(function.Structured.Parameters) != 2 || function.Structured.Parameters[0].Type != "u32" || function.Structured.Parameters[1].Type != "u8" {
				t.Fatalf("specialized parameters = %#v", function.Structured.Parameters)
			}
		}
	}
	if !seen {
		t.Fatalf("generic specialization was not projected: functions=%+v refusals=%+v", module.Functions, module.Refusals)
	}
}

func TestCheckedOakProjectionRefusesUnmodeledLoopMutation(t *testing.T) {
	module, err := New().WithSource("optir_loop_refusal.oak", `
hidden: (): u32 {
  i: u32 = u32(0)
  while false {
    value: u32 = true ? {
      i = i + u32(1)
      i
    } | { i }
  }
  i
}
main: (): i32 = 0
`).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	if len(module.Refusals) != 1 || module.Refusals[0].Function != "hidden" || !strings.Contains(module.Refusals[0].Reason, "unsupported expression shape") {
		t.Fatalf("hidden loop mutation was not refused: %+v", module.Refusals)
	}
}
