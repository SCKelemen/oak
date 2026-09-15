package optir

import (
	"reflect"
	"strings"
	"testing"
)

func sccpValue(id ValueID, typ Type) Value {
	return Value{ID: id, Type: typ}
}

func integerConstant(id ValueID, typ Type, value string) Operation {
	return Operation{Code: OpConstInt, Results: []Value{sccpValue(id, typ)}, Attributes: []Attribute{{Name: AttributeValue, Value: value}}}
}

func TestSCCPFoldsOakFixedWidthArithmetic(t *testing.T) {
	cfg := CFG{
		Name:    "arithmetic",
		Entry:   0,
		Results: []Type{TypeBool},
		Blocks: []Block{{
			ID: 0,
			Operations: []Operation{
				integerConstant(1, "i8", "127"),
				integerConstant(2, "i8", "1"),
				{Code: OpIntAdd, Results: []Value{sccpValue(3, "i8")}, Operands: []ValueID{1, 2}},
				integerConstant(4, "i8", "-1"),
				{Code: OpIntDiv, Results: []Value{sccpValue(5, "i8")}, Operands: []ValueID{3, 4}, Effects: []Effect{EffectTrap}},
				{Code: OpIntRem, Results: []Value{sccpValue(6, "i8")}, Operands: []ValueID{3, 4}, Effects: []Effect{EffectTrap}},
				{Code: OpIntShr, Results: []Value{sccpValue(7, "i8")}, Operands: []ValueID{4, 2}, Effects: []Effect{EffectTrap}},
				integerConstant(8, "i8", "127"),
				{Code: OpEqual, Results: []Value{sccpValue(9, TypeBool)}, Operands: []ValueID{7, 8}},
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{9}},
		}},
	}
	result, err := AnalyzeSCCP(cfg)
	if err != nil {
		t.Fatal(err)
	}
	for id, want := range map[ValueID]string{3: "-128", 5: "-128", 6: "0", 7: "127"} {
		value, ok := result.Value(id)
		if !ok || value.State != LatticeConstant || value.Constant.Integer != want {
			t.Errorf("value %d = %+v, want integer %s", id, value, want)
		}
	}
	comparison, _ := result.Value(9)
	if comparison.State != LatticeConstant || !comparison.Constant.Bool {
		t.Fatalf("comparison = %+v, want true", comparison)
	}
}

func TestSCCPDiscoversOnlyTheConstantBranch(t *testing.T) {
	cfg := CFG{
		Name:    "branch",
		Entry:   0,
		Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Operations: []Operation{{Code: OpConstBool, Results: []Value{sccpValue(1, TypeBool)}, Attributes: []Attribute{{Name: AttributeValue, Value: "true"}}}}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: 2}}},
			{ID: 1, Operations: []Operation{integerConstant(2, "u32", "7")}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3, Arguments: []ValueID{2}}}},
			{ID: 2, Operations: []Operation{integerConstant(3, "u32", "9")}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3, Arguments: []ValueID{3}}}},
			{ID: 3, Parameters: []Value{sccpValue(4, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4}}},
		},
	}
	result, err := AnalyzeSCCP(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(result.ExecutableBlocks, []BlockID{0, 1, 3}) {
		t.Fatalf("executable blocks = %v", result.ExecutableBlocks)
	}
	if !reflect.DeepEqual(result.Branches, []SCCPBranch{{Block: 0, Condition: 1, Taken: true, Target: 1}}) {
		t.Fatalf("constant branches = %+v", result.Branches)
	}
	merged, _ := result.Value(4)
	if merged.State != LatticeConstant || merged.Constant.Integer != "7" {
		t.Fatalf("merge parameter = %+v", merged)
	}
	dead, _ := result.Value(3)
	if dead.State != LatticeUnknown {
		t.Fatalf("unreachable definition = %+v, want unknown", dead)
	}
}

func TestSCCPLoopCarriedJoinReachesOverdefinedFixedPoint(t *testing.T) {
	cfg := CFG{
		Name:    "loop",
		Entry:   0,
		Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Operations: []Operation{integerConstant(1, "u32", "0")}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1, Arguments: []ValueID{1}}}},
			{ID: 1, Parameters: []Value{sccpValue(2, "u32")}, Operations: []Operation{integerConstant(3, "u32", "3"), {Code: OpLess, Results: []Value{sccpValue(4, TypeBool)}, Operands: []ValueID{2, 3}}}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 4, True: Edge{Target: 2, Arguments: []ValueID{2}}, False: Edge{Target: 3, Arguments: []ValueID{2}}}},
			{ID: 2, Parameters: []Value{sccpValue(5, "u32")}, Operations: []Operation{integerConstant(6, "u32", "1"), {Code: OpIntAdd, Results: []Value{sccpValue(7, "u32")}, Operands: []ValueID{5, 6}}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1, Arguments: []ValueID{7}}}},
			{ID: 3, Parameters: []Value{sccpValue(8, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{8}}},
		},
	}
	result, err := AnalyzeSCCP(cfg)
	if err != nil {
		t.Fatal(err)
	}
	carried, _ := result.Value(2)
	if carried.State != LatticeOverdefined {
		t.Fatalf("header value = %+v, want overdefined", carried)
	}
	if !reflect.DeepEqual(result.ExecutableBlocks, []BlockID{0, 1, 2, 3}) {
		t.Fatalf("executable blocks = %v", result.ExecutableBlocks)
	}
}

func TestSCCPRejectsMalformedKnownOperationAttributes(t *testing.T) {
	cfg := CFG{
		Name:    "malformed",
		Entry:   0,
		Results: []Type{"u32"},
		Blocks:  []Block{{ID: 0, Operations: []Operation{{Code: OpConstInt, Results: []Value{sccpValue(1, "u32")}, Attributes: []Attribute{{Name: AttributeValue, Value: "not-an-integer"}}}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}}}},
	}
	_, err := AnalyzeSCCP(cfg)
	if err == nil || !strings.Contains(err.Error(), "invalid integer value") {
		t.Fatalf("malformed constant accepted: %v", err)
	}
}

func TestSCCPRejectsNoncanonicalIntegerConstant(t *testing.T) {
	cfg := CFG{
		Name:    "noncanonical",
		Entry:   0,
		Results: []Type{"u8"},
		Blocks:  []Block{{ID: 0, Operations: []Operation{integerConstant(1, "u8", "256")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}}}},
	}
	_, err := AnalyzeSCCP(cfg)
	if err == nil || !strings.Contains(err.Error(), "not canonical for u8") {
		t.Fatalf("noncanonical constant accepted: %v", err)
	}
}

func TestSCCPRejectsNarrowingIntegerCast(t *testing.T) {
	cfg := CFG{
		Name:    "narrowing",
		Entry:   0,
		Results: []Type{"u8"},
		Blocks: []Block{{
			ID: 0,
			Operations: []Operation{
				integerConstant(1, "u16", "256"),
				{Code: OpCastInt, Results: []Value{sccpValue(2, "u8")}, Operands: []ValueID{1}},
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{2}},
		}},
	}
	_, err := AnalyzeSCCP(cfg)
	if err == nil || !strings.Contains(err.Error(), "not value-preserving") {
		t.Fatalf("narrowing cast accepted: %v", err)
	}
}
