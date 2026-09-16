package optir

import (
	"slices"
	"testing"
)

func TestRegisterColoringHonorsFixedValuesAndInterference(t *testing.T) {
	cfg := CFG{
		Name: "sum", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{{
			ID:         0,
			Parameters: []Value{{ID: 1, Type: "u32", Name: "a"}, {ID: 2, Type: "u32", Name: "b"}},
			Operations: []Operation{{Code: OpIntAdd, Results: []Value{{ID: 3, Type: "u32"}}, Operands: []ValueID{1, 2}}},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{3}},
		}},
	}
	colored, err := ColorRegisters(cfg, []int{0, 1, 2}, map[ValueID]int{1: 0, 2: 1})
	if err != nil {
		t.Fatal(err)
	}
	if colored.Colors[1] != 0 || colored.Colors[2] != 1 {
		t.Fatalf("fixed colors changed: %v", colored.Colors)
	}
	if colored.Colors[1] == colored.Colors[2] {
		t.Fatalf("simultaneously live parameters share a color: %v", colored.Colors)
	}
	if len(colored.LiveIn[0]) != 0 || len(colored.LiveOut[0]) != 0 {
		t.Fatalf("closed entry liveness = in %v out %v", colored.LiveIn[0], colored.LiveOut[0])
	}
}

func TestRegisterColoringTracksEdgeArguments(t *testing.T) {
	cfg := CFG{
		Name: "choose", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{{ID: 1, Type: TypeBool}, {ID: 2, Type: "u32"}, {ID: 3, Type: "u32"}}, Terminator: Terminator{
				Kind: TerminatorCondBranch, Condition: 1,
				True: Edge{Target: 1, Arguments: []ValueID{2}}, False: Edge{Target: 2, Arguments: []ValueID{3}},
			}},
			{ID: 1, Parameters: []Value{{ID: 4, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4}}},
			{ID: 2, Parameters: []Value{{ID: 5, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{5}}},
		},
	}
	colored, err := ColorRegisters(cfg, []int{0, 1, 2, 3}, map[ValueID]int{1: 0, 2: 1, 3: 2})
	if err != nil {
		t.Fatal(err)
	}
	if len(colored.Colors) != 5 {
		t.Fatalf("colors = %v", colored.Colors)
	}
}

func TestRegisterColoringDoesNotInterfereDeadBlockParameters(t *testing.T) {
	cfg := CFG{
		Name: "dead_parameters", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{{
			ID:         0,
			Parameters: []Value{{ID: 1, Type: "u32"}, {ID: 2, Type: "u32"}, {ID: 3, Type: "u32"}},
			Operations: []Operation{integerConstant(4, "u32", "7")},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4}},
		}},
	}
	colored, err := ColorRegisters(cfg, []int{0}, nil)
	if err != nil {
		t.Fatal(err)
	}
	for _, parameter := range []ValueID{1, 2, 3} {
		if colored.Colors[parameter] != 0 {
			t.Fatalf("dead parameter %d color = %d, want 0: %v", parameter, colored.Colors[parameter], colored.Colors)
		}
		if len(colored.Interference[parameter]) != 0 {
			t.Fatalf("dead parameter %d interference = %v, want none", parameter, colored.Interference[parameter])
		}
	}
}

func TestRegisterColoringKeepsLiveAndDeadBlockParametersDistinct(t *testing.T) {
	cfg := CFG{
		Name: "live_and_dead_parameters", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{{
			ID:         0,
			Parameters: []Value{{ID: 1, Type: "u32"}, {ID: 2, Type: "u32"}},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}},
		}},
	}
	colored, err := ColorRegisters(cfg, []int{0, 1}, nil)
	if err != nil {
		t.Fatal(err)
	}
	if !slices.Contains(colored.Interference[1], ValueID(2)) || !slices.Contains(colored.Interference[2], ValueID(1)) {
		t.Fatalf("live/dead parameter interference missing: %v", colored.Interference)
	}
	if _, err := ColorRegisters(cfg, []int{0}, nil); err == nil {
		t.Fatal("one color admitted a live and dead block parameter")
	}
	if _, err := ColorRegisters(cfg, []int{0, 1}, map[ValueID]int{1: 0, 2: 0}); err == nil {
		t.Fatal("one fixed color admitted interfering live and dead parameters")
	}
}

func TestRegisterColoringKeepsConditionalEdgeArgumentsLiveTogether(t *testing.T) {
	cfg := CFG{
		Name: "conditional_edge_pressure", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{{ID: 1, Type: TypeBool}}, Operations: []Operation{
				integerConstant(2, "u32", "7"),
				integerConstant(3, "u32", "9"),
			}, Terminator: Terminator{
				Kind: TerminatorCondBranch, Condition: 1,
				True: Edge{Target: 1, Arguments: []ValueID{2}}, False: Edge{Target: 2, Arguments: []ValueID{3}},
			}},
			{ID: 1, Parameters: []Value{{ID: 4, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4}}},
			{ID: 2, Parameters: []Value{{ID: 5, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{5}}},
		},
	}
	colored, err := ColorRegisters(cfg, []int{0, 1, 2}, nil)
	if err != nil {
		t.Fatal(err)
	}
	if !slices.Contains(colored.Interference[2], ValueID(3)) || !slices.Contains(colored.Interference[3], ValueID(2)) {
		t.Fatalf("conditional edge arguments do not interfere: %v", colored.Interference)
	}
	if _, err := ColorRegisters(cfg, []int{0, 1}, nil); err == nil {
		t.Fatal("two colors admitted the condition and both conditional edge arguments")
	}
}

func TestRegisterColoringFailsClosedOnPressure(t *testing.T) {
	cfg := CFG{
		Name: "pressure", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{{
			ID:         0,
			Parameters: []Value{{ID: 1, Type: "u32"}, {ID: 2, Type: "u32"}, {ID: 3, Type: "u32"}},
			Operations: []Operation{
				{Code: OpIntAdd, Results: []Value{{ID: 4, Type: "u32"}}, Operands: []ValueID{1, 2}},
				{Code: OpIntAdd, Results: []Value{{ID: 5, Type: "u32"}}, Operands: []ValueID{4, 3}},
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{5}},
		}},
	}
	if _, err := ColorRegisters(cfg, []int{0, 1}, nil); err == nil {
		t.Fatal("two colors admitted three simultaneously live parameters")
	}
}
