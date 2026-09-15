package optir

import "testing"

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
