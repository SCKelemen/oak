package optir

import (
	"reflect"
	"strings"
	"testing"
)

func value(id ValueID, typ Type, name string) Value {
	return Value{ID: id, Type: typ, Name: name}
}

func operation(code string, results []Value, operands ...ValueID) Node {
	return Node{Operation: &Operation{Code: code, Results: results, Operands: operands}}
}

func TestProjectStructuredIfToCanonicalCFG(t *testing.T) {
	function := Function{
		Name:       "choose",
		Parameters: []Value{value(1, TypeBool, "condition")},
		Results:    []Type{"u32"},
		Body: Region{
			Nodes: []Node{{If: &If{
				Condition: 1,
				Results:   []Value{value(4, "u32", "selected")},
				Then: Region{
					Nodes: []Node{operation("const", []Value{value(2, "u32", "left")})},
					Yield: []ValueID{2},
				},
				Else: Region{
					Nodes: []Node{operation("const", []Value{value(3, "u32", "right")})},
					Yield: []ValueID{3},
				},
			}}},
			Yield: []ValueID{4},
		},
	}

	first, err := Project(function)
	if err != nil {
		t.Fatal(err)
	}
	second, err := Project(function)
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(first, second) {
		t.Fatalf("projection is not deterministic:\nfirst:  %#v\nsecond: %#v", first, second)
	}
	if len(first.Blocks) != 4 || first.Entry != 0 {
		t.Fatalf("if CFG shape = %#v", first)
	}
	entry, merge := first.Blocks[0], first.Blocks[3]
	if entry.Terminator.Kind != TerminatorCondBranch || entry.Terminator.True.Target != 1 || entry.Terminator.False.Target != 2 {
		t.Fatalf("if entry terminator = %#v", entry.Terminator)
	}
	if len(merge.Parameters) != 1 || merge.Parameters[0].ID != 4 || merge.Terminator.Kind != TerminatorReturn || !reflect.DeepEqual(merge.Terminator.Values, []ValueID{4}) {
		t.Fatalf("if merge block = %#v", merge)
	}
}

func TestProjectStructuredWhileCarriesSSAValue(t *testing.T) {
	conditionFact := Fact{Name: "bounded", Values: []ValueID{3, 1}, Provenance: "checked", Witness: "i < n"}
	function := Function{
		Name:       "count",
		Parameters: []Value{value(1, "u32", "n")},
		Results:    []Type{"u32"},
		Facts:      []Fact{{Name: "extent", Values: []ValueID{1}, Provenance: "checked"}},
		Body: Region{
			Nodes: []Node{
				operation("const", []Value{value(2, "u32", "zero")}),
				{While: &While{
					Initial: []ValueID{2},
					Results: []Value{value(8, "u32", "i")},
					Condition: Region{
						Arguments: []Value{value(3, "u32", "i")},
						Nodes: []Node{{Operation: &Operation{
							Code:     "lt",
							Results:  []Value{value(4, TypeBool, "more")},
							Operands: []ValueID{3, 1},
							Facts:    []Fact{conditionFact},
						}}},
						Yield: []ValueID{4},
					},
					Body: Region{
						Arguments: []Value{value(5, "u32", "i")},
						Nodes: []Node{
							operation("const", []Value{value(6, "u32", "one")}),
							{Operation: &Operation{
								Code:       "add",
								Results:    []Value{value(7, "u32", "next")},
								Operands:   []ValueID{5, 6},
								Effects:    []Effect{EffectTrap},
								Attributes: []Attribute{{Name: "overflow", Value: "defined-wrap"}},
							}},
						},
						Yield: []ValueID{7},
					},
				}},
			},
			Yield: []ValueID{8},
		},
	}

	cfg, err := Project(function)
	if err != nil {
		t.Fatal(err)
	}
	if len(cfg.Blocks) != 4 {
		t.Fatalf("while CFG has %d blocks, want 4: %#v", len(cfg.Blocks), cfg)
	}
	entry, header, body, exit := cfg.Blocks[0], cfg.Blocks[1], cfg.Blocks[2], cfg.Blocks[3]
	if entry.Terminator.Kind != TerminatorBranch || entry.Terminator.True.Target != header.ID || !reflect.DeepEqual(entry.Terminator.True.Arguments, []ValueID{2}) {
		t.Fatalf("while preheader = %#v", entry)
	}
	if len(header.Parameters) != 1 || header.Terminator.Kind != TerminatorCondBranch || header.Terminator.False.Target != exit.ID {
		t.Fatalf("while header = %#v", header)
	}
	if len(body.Parameters) != 1 || body.Terminator.True.Target != header.ID || len(body.Operations) != 2 {
		t.Fatalf("while body = %#v", body)
	}
	add := body.Operations[1]
	if !reflect.DeepEqual(add.Effects, []Effect{EffectTrap}) || !reflect.DeepEqual(add.Attributes, []Attribute{{Name: "overflow", Value: "defined-wrap"}}) {
		t.Fatalf("operation metadata was not preserved: %#v", add)
	}
	if len(header.Operations[0].Facts) != 1 || header.Operations[0].Facts[0].Values[0] != header.Parameters[0].ID {
		t.Fatalf("condition fact was not remapped: %#v", header.Operations[0].Facts)
	}
	if len(exit.Parameters) != 1 || exit.Parameters[0].ID != 8 || !reflect.DeepEqual(exit.Terminator.Values, []ValueID{8}) {
		t.Fatalf("while exit = %#v", exit)
	}
}

func TestProjectRejectsInvalidWhileShape(t *testing.T) {
	function := Function{
		Name:       "bad",
		Parameters: []Value{value(1, "u32", "n")},
		Results:    []Type{"u32"},
		Body: Region{
			Nodes: []Node{{While: &While{
				Initial: []ValueID{1},
				Results: []Value{value(2, "u32", "i")},
				Condition: Region{
					Arguments: []Value{value(3, "u64", "i")},
					Nodes:     []Node{operation("const", []Value{value(4, TypeBool, "more")})},
					Yield:     []ValueID{4},
				},
				Body: Region{
					Arguments: []Value{value(5, "u32", "i")},
					Yield:     []ValueID{5},
				},
			}}},
			Yield: []ValueID{2},
		},
	}
	_, err := Project(function)
	if err == nil || !strings.Contains(err.Error(), "condition argument types") {
		t.Fatalf("invalid while shape was accepted: %v", err)
	}
}

func TestVerifyRejectsNonDominatingValue(t *testing.T) {
	cfg := CFG{
		Name:    "bad_dominance",
		Entry:   0,
		Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{value(1, TypeBool, "condition")}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: 2}}},
			{ID: 1, Operations: []Operation{{Code: "const", Results: []Value{value(2, "u32", "branch_only")}}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3}}},
			{ID: 2, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3}}},
			{ID: 3, Operations: []Operation{{Code: "copy", Results: []Value{value(3, "u32", "result")}, Operands: []ValueID{2}}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{3}}},
		},
	}
	if err := Verify(cfg); err == nil || !strings.Contains(err.Error(), "does not dominate") {
		t.Fatalf("non-dominating value was accepted: %v", err)
	}
}
