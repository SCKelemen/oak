package optir

import "testing"

func TestSnapshotCFG(t *testing.T) {
	input := licmTestCFG()
	snapshot, fingerprint, err := SnapshotCFG(input)
	if err != nil {
		t.Fatal(err)
	}
	input.Results[0] = "unknown"
	input.Blocks[0].Operations[0].Attributes[0].Value = "different"
	input.Blocks[0].Operations[0].Results[0].Type = "unknown"
	input.Blocks[0].Terminator.True.Arguments[0] = 999
	if after, err := FingerprintCFG(snapshot); err != nil || after != fingerprint {
		t.Fatal("caller mutation changed published snapshot", after, err)
	}
	empty := cloneCFG(snapshot)
	empty.Facts = []Fact{}
	empty.Blocks[0].Operations[0].Effects = []Effect{}
	if equal, err := ExactCFGEqual(snapshot, empty); err != nil || !equal {
		t.Fatal("nil/empty builder representation changed exact CFG identity", err)
	}
	changed := cloneCFG(snapshot)
	changed.Blocks[0].Operations[0].Source.Column++
	if equal, err := ExactCFGEqual(snapshot, changed); err != nil || equal {
		t.Fatal("semantic field change retained exact CFG identity", err)
	}
	if bad, key, err := SnapshotCFG(input); err == nil || len(bad.Blocks) != 0 || key != "" {
		t.Fatal("malformed input received a snapshot identity", err)
	}
}

func TestSnapshotFunction(t *testing.T) {
	input := Function{
		Name: "nested", Parameters: []Value{value(1, "u32", "n")}, Results: []Type{"u32"},
		Facts: []Fact{{ID: "input", Name: "range", Values: []ValueID{1}, Dependencies: []string{"checked"}}},
		Body: Region{Nodes: []Node{
			operation("const", []Value{value(2, "u32", "zero")}),
			{While: &While{Initial: []ValueID{2}, Results: []Value{value(7, "u32", "i")},
				Condition: Region{Arguments: []Value{value(3, "u32", "i")}, Nodes: []Node{
					operation("lt", []Value{value(4, TypeBool, "more")}, 3, 1),
				}, Yield: []ValueID{4}},
				Body: Region{Arguments: []Value{value(5, "u32", "i")}, Nodes: []Node{
					operation("copy", []Value{value(6, "u32", "next")}, 5),
				}, Yield: []ValueID{6}},
			}},
		}, Yield: []ValueID{7}},
	}
	snapshot, fingerprint, err := SnapshotFunction(input)
	if err != nil {
		t.Fatal(err)
	}
	input.Name = "mutated"
	input.Results[0] = "bad"
	input.Facts[0].Dependencies[0] = "mutated"
	input.Body.Nodes[1].While.Condition.Arguments[0].Type = "bad"
	input.Body.Nodes[1].While.Body.Nodes[0].Operation.Operands[0] = 999
	if after, err := FingerprintFunction(snapshot); err != nil || after != fingerprint {
		t.Fatal("caller mutation changed structured snapshot", after, err)
	}
	changed := cloneFunction(snapshot)
	changed.Body.Nodes[1].While.Body.Nodes[0].Operation.Source.Column++
	if after, err := FingerprintFunction(changed); err != nil || after == fingerprint {
		t.Fatal("nested semantic change retained structured identity", after, err)
	}
	snapshot.Body.Nodes[1].While.Condition.Yield[0] = 999
	if bad, key, err := SnapshotFunction(snapshot); err == nil || bad.Name != "" || key != "" {
		t.Fatal("malformed structured input received snapshot identity", err)
	}
	multiple := cloneFunction(changed)
	multiple.Body.Nodes[0].If = &If{}
	if bad, key, err := SnapshotFunction(multiple); err == nil || bad.Name != "" || key != "" {
		t.Fatal("multiply populated structured node was normalized into validity", err)
	}
}
