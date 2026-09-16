package optir

import (
	"reflect"
	"testing"
)

func TestRegionLoadForwardingSharesSplitAcrossMemoryPhis(t *testing.T) {
	for _, test := range []struct {
		name      string
		known     RegionID
		loadKnown bool
		join      BlockID
	}{
		{name: "two moved loads", join: 3},
		{name: "available phi planned before split", known: "left", join: 3},
		{name: "available phi planned after split", known: "right", join: 3},
		{name: "dominating load before split", known: "left", loadKnown: true, join: 3},
		{name: "dominating load after split", known: "right", loadKnown: true, join: 3},
		{name: "reuse last block identity", join: ^BlockID(0) - 1},
	} {
		for _, splitTrue := range []bool{false, true} {
			name := test.name + "/false edge"
			if splitTrue {
				name = test.name + "/true edge"
			}
			t.Run(name, func(t *testing.T) {
				cfg := CFG{
					Name: "shared_memory_edge", Entry: 0, Results: []Type{"u32"},
					Blocks: []Block{
						{ID: 0, Parameters: []Value{{ID: 1, Type: TypeBool}, {ID: 2, Type: "u32"}, {ID: 3, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: test.join, Arguments: []ValueID{2}}}},
						{ID: 1, Operations: []Operation{
							{Code: OpStoreRegion, Operands: []ValueID{2}, Effects: []Effect{EffectWriteMemory}},
							{Code: OpStoreRegion, Operands: []ValueID{3}, Effects: []Effect{EffectWriteMemory}},
						}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: test.join, Arguments: []ValueID{3}}}},
						{ID: test.join, Parameters: []Value{{ID: 4, Type: "u32"}}, Operations: []Operation{
							regionLoadOperation(5, "u32"), regionLoadOperation(6, "u32"),
							{Code: OpIntAdd, Results: []Value{{ID: 7, Type: "u32"}}, Operands: []ValueID{5, 6}},
							{Code: OpIntAdd, Results: []Value{{ID: 8, Type: "u32"}}, Operands: []ValueID{7, 4}},
						}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{8}}},
					},
				}
				metadata := RegionMemoryMetadata{Regions: []RegionID{"left", "right"}, Operations: []MemoryOperationMetadata{
					{Site: OperationSite{Block: 1, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "left", Kind: MemoryWrite, WholeRegion: true}}},
					{Site: OperationSite{Block: 1, Index: 1}, Accesses: []MemoryAccessSpec{{Region: "right", Kind: MemoryWrite, WholeRegion: true}}},
					regionLoadMetadata(test.join, 0, "left", false), regionLoadMetadata(test.join, 1, "right", false),
				}}
				knownValue := ValueID(3)
				if test.loadKnown {
					knownValue = 9
					cfg.Blocks[0].Operations = []Operation{regionLoadOperation(knownValue, "u32")}
					metadata.Operations = append(metadata.Operations, regionLoadMetadata(0, 0, test.known, false))
				} else if test.known != "" {
					cfg.Blocks[0].Operations = []Operation{{Code: OpStoreRegion, Operands: []ValueID{3}, Effects: []Effect{EffectWriteMemory}}}
					metadata.Operations = append(metadata.Operations, MemoryOperationMetadata{Site: OperationSite{Block: 0, Index: 0}, Accesses: []MemoryAccessSpec{{Region: test.known, Kind: MemoryWrite, WholeRegion: true}}})
				}
				if splitTrue {
					terminator := &cfg.Blocks[0].Terminator
					terminator.True, terminator.False = terminator.False, terminator.True
				}
				before := fingerprintCFG(cfg)
				memorySSA := mustRegionLoadMemorySSA(t, cfg, metadata)
				result, resultMetadata, report, err := ForwardRegionLoads(cfg, metadata, memorySSA)
				if err != nil {
					t.Fatal(err)
				}
				if err := VerifyRegionLoadForwarding(cfg, metadata, memorySSA, result, resultMetadata, report); err != nil {
					t.Fatal(err)
				}
				wantInsertions := 2
				if test.known != "" {
					wantInsertions = 1
				}
				if len(report.Replacements) != 2 || len(report.Insertions) != wantInsertions || len(result.Blocks) != 4 {
					t.Fatalf("want both phis and one shared block, got report %+v, blocks %+v", report, result.Blocks)
				}
				join, split := result.Blocks[2], result.Blocks[3]
				if split.ID != test.join+1 || len(split.Parameters) != 0 || len(split.Operations) != wantInsertions || len(join.Parameters) != 3 || len(join.Operations) != 2 {
					t.Fatalf("unexpected join/split shape: join %+v, split %+v", join, split)
				}
				incoming := result.Blocks[0].Terminator.False
				untouched := result.Blocks[0].Terminator.True
				if splitTrue {
					incoming, untouched = untouched, incoming
				}
				if incoming.Target != split.ID || len(incoming.Arguments) != 0 || untouched.Target != 1 || len(untouched.Arguments) != 0 {
					t.Fatalf("split redirected the wrong arm: %+v", result.Blocks[0].Terminator)
				}
				supplied := map[RegionID]ValueID{test.known: knownValue}
				for i, insertion := range report.Insertions {
					if !insertion.Split || insertion.Predecessor != 0 || insertion.Target != test.join || insertion.Site != (OperationSite{Block: split.ID, Index: i}) {
						t.Fatalf("incorrect shared insertion: %+v", insertion)
					}
					supplied[insertion.Region] = insertion.Result
				}
				if split.Terminator.Kind != TerminatorBranch || split.Terminator.True.Target != test.join ||
					!reflect.DeepEqual(split.Terminator.True.Arguments, []ValueID{2, supplied["left"], supplied["right"]}) ||
					!reflect.DeepEqual(result.Blocks[1].Terminator.True.Arguments, []ValueID{3, 2, 3}) {
					t.Fatalf("phi arguments lost their original edge/value: split %+v, stored %+v", split.Terminator, result.Blocks[1].Terminator)
				}
				if !reflect.DeepEqual(join.Operations[0].Operands, []ValueID{join.Parameters[1].ID, join.Parameters[2].ID}) || !reflect.DeepEqual(join.Operations[1].Operands, []ValueID{7, 4}) {
					t.Fatalf("join uses do not match promoted parameters: %+v", join)
				}
				if fingerprintCFG(cfg) != before {
					t.Fatal("forwarding mutated its input")
				}
				again, againMetadata, againReport, err := ForwardRegionLoads(cfg, metadata, memorySSA)
				if err != nil || !reflect.DeepEqual(again, result) || !reflect.DeepEqual(againMetadata, resultMetadata) || !reflect.DeepEqual(againReport, report) {
					t.Fatalf("shared split is not deterministic: %v", err)
				}
				mutated := report
				mutated.Insertions = append([]RegionLoadInsertion(nil), report.Insertions...)
				mutated.Insertions[0].Split = false
				if err := VerifyRegionLoadForwarding(cfg, metadata, memorySSA, result, resultMetadata, mutated); err == nil {
					t.Fatal("accepted mutated split evidence")
				}
			})
		}
	}
}

func TestRegionLoadForwardingKeepsDistinctSplitTargets(t *testing.T) {
	// Both edges of block 1 require a load, but they enter different phis.
	// Coalescing them by predecessor alone would read the wrong region/path.
	cfg := CFG{
		Name: "distinct_memory_edges", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{{ID: 1, Type: TypeBool}, {ID: 2, Type: TypeBool}, {ID: 3, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: 2}}},
			{ID: 1, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 2, True: Edge{Target: 5}, False: Edge{Target: 6}}},
			{ID: 2, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 2, True: Edge{Target: 3}, False: Edge{Target: 4}}},
			{ID: 3, Operations: []Operation{{Code: OpStoreRegion, Operands: []ValueID{3}, Effects: []Effect{EffectWriteMemory}}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 5}}},
			{ID: 4, Operations: []Operation{{Code: OpStoreRegion, Operands: []ValueID{3}, Effects: []Effect{EffectWriteMemory}}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 6}}},
			{ID: 5, Operations: []Operation{regionLoadOperation(4, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4}}},
			{ID: 6, Operations: []Operation{regionLoadOperation(5, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{5}}},
		},
	}
	metadata := RegionMemoryMetadata{Regions: []RegionID{"left", "right"}, Operations: []MemoryOperationMetadata{
		{Site: OperationSite{Block: 3, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "left", Kind: MemoryWrite, WholeRegion: true}}},
		{Site: OperationSite{Block: 4, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "right", Kind: MemoryWrite, WholeRegion: true}}},
		regionLoadMetadata(5, 0, "left", false), regionLoadMetadata(6, 0, "right", false),
	}}
	memorySSA := mustRegionLoadMemorySSA(t, cfg, metadata)
	result, resultMetadata, report, err := ForwardRegionLoads(cfg, metadata, memorySSA)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyRegionLoadForwarding(cfg, metadata, memorySSA, result, resultMetadata, report); err != nil {
		t.Fatal(err)
	}
	if len(result.Blocks) != 9 || len(report.Insertions) != 2 || len(report.Replacements) != 2 {
		t.Fatalf("distinct edges were not both split: %+v", report)
	}
	left, right := result.Blocks[7], result.Blocks[8]
	if left.ID != 7 || right.ID != 8 || result.Blocks[1].Terminator.True.Target != left.ID || result.Blocks[1].Terminator.False.Target != right.ID ||
		left.Terminator.True.Target != 5 || right.Terminator.True.Target != 6 ||
		len(left.Operations) != 1 || len(right.Operations) != 1 {
		t.Fatalf("different targets shared a split: predecessor %+v, left %+v, right %+v", result.Blocks[1], left, right)
	}
	for i, insertion := range report.Insertions {
		if !insertion.Split || insertion.Predecessor != 1 || insertion.Target != BlockID(5+i) || insertion.Site != (OperationSite{Block: BlockID(7 + i), Index: 0}) {
			t.Fatalf("incorrect distinct-edge insertion: %+v", insertion)
		}
	}
}
