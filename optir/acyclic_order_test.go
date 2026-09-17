package optir

import (
	"math/rand"
	"reflect"
	"testing"
)

func TestAcyclicOrder(t *testing.T) {
	random := rand.New(rand.NewSource(617))
	for trial := 0; trial < 256; trial++ {
		n := 2 + random.Intn(30)
		cfg := CFG{Name: "forward", Entry: 100}
		for i := 0; i < n; i++ {
			b := Block{ID: BlockID(100 + i*7), Terminator: Terminator{Kind: TerminatorReturn}}
			if i == 0 {
				b.Parameters = []Value{{ID: 1, Type: TypeBool}}
			}
			if i+1 < n {
				b.Terminator = Terminator{Kind: TerminatorCondBranch, Condition: 1,
					True: Edge{Target: BlockID(100 + (i+1)*7)}, False: Edge{Target: BlockID(100 + (i+1+random.Intn(n-i-1))*7)}}
			}
			cfg.Blocks = append(cfg.Blocks, b)
		}
		before := fingerprintCFG(cfg)
		order, err := AcyclicOrder(cfg)
		if err != nil || len(order) != n || order[0] != cfg.Entry {
			t.Fatalf("trial %d: order=%v err=%v", trial, order, err)
		}
		positions := map[BlockID]int{}
		for i, id := range order {
			if _, exists := positions[id]; exists {
				t.Fatal("duplicated block", id)
			}
			positions[id] = i
		}
		for _, b := range cfg.Blocks {
			for _, e := range transformEdges(b.Terminator) {
				if positions[b.ID] >= positions[e.Target] {
					t.Fatal("non-forward edge", b.ID, e.Target)
				}
			}
		}
		if before != fingerprintCFG(cfg) {
			t.Fatal("analysis mutated CFG")
		}
		random.Shuffle(n, func(i, j int) { cfg.Blocks[i], cfg.Blocks[j] = cfg.Blocks[j], cfg.Blocks[i] })
		again, err := AcyclicOrder(cfg)
		if err != nil || !reflect.DeepEqual(order, again) {
			t.Fatal("schedule depends on block storage order", again, err)
		}
	}
}

func TestAcyclicOrderCyclesAndMalformed(t *testing.T) {
	loop := canonicalLoopCFG("loop", "u32", "0", "4", "1", OpLess, OpIntAdd)
	if order, err := AcyclicOrder(loop); err != nil || order != nil {
		t.Fatal("loop received partial/forward order", order, err)
	}
	self := CFG{Name: "self", Entry: 0, Blocks: []Block{{ID: 0, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 0}}}}}
	if order, err := AcyclicOrder(self); err != nil || order != nil {
		t.Fatal("self-loop received forward order", order, err)
	}
	for _, mutate := range []func(*CFG){
		func(c *CFG) { c.Entry = 999 },
		func(c *CFG) { c.Blocks[0].Terminator.True.Target = 999 },
		func(c *CFG) { c.Blocks = append(c.Blocks, c.Blocks[0]) },
		func(c *CFG) {
			c.Blocks = append(c.Blocks, Block{ID: 999, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}}})
		},
		func(c *CFG) { c.Blocks[1].Terminator.Condition = 1 }, // integer is not Bool
	} {
		cfg := canonicalLoopCFG("invalid", "u32", "0", "4", "1", OpLess, OpIntAdd)
		mutate(&cfg)
		if order, err := AcyclicOrder(cfg); err == nil || order != nil {
			t.Fatal("malformed graph silently treated as fallback", order, err)
		}
	}
}

func TestAcyclicRegionOrder(t *testing.T) {
	cfg := canonicalLoopCFG("region", "u32", "0", "4", "1", OpLess, OpIntAdd)
	before := fingerprintCFG(cfg)
	for _, tc := range []struct {
		entry            BlockID
		boundaries, want []BlockID
	}{
		{2, []BlockID{1, 3}, []BlockID{2}},
		{1, []BlockID{2, 3}, []BlockID{1}},
		{0, []BlockID{1}, []BlockID{0}},
		{3, nil, []BlockID{3}},
	} {
		order, err := AcyclicRegionOrder(cfg, tc.entry, tc.boundaries)
		if err != nil || !reflect.DeepEqual(order, tc.want) {
			t.Fatalf("region: %v %v", order, err)
		}
	}
	if fingerprintCFG(cfg) != before {
		t.Fatal("region analysis mutated CFG")
	}
	if order, err := AcyclicRegionOrder(cfg, 2, []BlockID{3}); err != nil || order != nil {
		t.Fatal("uncontained cycle got partial schedule", order, err)
	}
	for _, tc := range []struct {
		entry      BlockID
		boundaries []BlockID
	}{
		{999, nil}, {2, []BlockID{999}}, {2, []BlockID{2}}, {2, []BlockID{1, 1}},
	} {
		if order, err := AcyclicRegionOrder(cfg, tc.entry, tc.boundaries); err == nil || order != nil {
			t.Fatal("invalid region request admitted", order, err)
		}
	}
	// A boundary is only a traversal stop, not permission to skip validation.
	cfg.Blocks[3].Terminator.Values = []ValueID{999}
	if order, err := AcyclicRegionOrder(cfg, 2, []BlockID{1, 3}); err == nil || order != nil {
		t.Fatal("malformed boundary escaped CFG validation", order, err)
	}
}
