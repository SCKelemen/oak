package asm

import "testing"

// A store both paths of a fork make after they meet again is logged once
// in the merged log, after the fork's exclusive remainders (mergeWrites'
// common suffix); a store whose value differs between the paths stays
// once per path under the fork's condition.
func TestMergeWritesFactorsTheCommonSuffix(t *testing.T) {
	cond := cmpTerm("eq", paramTerm("a", 32), constTerm(0, 32))
	before := &spanWrite{index: constTerm(0, 32), value: paramTerm("v0", 32)}
	takenOwn := &spanWrite{index: constTerm(1, 32), value: paramTerm("v1", 32)}
	// The same store built afresh on each path: equal terms, distinct nodes.
	afterTaken := &spanWrite{index: binaryTerm("add", paramTerm("at", 32), constTerm(1, 32)), value: constTerm(7, 32)}
	afterFall := &spanWrite{index: binaryTerm("add", paramTerm("at", 32), constTerm(1, 32)), value: constTerm(7, 32)}
	// A store whose value the paths compute differently.
	lastTaken := &spanWrite{index: constTerm(5, 32), value: paramTerm("x", 32)}
	lastFall := &spanWrite{index: constTerm(5, 32), value: paramTerm("y", 32)}

	merged := mergeWrites(cond, map[string][]*spanWrite{"w": {before, takenOwn, afterTaken}}, map[string][]*spanWrite{"w": {before, afterFall}})
	log := merged["w"]
	if len(log) != 3 {
		t.Fatalf("merged log has %d writes, want 3 (the shared prefix, the taken path's own, the common suffix once): %v", len(log), describeWrites(log))
	}
	if log[0] != before {
		t.Errorf("the shared prefix must stay as it is")
	}
	if log[1].guard == nil || !equalTerms(log[1].index, takenOwn.index) {
		t.Errorf("the taken path's own store must run under the fork's condition: %v", describeWrites(log[1:2]))
	}
	if log[2].guard != nil || !equalTerms(log[2].index, afterTaken.index) {
		t.Errorf("the common suffix must follow once, unguarded: %v", describeWrites(log[2:]))
	}

	merged = mergeWrites(cond, map[string][]*spanWrite{"w": {before, afterTaken, lastTaken}}, map[string][]*spanWrite{"w": {before, afterFall, lastFall}})
	log = merged["w"]
	if len(log) != 5 {
		t.Fatalf("a differing last store keeps the paths apart: %d writes, want 5: %v", len(log), describeWrites(log))
	}
	for k := 1; k < 5; k++ {
		if log[k].guard == nil {
			t.Errorf("write %d must be guarded when the last stores differ", k)
		}
	}
}

func describeWrites(log []*spanWrite) []string {
	out := make([]string, len(log))
	for k, w := range log {
		guard := "always"
		if w.guard != nil {
			guard = w.guard.String()
		}
		out[k] = w.index.String() + " := " + w.value.String() + " if " + guard
	}
	return out
}
