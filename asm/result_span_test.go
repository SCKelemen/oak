package asm

import "testing"

// A result span's log collapses to the zero marker once zero stores at
// constant indices have covered every element (the backend's fill of a
// value-less record in the result area), and not before, nor over a
// guarded, symbolic, or non-zero write.
func TestCollapseZeroFill(t *testing.T) {
	fs := frameSpan{name: "out.at", offset: resultAreaBase, size: 16, elem: 4, entry: true}
	zero := constTerm(0, 32)
	state := &symbolicState{}
	for k := 0; k < 3; k++ {
		state.writes = appendWrite(state.writes, fs.name, constTerm(uint64(k), 32), zero, nil)
	}
	collapseZeroFill(state, fs)
	if log := state.writes[fs.name]; len(log) != 3 {
		t.Fatalf("three of four elements zeroed must not collapse, got %d writes", len(log))
	}
	state.writes = appendWrite(state.writes, fs.name, constTerm(3, 32), zero, nil)
	collapseZeroFill(state, fs)
	if log := state.writes[fs.name]; len(log) != 1 || log[0].memory != zeroMemory {
		t.Fatalf("a complete zero fill must collapse to the zero marker, got %d writes", len(log))
	}
	// A write of a non-zero value, a symbolic index, or a guard keeps the log.
	for name, write := range map[string]*spanWrite{
		"value":  {index: constTerm(0, 32), value: constTerm(1, 32)},
		"index":  {index: paramTerm("i", 32), value: zero},
		"guard":  {index: constTerm(0, 32), value: zero, guard: paramTerm("c", 1)},
		"marker": {memory: "loop1"},
	} {
		s := &symbolicState{writes: map[string][]*spanWrite{}}
		for k := 0; k < 4; k++ {
			s.writes = appendWrite(s.writes, fs.name, constTerm(uint64(k), 32), zero, nil)
		}
		s.writes[fs.name] = append([]*spanWrite{write}, s.writes[fs.name]...)
		collapseZeroFill(s, fs)
		if log := s.writes[fs.name]; len(log) != 5 {
			t.Fatalf("%s: a log with a %s write must not collapse, got %d writes", name, name, len(log))
		}
	}
	// Reads of the collapsed log are zero at every index; a store after it
	// layers on the marker.
	index := paramTerm("j", 32)
	if got := memoryAt(state.writes[fs.name], index, selectTerm(fs.name, index, 32)); got.kind != termConst || got.value != 0 {
		t.Fatalf("a read of the collapsed log must be zero, got %s", got)
	}
}
