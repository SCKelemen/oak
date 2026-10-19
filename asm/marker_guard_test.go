package asm

import "testing"

func TestWriteLogsEqualUnderChecksMemoryMarkerGuards(t *testing.T) {
	p, q := paramTerm("p", 1), paramTerm("q", 1)
	one := constTerm(1, 1)
	marker := "loop1.v"
	log := func(memory string, guard *term) []*spanWrite {
		return []*spanWrite{{memory: memory, guard: guard}}
	}
	widthOf := func(string) int { return 1 }
	decide := func(premise, a, b *term) (bool, bool) {
		return impliesEqual(premise, a, b, widthOf)
	}
	tests := []struct {
		name               string
		premise            *term
		oak, machine       []*spanWrite
		want               bool
		wantCounterexample bool
	}{
		{"opposite guards", one, log(marker, p), log(marker, notTerm(p)), false, true},
		{"conditional and unconditional", one, log(marker, p), log(marker, nil), false, true},
		{"independent guards", one, log(marker, p), log(marker, q), false, true},
		{"same guard", one, log(marker, p), log(marker, p), true, false},
		{"same unconditional marker", one, log(marker, nil), log(marker, nil), true, false},
		{"equivalent conjunctions", one, log(marker, binaryTerm("and", p, q)), log(marker, binaryTerm("and", q, p)), true, false},
		{"guard implied by premise", p, log(marker, p), log(marker, nil), true, false},
		{"different markers", one, log(marker, p), log("loop2.v", p), false, true},
		{"opposite zero-fill guards", one, log(zeroMemory, p), log(zeroMemory, notTerm(p)), false, true},
		{"same conditional zero fill", one, log(zeroMemory, p), log(zeroMemory, p), true, false},
		{"same unconditional zero fill", one, log(zeroMemory, nil), log(zeroMemory, nil), true, false},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			// The exit-memory caller prunes before comparing logs. Unknown
			// guards survive this operation and must still be compared.
			oak := pruneWritesUnder(test.premise, test.oak, widthOf)
			machine := pruneWritesUnder(test.premise, test.machine, widthOf)
			if got := writeLogsEqualUnder(oak, machine, test.premise, decide); got != test.want {
				t.Fatalf("pointwise equality = %v, want %v", got, test.want)
			}
			at := constTerm(0, 32)
			base := selectTerm("v", at, 1)
			first := selectTerm("loop1.v", at, 1)
			second := selectTerm("loop2.v", at, 1)
			if base.kind != termParam || first.kind != termParam || second.kind != termParam ||
				base.name == first.name || first.name == second.name || base.name == second.name {
				t.Fatal("constant reads must name three distinct memory parameters")
			}
			a, b := memoryAt(test.oak, at, base), memoryAt(test.machine, at, base)
			counterexample := false
			for bits := uint64(0); bits < 32; bits++ {
				env := map[string]uint64{
					"p": bits & 1, "q": (bits >> 1) & 1,
					base.name:   (bits >> 2) & 1,
					first.name:  (bits >> 3) & 1,
					second.name: (bits >> 4) & 1,
				}
				if test.premise.eval(env)&1 != 0 && a.eval(env) != b.eval(env) {
					counterexample = true
				}
			}
			if counterexample != test.wantCounterexample {
				t.Fatalf("memoryAt counterexample = %v, want %v", counterexample, test.wantCounterexample)
			}
		})
	}
}

func TestWriteLogsEqualUnderMarkerGuardUnknownFailsClosed(t *testing.T) {
	p, q := paramTerm("p", 1), paramTerm("q", 1)
	oak := []*spanWrite{{memory: "loop1.v", guard: p}}
	machine := []*spanWrite{{memory: "loop1.v", guard: q}}
	calls := 0
	unknown := func(premise, a, b *term) (bool, bool) {
		calls++
		return false, false
	}
	if writeLogsEqualUnder(oak, machine, constTerm(1, 1), unknown) {
		t.Fatal("an undecided marker guard must select the whole-memory fallback")
	}
	if calls != 1 {
		t.Fatalf("guard decision calls = %d, want 1", calls)
	}
	if oak[0].guard != p || machine[0].guard != q {
		t.Fatal("pointwise comparison mutated shared marker guards")
	}
}

func TestDecideSpansRejectsDifferentMemoryMarkerGuards(t *testing.T) {
	// Exercise the production caller with synthetic, well-declared internal
	// logs. This is not a claim that a source/assembly pair reaches this state
	// through the complete loop-coupling pipeline.
	for _, equal := range []bool{false, true} {
		name := "different"
		if equal {
			name = "equal"
		}
		t.Run(name, func(t *testing.T) {
			p := paramTerm("p", 1)
			machineGuard := notTerm(p)
			if equal {
				machineGuard = p
			}
			lo := &oakLowering{
				params: map[string]int{"p": 1},
				fresh:  map[string]int{},
				spans: map[string]spanContract{
					"v": {elemWidth: 8}, "loop1.v": {elemWidth: 8},
				},
				writes: map[string][]*spanWrite{"v": {{memory: "loop1.v", guard: p}}},
			}
			exec := &pathExecutor{
				spans:  map[string]int64{"v": 1},
				writes: map[string][]*spanWrite{"v": {{memory: "loop1.v", guard: machineGuard}}},
			}
			verdict := decideSpans(&Function{Name: "marker_guard"}, lo, exec, nil)
			want := VerdictMismatch
			if equal {
				want = VerdictProven
			}
			if verdict.Kind != want {
				t.Fatalf("verdict = %s, want %s: %s", verdict.Kind, want, verdict.Message)
			}
		})
	}
}
