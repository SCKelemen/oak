package asm

import "testing"

// These tests pin the existing native call boundary when verifier internals
// move between modules. A caller-saved register cannot retain symbolic facts
// across a call just because a proof/symbolic-execution path was refactored.
func TestNativeVerifierCallABIClobber(t *testing.T) {
	for _, tt := range []struct {
		name       string
		arch       string
		clobbered  []int
		preserved  []int
		floatClob  []int
		floatKeep  []int
		vectorGone []int
		vectorKeep []int
		clearFlags bool
	}{
		{
			name: "AArch64", arch: ArchArm64,
			clobbered: []int{0, 1, 9, 17, 30},
			preserved: []int{18, 19, 28, 29},
			vectorGone: []int{0, 7, 16, 31},
			vectorKeep: []int{8, 15},
			clearFlags: true,
		},
		{
			name: "RV64", arch: ArchRV64,
			clobbered: []int{1, 5, 6, 7, 10, 17, 28, 31},
			preserved: []int{2, 3, 4, 8, 9, 18, 27},
			floatClob: []int{0, 7, 10, 17, 28, 31},
			floatKeep: []int{8, 9, 18, 27},
		},
	} {
		t.Run(tt.name, func(t *testing.T) {
			state := &symbolicState{
				arch: tt.arch,
				regs: make(map[int]*term),
				bounds: make(map[int]uint64),
				fregs: make(map[int]*term),
				vregs: make(map[int]vecValue),
				flags: &flagsFact{},
			}
			for reg := 0; reg <= 31; reg++ {
				state.regs[reg] = constTerm(uint64(reg + 1), 64)
				state.bounds[reg] = 4096
				state.fregs[reg] = constTerm(uint64(reg + 1), 64)
				state.vregs[reg] = vecValue{}
			}
			x := &pathExecutor{arch: tt.arch}
			x.forgetCallerSaved(state)
			for _, reg := range tt.clobbered {
				if state.regs[reg] != nil {
					t.Errorf("caller-saved integer register %d survived", reg)
				}
				if _, ok := state.bounds[reg]; ok {
					t.Errorf("caller-saved integer bound %d survived", reg)
				}
			}
			for _, reg := range tt.preserved {
				if state.regs[reg] == nil {
					t.Errorf("callee-saved integer register %d disappeared", reg)
				}
				if _, ok := state.bounds[reg]; !ok {
					t.Errorf("callee-saved integer bound %d disappeared", reg)
				}
			}
			for _, reg := range tt.floatClob {
				if state.fregs[reg] != nil {
					t.Errorf("caller-saved float register %d survived", reg)
				}
			}
			for _, reg := range tt.floatKeep {
				if state.fregs[reg] == nil {
					t.Errorf("callee-saved float register %d disappeared", reg)
				}
			}
			for _, reg := range tt.vectorGone {
				if _, ok := state.vregs[reg]; ok {
					t.Errorf("caller-saved vector register %d survived", reg)
				}
			}
			for _, reg := range tt.vectorKeep {
				if _, ok := state.vregs[reg]; !ok {
					t.Errorf("callee-saved vector register %d disappeared", reg)
				}
			}
			if tt.clearFlags && state.flags != nil {
				t.Error("condition flags survived native call")
			}
		})
	}
}

// The status contract must never treat evidence or external trust as proof.
// Keep the labels stable across the extracted verdict module.
func TestVerifierVerdictKindsRemainDistinct(t *testing.T) {
	kinds := map[VerdictKind]string{
		VerdictTrusted: "trusted",
		VerdictProven: "proven",
		VerdictWitnessed: "witness-checked",
		VerdictMismatch: "mismatch",
	}
	for kind, want := range kinds {
		if got := kind.String(); got != want {
			t.Errorf("verdict kind %d = %q, want %q", kind, got, want)
		}
	}
	v := verdictWithCallees(Verdict{Kind: VerdictProven}, []string{"f", "g"}, []string{"g", "h"})
	if len(v.Callees) != 3 || v.Callees[0] != "f" || v.Callees[1] != "g" || v.Callees[2] != "h" {
		t.Fatalf("verdict dependencies changed: %v", v.Callees)
	}
}
