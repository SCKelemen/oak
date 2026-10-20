package asm

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// TestEntryReadableProvenanceCorrespondence is the bounded production pin for
// Oak.AssemblerEntryProvenance. Lean proves the parametric transition laws;
// Go still needs these executable tests against the real symbolic executor.
// This test deliberately uses independently stated psABI entry masks.
func TestEntryReadableProvenanceCorrespondence(t *testing.T) {
	data, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "AssemblerEntryProvenance.lean"))
	if err != nil {
		t.Fatal(err)
	}
	lean := strings.Join(strings.Fields(string(data)), " ")
	for _, name := range []string{
		"read_clobber_none",
		"read_clobber_other",
		"read_write_after_clobber",
		"write_keeps_invalidation",
		"read_second_clobber_none",
		"fork_sibling_unchanged",
		"fork_clobbered_side_none",
		"join_invalid_left",
		"join_invalid_right",
		"read_join_clobber_right_none",
		"read_join_clobber_left_none",
		"read_join_writes",
	} {
		if !strings.Contains(lean, "theorem "+name+" ") {
			t.Errorf("missing Lean provenance obligation: %s", name)
		}
	}
	for _, marker := range []string{
		"example : entryReadable .arm64 30 = true := by decide",
		"example : entryReadable .arm64 18 = false := by decide",
		"example : entryReadable .rv64 1 = true := by decide",
		"example : entryReadable .rv64 5 = false := by decide",
	} {
		if !strings.Contains(lean, marker) {
			t.Errorf("missing Go/Lean ISA entry-mask pin: %s", marker)
		}
	}
	if strings.Contains(lean, "sorry") || strings.Contains(lean, "axiom ") {
		t.Fatal("provenance module contains an unverified axiom or sorry")
	}

	for _, tc := range []struct {
		arch string
		cls RegClass
		entry func(int) bool
	}{
		{ArchArm64, ClassX, func(r int) bool { return r >= 19 && r <= 30 }},
		{ArchRV64, ClassRV64X, func(r int) bool {
			return r == 1 || r == 8 || r == 9 || (r >= 18 && r <= 27)
		}},
	} {
		isa, found := verifierISAFor(tc.arch)
		if !found {
			t.Fatalf("missing native ISA: %s", tc.arch)
		}
		clobbered := make(map[int]bool, len(isa.clobberedGPR))
		for _, r := range isa.clobberedGPR {
			clobbered[r] = true
		}
		for r := 0; r < 32; r++ {
			if got, want := verifierEntryReadableGPR(tc.arch, r), tc.entry(r); got != want {
				t.Fatalf("%s entry mask reg %d = %v; want %v", tc.arch, r, got, want)
			}
			if !tc.entry(r) {
				continue
			}
			reg := Register{Class: tc.cls, Num: r}
			s := &symbolicState{arch: tc.arch, regs: make(map[int]*term)}
			before, ok := s.read(reg)
			if !ok || before == nil {
				t.Fatalf("%s reg %d not entry-readable", tc.arch, r)
			}
			(&pathExecutor{arch: tc.arch}).forgetCallerSaved(s)
			after, readable := s.read(reg)
			if clobbered[r] {
				if readable || after != nil || !s.invalidEntryGPR[r] {
					t.Fatalf("%s reg %d resurrected after call (value %v)", tc.arch, r, after)
				}
			} else {
				if !readable || !equalTerms(before, after) || s.invalidEntryGPR[r] {
					t.Fatalf("%s reg %d changed despite preserved call state", tc.arch, r)
				}
			}
			// An actual write is always readable, but cannot restore the
			// original entry authority destroyed by an earlier call.
			s.write(reg, constTerm(99, 64))
			got, ok := s.read(reg)
			if !ok || !equalTerms(got, constTerm(99, 64)) {
				t.Fatalf("%s reg %d real write was lost", tc.arch, r)
			}
			if clobbered[r] {
				if !s.invalidEntryGPR[r] {
					t.Fatalf("%s reg %d real write resurrected entry provenance", tc.arch, r)
				}
				(&pathExecutor{arch: tc.arch}).forgetCallerSaved(s)
				if got, ok := s.read(reg); ok || got != nil {
					t.Fatalf("%s reg %d second call resurrected entry value", tc.arch, r)
				}
			}
		}
	}
}
