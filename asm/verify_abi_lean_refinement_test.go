package asm

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// The independently written reference mask is deliberately separate from
// verifierISAFor and checks *all* registers, not a handful of examples.
func assemblerCallFloatSaved(reg int) bool {
	return reg == 8 || reg == 9 || (reg >= 18 && reg <= 27)
}
func assemblerCallVectorSaved(arch string, reg int) bool {
	return arch == ArchArm64 && reg >= 8 && reg <= 15
}

func TestAssemblerCallStateLeanCorrespondence(t *testing.T) {
	content, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "AssemblerCallState.lean"))
	if err != nil {
		t.Fatal(err)
	}
	lean := strings.Join(strings.Fields(string(content)), " ")
	for _, label := range []string{
		"caller_fpr_dead", "callee_fpr_retained",
		"caller_vector_dead", "callee_vector_retained",
		"caller_gpr_dead", "caller_entry_gpr_invalid",
		"caller_entry_gpr_unreadable",
		"return_fpr_rebound", "return_vector_rebound",
		"return_gpr_keeps_entry_invalidation",
		"join_fpr_requires_both", "join_vector_requires_both",
		"join_called_fpr_left_dead", "join_called_fpr_right_dead",
		"join_called_vector_left_dead", "join_called_vector_right_dead",
		"rv64_all_vector_dead", "rv64_config_dead",
		"arm64_flags_dead", "rv64_fs8_retained", "rv64_fa0_dead",
		"arm64_v8_retained", "arm64_v16_dead",
	} {
		if !strings.Contains(lean, "theorem "+label+" ") {
			t.Errorf("missing cross-class Lean theorem: %s", label)
		}
	}
	for _, exp := range []string{
		"example : callerSavedFPR .rv64 8 = false := by decide",
		"example : callerSavedFPR .rv64 10 = true := by decide",
		"example : callerSavedVector .arm64 8 = false := by decide",
		"example : callerSavedVector .arm64 16 = true := by decide",
		"example : callerSavedVector .rv64 8 = true := by decide",
	} {
		if !strings.Contains(lean, exp) {
			t.Errorf("missing ABI witness: %s", exp)
		}
	}
	if strings.Contains(lean, "sorry") || strings.Contains(lean, "axiom ") {
		t.Fatal("cross-class proof contains an admitted axiom or sorry")
	}
	for _, arch := range []string{ArchArm64, ArchRV64} {
		t.Run(arch, func(t *testing.T) {
			policy, ok := verifierISAFor(arch)
			if !ok {
				t.Fatal("unregistered native verifier ISA")
			}
			for reg := 0; reg < 32; reg++ {
				// For AArch64 no Go FPR file is interpreted independently;
				// only the register vector views represent FP state.
				if arch == ArchRV64 {
					got := policy.preservedFPR != nil && policy.preservedFPR(reg)
					if got != assemblerCallFloatSaved(reg) {
						t.Errorf("RV64 FPR f%d preservation mismatch: %v", reg, got)
					}
				}
				wantVecSave := assemblerCallVectorSaved(arch, reg)
				gotVecSave := policy.preservedVector != nil && policy.preservedVector(reg)
				if gotVecSave != wantVecSave {
					t.Errorf("%s v%d preservation mismatch: %v", arch, reg, gotVecSave)
				}
			}
			if (arch == ArchRV64) != policy.invalidateAllVector {
				t.Fatal("RVV vector-clobber policy mismatch")
			}
		})
	}
}

func TestAssemblerCallStateAcrossRegisterClasses(t *testing.T) {
	for _, arch := range []string{ArchArm64, ArchRV64} {
		t.Run(arch, func(t *testing.T) {
			s := &symbolicState{
				arch: arch,
				regs: map[int]*term{},
				fregs: map[int]*term{},
				vregs: map[int]vecValue{},
				rvcfg: &rvVectorConfigVerify{lanes: 4, bits: 32},
				flags: &flagsFact{},
			}
			for r := 0; r < 32; r++ {
				s.fregs[r] = constTerm(uint64(100+r), 64)
				s.vregs[r] = vecValue{bits: 64, lanes: []*term{constTerm(uint64(100+r), 64)}}
			}
			(&pathExecutor{arch: arch}).forgetCallerSaved(s)
			for r := 0; r < 32; r++ {
				if arch == ArchRV64 {
					_, actual := s.fregs[r]
					if actual != assemblerCallFloatSaved(r) {
						t.Errorf("RV64 f%d: actual bound=%v", r, actual)
					}
					// No RV64 vector register remains after the standard ABI call.
					if _, exists := s.vregs[r]; exists {
						t.Errorf("RV64 v%d unexpectedly survived", r)
					}
				} else {
					_, actual := s.vregs[r]
					if actual != assemblerCallVectorSaved(arch, r) {
						t.Errorf("ARM64 v%d: actual bound=%v", r, actual)
					}
				}
			}
			if arch == ArchRV64 {
				if s.rvcfg != nil {
					t.Fatal("RV64 caller retained vl/vtype")
				}
				// A legitimate post-call result write is available until the
				// *next* call, after which fa0 must again be unbound.
				result := Register{Class: ClassRV64F, Num: 10}
				s.write(result, constTerm(99, 64))
				if got, ok := s.read(result); !ok || !equalTerms(got, constTerm(99, 64)) {
					t.Fatal("RV64 post-call FPR result missing")
				}
				(&pathExecutor{arch: arch}).forgetCallerSaved(s)
				if got, ok := s.read(result); ok || got != nil {
					t.Fatal("RV64 caller-saved result survived subsequent call")
				}
				s.writeVec(8, vecValue{bits: 64, lanes: []*term{constTerm(99, 64)}})
				if _, ok := s.readVec(8); !ok {
					t.Fatal("RV64 post-call vector result missing")
				}
				(&pathExecutor{arch: arch}).forgetCallerSaved(s)
				if _, ok := s.readVec(8); ok {
					t.Fatal("RV64 vector result survived subsequent call")
				}
			} else if s.flags != nil {
				t.Fatal("ARM64 NZCV survived a call")
			}
		})
	}
}

func TestAssemblerCallStateJoinDropsOneSidedCallerFacts(t *testing.T) {
	for _, arch := range []string{ArchArm64, ArchRV64} {
		t.Run(arch, func(t *testing.T) {
			initial := &symbolicState{
				arch: arch,
				regs: map[int]*term{},
				fregs: map[int]*term{
					8: constTerm(8, 64),
					10: constTerm(10, 64),
				},
				vregs: map[int]vecValue{
					0: {bits: 64, lanes: []*term{constTerm(1, 64)}},
					8: {bits: 64, lanes: []*term{constTerm(8, 64)}},
				},
				rvcfg: &rvVectorConfigVerify{lanes: 4, bits: 32},
			}
			called, untouched := initial.clone(), initial.clone()
			(&pathExecutor{arch: arch}).forgetCallerSaved(called)
			joined, ok := (&pathExecutor{arch: arch}).mergeTwo(constTerm(1, 1), called, untouched)
			if !ok {
				t.Fatal("failed to join compatible paths")
			}
			if _, live := joined.vregs[0]; live {
				t.Fatal("joined vector v0 survived a one-sided call")
			}
			if arch == ArchRV64 {
				if _, live := joined.fregs[10]; live {
					t.Fatal("joined fa0 survived a one-sided call")
				}
				if _, live := joined.fregs[8]; !live {
					t.Fatal("RV64 preserved fs0 disappeared across the join")
				}
				if len(joined.vregs) != 0 || joined.rvcfg != nil {
					t.Fatal("RV64 vector or vtype facts reappeared after join")
				}
			} else {
				if _, live := joined.vregs[8]; !live {
					t.Fatal("ARM64 preserved v8 disappeared across the join")
				}
				if joined.flags != nil {
					t.Fatal("ARM64 flags survived a one-sided call join")
				}
			}
		})
	}
}
