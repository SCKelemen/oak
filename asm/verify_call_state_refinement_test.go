package asm

import (
	"os"
	"strings"
	"testing"
)

// A call invalidates the entire caller-owned register state, regardless
// of whether the callee returns an integer, float, vector, aggregate or unit.
func TestNativeCallInvalidatesAllCallerSavedRegisterClasses(t *testing.T) {
	for _, arch := range []string{ArchArm64, ArchRV64} {
		s := &symbolicState{
			arch: arch,
			regs: map[int]*term{},
			fregs: map[int]*term{},
			vregs: map[int]vecValue{},
			rvcfg: &rvVectorConfigVerify{lanes: 4, bits: 32},
			flags: &flagsFact{},
		}
		for reg := 0; reg < 32; reg++ {
			s.regs[reg] = constTerm(uint64(reg+1), 64)
			s.fregs[reg] = constTerm(uint64(reg+1), 64)
			s.vregs[reg] = vecValue{}
		}
		(&pathExecutor{arch: arch}).forgetCallerSaved(s)
		if arch == ArchRV64 {
			if s.rvcfg != nil || len(s.vregs) != 0 {
				t.Fatal("RV64 call retained vector or vl/vtype state")
			}
			for reg := 0; reg < 32; reg++ {
				_, exists := s.fregs[reg]
				want := reg == 8 || reg == 9 || (reg >= 18 && reg <= 27)
				if exists != want {
					t.Errorf("RV64 float register f%d: bound=%v, want=%v", reg, exists, want)
				}
			}
			if s.regs[1] != nil || !s.invalidEntryGPR[1] {
				t.Error("RV64 call retained or resurrected ra/x1")
			}
		} else {
			for reg := 0; reg < 32; reg++ {
				_, exists := s.vregs[reg]
				want := reg >= 8 && reg <= 15
				if exists != want {
					t.Errorf("ARM64 vector register v%d: bound=%v, want=%v", reg, exists, want)
				}
			}
			if s.flags != nil {
				t.Error("ARM64 call retained NZCV condition flags")
			}
			if s.regs[30] != nil || !s.invalidEntryGPR[30] {
				t.Error("ARM64 call retained or resurrected x30")
			}
		}
	}
}

// Preserve the architectural invariant structurally. When new call-result
// shapes are added, they must go through the same cross-class policy rather
// than manually invalidating one class and forgetting the others.
func TestNativeCallReturnBranchesUseOneABIPolicy(t *testing.T) {
	src, err := os.ReadFile("verify_calls.go")
	if err != nil {
		t.Fatal(err)
	}
	code := string(src)
	index := strings.Index(code, "func (x *pathExecutor) summarizeCall(")
	if index < 0 {
		t.Fatal("missing production call summary")
	}
	body := code[index:]
	if n := strings.Count(body, "x.forgetCallerSaved(state)"); n != 6 {
		t.Fatalf("call summary has %d ABI invalidations, want one in each of six return shapes", n)
	}
	for _, forbidden := range []string{
		"state.clobberGPR(",
		"delete(state.regs",
		"delete(state.fregs",
		"delete(state.vregs",
	} {
		if strings.Contains(body, forbidden) {
			t.Fatalf("manual register clobber in native call summary: %s", forbidden)
		}
	}
}
