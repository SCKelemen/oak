package asm

import (
	"strings"
	"testing"
)

func TestNativeVerifierISASelectionFailsClosed(t *testing.T) {
	for _, arch := range []string{ArchArm64, ArchRV64} {
		isa, ok := verifierISAFor(arch)
		if !ok || isa == nil || isa.arch != arch {
			t.Fatalf("verifierISAFor(%q) = %v, %v", arch, isa, ok)
		}
	}
	for _, arch := range []string{"", "wasm32", "amd64", "aarch64", "riscv64", "ARM64", "unknown"} {
		isa, ok := verifierISAFor(arch)
		if ok || isa != nil {
			t.Fatalf("unsupported architecture %q selected a verifier ISA: %v", arch, isa)
		}
		if verifierEntryReadableGPR(arch, 19) {
			t.Fatalf("unsupported architecture %q inherited AArch64 register preservation", arch)
		}
		// The seam checker must reject before dereferencing an absent source
		// signature; a mistaken AArch64 fallback would panic here.
		fn := &Function{Arch: arch, Name: "invalid_isa"}
		findings := Check(fn, nil, nil)
		if len(findings) == 0 || !strings.Contains(strings.Join(findings, " "), "unsupported native verifier architecture") {
			t.Fatalf("Check(%q) = %v; wanted explicit refusal", arch, findings)
		}
		verdict := Verify(fn, nil, nil)
		if verdict.Kind != VerdictTrusted || !strings.Contains(verdict.Message, "unsupported native verifier architecture") {
			t.Fatalf("Verify(%q) = %+v; wanted non-proven refusal", arch, verdict)
		}
		x := &pathExecutor{arch: arch}
		if reason, ok := x.summarizeCall(Instruction{Mnemonic: "call"}, &symbolicState{}); ok || !strings.Contains(reason, "unsupported native verifier architecture") {
			t.Fatalf("summarizeCall(%q) = %q, %v", arch, reason, ok)
		}
	}
	if findings := Check(nil, nil, nil); len(findings) == 0 {
		t.Fatal("nil native function admitted by seam checker")
	}
	if verdict := Verify(nil, nil, nil); verdict.Kind == VerdictProven {
		t.Fatal("nil native function produced a proof")
	}
}

func TestNativeVerifierEntryReadableRegistersAreISAOwned(t *testing.T) {
	for _, tc := range []struct {
		arch      string
		preserved []int
		volatile  []int
	}{
		{ArchArm64, []int{19, 20, 28, 29, 30}, []int{0, 1, 8, 9, 17, 18}},
		{ArchRV64, []int{1, 8, 9, 18, 27}, []int{0, 5, 6, 7, 10, 17, 28, 31}},
	} {
		for _, reg := range tc.preserved {
			if !verifierEntryReadableGPR(tc.arch, reg) {
				t.Errorf("%s entry-readable register %d not admitted", tc.arch, reg)
			}
		}
		for _, reg := range tc.volatile {
			if verifierEntryReadableGPR(tc.arch, reg) {
				t.Errorf("%s unbound register %d erroneously admitted", tc.arch, reg)
			}
		}
	}
}

func TestUnsupportedNativeVerifierClobberDiscardsAllState(t *testing.T) {
	state := &symbolicState{
		regs: map[int]*term{0: constTerm(1, 64)},
		bounds: map[int]uint64{0: 1},
		fregs: map[int]*term{0: constTerm(1, 64)},
		vregs: map[int]vecValue{0: {}},
		flags: &flagsFact{},
	}
	(&pathExecutor{arch: "unknown"}).forgetCallerSaved(state)
	if state.regs != nil || state.bounds != nil || state.fregs != nil || state.vregs != nil || state.flags != nil {
		t.Fatal("unrecognized architecture retained symbolic assumptions")
	}
}
