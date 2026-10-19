package asm

// verifierISA is the explicitly registered machine/ABI policy consumed by
// the symbolic verifier's native call boundaries. It is deliberately not a
// claim that target-independent execution or whole-program refinement is
// complete: instruction semantics and encoding remain ISA-specific.
//
// The tables below preserve the verifier's existing AAPCS64 and RV64 LP64D
// clobber behavior exactly. Adding a lane requires a new reviewed policy,
// seam-checker dispatch, independent semantics, and target proof evidence.
type verifierISA struct {
	arch string
	// Entry-readable differs from call-preserved: on RV64, ra (x1) is
	// readable at function entry but is clobbered by an ordinary call.
	entryReadableGPR func(int) bool
	clobberedGPR     []int
	preservedFPR     func(int) bool // nil: this policy does not model FPR clobbers
	preservedVector  func(int) bool // nil: this policy does not model vector clobbers
	invalidateFlags  bool
}

var verifierArm64ISA = verifierISA{
	arch:             ArchArm64,
	entryReadableGPR: calleeSavedRegister,
	clobberedGPR:     []int{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 30},
	preservedVector:  calleeSavedVector,
	invalidateFlags:  true,
}

var verifierRV64ISA = verifierISA{
	arch:             ArchRV64,
	entryReadableGPR: rv64Preserved,
	clobberedGPR:     []int{1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31},
	preservedFPR:     rv64FloatCalleeSaved,
}

// verifierISAFor is the only native verifier policy dispatch. It must never
// substitute AArch64 policy for empty or unrecognized target names.
func verifierISAFor(arch string) (*verifierISA, bool) {
	switch arch {
	case ArchArm64:
		return &verifierArm64ISA, true
	case ArchRV64:
		return &verifierRV64ISA, true
	default:
		return nil, false
	}
}

func verifierEntryReadableGPR(arch string, reg int) bool {
	isa, ok := verifierISAFor(arch)
	return ok && isa.entryReadableGPR(reg)
}

// forgetCallerSaved applies only the target's established call clobber rules.
// RV64 vector and flags policy is unchanged here; completing RVV call-state
// semantics requires a separate ABI review and differential proof gate.
func (isa *verifierISA) forgetCallerSaved(state *symbolicState) {
	for _, reg := range isa.clobberedGPR {
		delete(state.regs, reg)
		delete(state.bounds, reg)
	}
	if isa.preservedFPR != nil {
		for reg := 0; reg < 32; reg++ {
			if !isa.preservedFPR(reg) {
				delete(state.fregs, reg)
			}
		}
	}
	if isa.preservedVector != nil {
		for reg := 0; reg < 32; reg++ {
			if !isa.preservedVector(reg) {
				delete(state.vregs, reg)
			}
		}
	}
	if isa.invalidateFlags {
		state.flags = nil
	}
}
