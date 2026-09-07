package semir

// Arm64ControlTransferSpec describes an architectural control transfer that
// does not return to its Oak caller.  It is deliberately separate from event
// control and barriers: changing PC/exception level is neither waiting nor a
// memory-ordering operation.
type Arm64ControlTransferSpec struct {
	Member      string
	Instruction string
}

func (s Arm64ControlTransferSpec) Effect() Effect {
	return Effect{Namespace: "Machine", Name: "ControlTransfer", Parameters: []string{s.Member}}
}

// LookupArm64ControlTransfer is intentionally tiny in v1.  ERET consumes the
// architectural ELR_EL2/SPSR_EL2 state already installed by explicit sysreg
// operations and transfers control according to the Arm architecture.
func LookupArm64ControlTransfer(member string) (Arm64ControlTransferSpec, bool) {
	if member == "eret" {
		return Arm64ControlTransferSpec{Member: "eret", Instruction: "eret"}, true
	}
	return Arm64ControlTransferSpec{}, false
}

func Arm64ControlTransferMembers() [1]string {
	return [1]string{"eret"}
}
