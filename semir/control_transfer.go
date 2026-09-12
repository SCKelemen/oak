package semir

// Arm64ControlTransferSpec describes an architectural control transfer that
// does not return to its Oak caller.  It is deliberately separate from event
// control and barriers: changing PC/exception level is neither waiting nor a
// memory-ordering operation.
type Arm64ControlTransferSpec struct {
	Member      string
	Instruction string
	// Carries names the general registers the transfer hands to the target
	// exception level, in parameter order: `eret_x0(value)` delivers its
	// argument in x0 (docs/spec/100-aarch64-control-transfer.md, the
	// register handoff). ERET itself moves no general register; the
	// handoff is the values that are live in them at the instruction.
	Carries []string
}

func (s Arm64ControlTransferSpec) Effect() Effect {
	return Effect{Namespace: "Machine", Name: "ControlTransfer", Parameters: []string{s.Member}}
}

// Arity is the number of source arguments: one per carried register.
func (s Arm64ControlTransferSpec) Arity() int { return len(s.Carries) }

// arm64ControlTransfers is the fixed catalog. ERET consumes the
// architectural ELR/SPSR state already installed by explicit sysreg
// operations and transfers control according to the Arm architecture;
// eret_x0 is the same transfer with one u64 handed to the target in x0 —
// the argument a kernel's first EL0 thread, or a guest's entry, receives.
var arm64ControlTransfers = [...]Arm64ControlTransferSpec{
	{Member: "eret", Instruction: "eret"},
	{Member: "eret_x0", Instruction: "eret", Carries: []string{"x0"}},
}

// LookupArm64ControlTransfer is intentionally tiny.
func LookupArm64ControlTransfer(member string) (Arm64ControlTransferSpec, bool) {
	for i := range arm64ControlTransfers {
		if arm64ControlTransfers[i].Member == member {
			return arm64ControlTransfers[i], true
		}
	}
	return Arm64ControlTransferSpec{}, false
}

func Arm64ControlTransferMembers() [len(arm64ControlTransfers)]string {
	var members [len(arm64ControlTransfers)]string
	for i := range arm64ControlTransfers {
		members[i] = arm64ControlTransfers[i].Member
	}
	return members
}
