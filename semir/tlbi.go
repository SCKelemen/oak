package semir

import "fmt"

// Arm64TLBISpec names one closed AArch64 translation-maintenance operation.
// Operation and Shareability describe the instruction spelling; they do not
// grant a barrier, completion, or invalidation-success capability.
type Arm64TLBISpec struct {
	Member       string
	Operation    string
	Shareability string
	Instruction  string
}

func (s Arm64TLBISpec) Effect() Effect {
	return Effect{
		Namespace:  "Machine",
		Name:       "TranslationMaintenance",
		Parameters: []string{"tlbi", s.Operation, s.Shareability},
	}
}

// LookupArm64TLBI is deliberately a closed lookup: Oak source cannot supply
// an instruction name, target, scope, or operand dynamically.
func LookupArm64TLBI(member string) (Arm64TLBISpec, bool) {
	switch member {
	case "tlbi_vmalls12e1is":
		return Arm64TLBISpec{
			Member:       member,
			Operation:    "vmalls12e1",
			Shareability: "inner-shareable",
			Instruction:  "tlbi vmalls12e1is",
		}, true
	default:
		return Arm64TLBISpec{}, false
	}
}

func Arm64TLBIMembers() [1]string {
	return [1]string{"tlbi_vmalls12e1is"}
}

func ValidateArm64TLBI(spec Arm64TLBISpec) error {
	if spec.Member != "tlbi_vmalls12e1is" {
		return fmt.Errorf("unsupported TLBI member %q", spec.Member)
	}
	if spec.Operation != "vmalls12e1" {
		return fmt.Errorf("TLBI %q has operation %q", spec.Member, spec.Operation)
	}
	if spec.Shareability != "inner-shareable" {
		return fmt.Errorf("TLBI %q has shareability %q", spec.Member, spec.Shareability)
	}
	if spec.Instruction != "tlbi vmalls12e1is" {
		return fmt.Errorf("TLBI %q has instruction %q", spec.Member, spec.Instruction)
	}
	return nil
}
