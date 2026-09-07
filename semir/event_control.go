package semir

import "fmt"

// EventControlOperation identifies the exact architectural instruction class.
type EventControlOperation string

const (
	EventDAIFSet EventControlOperation = "daifset"
	EventDAIFClr EventControlOperation = "daifclr"
	EventWFI     EventControlOperation = "wfi"
	EventWFE     EventControlOperation = "wfe"
	EventSEV     EventControlOperation = "sev"
)

// Arm64EventControlSpec is a compile-time machine operation. Every member is
// nullary and returns Unit; any DAIF immediate is part of source identity.
type Arm64EventControlSpec struct {
	Member      string
	Operation   EventControlOperation
	Instruction string
}

func (s Arm64EventControlSpec) Effect() Effect {
	return Effect{Namespace: "Machine", Name: "EventControl", Parameters: []string{string(s.Operation), s.Instruction}}
}

func LookupArm64EventControl(member string) (Arm64EventControlSpec, bool) {
	switch member {
	case "daifset_irq":
		return Arm64EventControlSpec{Member: member, Operation: EventDAIFSet, Instruction: "msr daifset, #2"}, true
	case "daifclr_irq":
		return Arm64EventControlSpec{Member: member, Operation: EventDAIFClr, Instruction: "msr daifclr, #2"}, true
	case "wfi":
		return Arm64EventControlSpec{Member: member, Operation: EventWFI, Instruction: "wfi"}, true
	case "wfe":
		return Arm64EventControlSpec{Member: member, Operation: EventWFE, Instruction: "wfe"}, true
	case "sev":
		return Arm64EventControlSpec{Member: member, Operation: EventSEV, Instruction: "sev"}, true
	default:
		return Arm64EventControlSpec{}, false
	}
}

func Arm64EventControlMembers() [5]string {
	return [5]string{"daifset_irq", "daifclr_irq", "wfi", "wfe", "sev"}
}

func ValidateArm64EventControl(spec Arm64EventControlSpec) error {
	if spec.Member == "" || spec.Instruction == "" {
		return fmt.Errorf("event-control member and instruction must be non-empty")
	}
	switch spec.Operation {
	case EventDAIFSet:
		if spec.Instruction != "msr daifset, #2" {
			return fmt.Errorf("DAIFSet IRQ must encode immediate #2")
		}
	case EventDAIFClr:
		if spec.Instruction != "msr daifclr, #2" {
			return fmt.Errorf("DAIFClr IRQ must encode immediate #2")
		}
	case EventWFI, EventWFE, EventSEV:
		if spec.Instruction != string(spec.Operation) {
			return fmt.Errorf("event instruction %q does not match operation %q", spec.Instruction, spec.Operation)
		}
	default:
		return fmt.Errorf("unknown event-control operation %q", spec.Operation)
	}
	return nil
}
