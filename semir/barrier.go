package semir

import "fmt"

// BarrierOperation is the architectural barrier class, independent of its
// scope/domain option. ISB is intentionally distinct from data-memory barriers.
type BarrierOperation string

const (
	BarrierDMB BarrierOperation = "dmb"
	BarrierDSB BarrierOperation = "dsb"
	BarrierISB BarrierOperation = "isb"
)

// BarrierScope is the architectural option encoded in a DMB/DSB instruction.
// ISB has no data-shareability scope and therefore uses BarrierScopeNone.
type BarrierScope string

const (
	BarrierScopeNone  BarrierScope = ""
	BarrierScopeISHLD BarrierScope = "ishld"
	BarrierScopeISH   BarrierScope = "ish"
	BarrierScopeSY    BarrierScope = "sy"
)

// Arm64BarrierSpec is the single semantic descriptor for source identity,
// architectural operation, scope, and effect projection. Barriers are all
// nullary and return Unit; the source surface carries no runtime barrier enum.
type Arm64BarrierSpec struct {
	Member    string
	Operation BarrierOperation
	Scope     BarrierScope
}

func (s Arm64BarrierSpec) Effect() Effect {
	parameters := []string{string(s.Operation)}
	if s.Scope != BarrierScopeNone {
		parameters = append(parameters, string(s.Scope))
	}
	return Effect{Namespace: "Machine", Name: "Barrier", Parameters: parameters}
}

func (s Arm64BarrierSpec) Instruction() string {
	if s.Operation == BarrierISB {
		return "isb"
	}
	return string(s.Operation) + " " + string(s.Scope)
}

// LookupArm64Barrier defines the complete first machine-barrier source surface.
// The spelling mirrors the exact AArch64 instruction option so a reviewer can
// infer the machine contract directly from Oak source.
func LookupArm64Barrier(member string) (Arm64BarrierSpec, bool) {
	switch member {
	case "dmb_ishld":
		return Arm64BarrierSpec{Member: member, Operation: BarrierDMB, Scope: BarrierScopeISHLD}, true
	case "dmb_ish":
		return Arm64BarrierSpec{Member: member, Operation: BarrierDMB, Scope: BarrierScopeISH}, true
	case "dmb_sy":
		return Arm64BarrierSpec{Member: member, Operation: BarrierDMB, Scope: BarrierScopeSY}, true
	case "dsb_ish":
		return Arm64BarrierSpec{Member: member, Operation: BarrierDSB, Scope: BarrierScopeISH}, true
	case "dsb_sy":
		return Arm64BarrierSpec{Member: member, Operation: BarrierDSB, Scope: BarrierScopeSY}, true
	case "isb":
		return Arm64BarrierSpec{Member: member, Operation: BarrierISB, Scope: BarrierScopeNone}, true
	default:
		return Arm64BarrierSpec{}, false
	}
}

// Arm64BarrierMembers returns a stable, allocation-free-to-query catalog source
// for compiler layers. The returned array is a value; callers may range it
// without maintaining a second list of barrier names.
func Arm64BarrierMembers() [6]string {
	return [6]string{"dmb_ishld", "dmb_ish", "dmb_sy", "dsb_ish", "dsb_sy", "isb"}
}

func ValidateArm64Barrier(spec Arm64BarrierSpec) error {
	if spec.Member == "" {
		return fmt.Errorf("barrier member is empty")
	}
	switch spec.Operation {
	case BarrierDMB:
		if spec.Scope != BarrierScopeISHLD && spec.Scope != BarrierScopeISH && spec.Scope != BarrierScopeSY {
			return fmt.Errorf("DMB has unsupported scope %q", spec.Scope)
		}
	case BarrierDSB:
		if spec.Scope != BarrierScopeISH && spec.Scope != BarrierScopeSY {
			return fmt.Errorf("DSB has unsupported scope %q", spec.Scope)
		}
	case BarrierISB:
		if spec.Scope != BarrierScopeNone {
			return fmt.Errorf("ISB cannot carry data shareability scope %q", spec.Scope)
		}
	default:
		return fmt.Errorf("unknown barrier operation %q", spec.Operation)
	}
	return nil
}
