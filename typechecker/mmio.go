package typechecker

import "github.com/SCKelemen/oak/semir"

// MmioRegisterType is a nominal machine register-address capability. Width and
// access authority are part of static identity; there are no implicit
// conversions between RO/WO/RW handles or between access widths.
type MmioRegisterType struct {
	Width  semir.MmioWidth
	Access semir.MmioAccess
}

func (t *MmioRegisterType) String() string {
	if t == nil {
		return "arm64.MMIO<?>"
	}
	return "arm64.MMIO[" + t.Width.Carrier() + "," + string(t.Access) + "]"
}

func (t *MmioRegisterType) Equals(other Type) bool {
	o, ok := other.(*MmioRegisterType)
	return ok && t != nil && o != nil && t.Width == o.Width && t.Access == o.Access
}

// Register the SemIR-owned MMIO catalog into the existing arm64 machine
// library. The backend and evaluator resolve the same member names through
// semir.LookupArm64Mmio; the typechecker contributes only exact source types.
func init() {
	for _, spec := range semir.Arm64MmioMembers() {
		reg := &MmioRegisterType{Width: spec.Width, Access: spec.Access}
		carrier := &PrimitiveType{Name: spec.Width.Carrier()}
		switch spec.Operation {
		case semir.MmioConstruct:
			arm64Intrinsics[spec.Member] = &FunctionType{
				Parameters: []Type{&PrimitiveType{Name: "u64"}},
				ReturnType: reg,
			}
		case semir.MmioRead:
			arm64Intrinsics[spec.Member] = &FunctionType{
				Parameters: []Type{reg},
				ReturnType: carrier,
			}
		case semir.MmioWrite:
			arm64Intrinsics[spec.Member] = &FunctionType{
				Parameters: []Type{reg, carrier},
				ReturnType: &UnitType{},
			}
		}
	}
}
