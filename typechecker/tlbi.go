package typechecker

import "github.com/SCKelemen/oak/semir"

// Register closed translation-maintenance operations independently of the
// barrier catalog. Each is a nullary, Unit-valued machine operation.
func init() {
	for _, member := range semir.Arm64TLBIMembers() {
		arm64Intrinsics[member] = &FunctionType{
			Parameters: []Type{},
			ReturnType: &UnitType{},
		}
	}
}
