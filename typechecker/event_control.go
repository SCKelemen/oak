package typechecker

import "github.com/SCKelemen/oak/semir"

// Register nullary machine-control operations in the existing arm64 catalog.
func init() {
	for _, member := range semir.Arm64EventControlMembers() {
		arm64Intrinsics[member] = &FunctionType{
			Parameters: []Type{},
			ReturnType: &UnitType{},
		}
	}
}
