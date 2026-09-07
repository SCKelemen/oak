package typechecker

import "github.com/SCKelemen/oak/semir"

// ERET is a genuine non-returning machine operation.  It is not typed as Unit
// merely to fit C: the source type is () -> never, matching Oak's existing
// bottom type.  Functions that end in ERET should therefore declare `never`
// until general expected-position bottom coercion is wired through all checker
// paths.
func init() {
	for _, member := range semir.Arm64ControlTransferMembers() {
		arm64Intrinsics[member] = &FunctionType{
			Parameters: []Type{},
			ReturnType: &NeverType{},
		}
	}
}
