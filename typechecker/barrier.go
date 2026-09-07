package typechecker

import "github.com/SCKelemen/oak/semir"

// Register the machine-barrier source surface in the same compiler-known arm64
// library used by the existing instruction functions. The SemIR catalog owns
// the names; the typechecker contributes only the source type: () -> ().
func init() {
	for _, member := range semir.Arm64BarrierMembers() {
		arm64Intrinsics[member] = &FunctionType{
			Parameters: []Type{},
			ReturnType: &UnitType{},
		}
	}
}

// Arm64IntrinsicArity exposes the checked arm64 library arity to backend code
// without maintaining a second independent signature table.
func Arm64IntrinsicArity(member string) (int, bool) {
	signature, ok := arm64Intrinsics[member]
	if !ok || signature == nil {
		return 0, false
	}
	return len(signature.Parameters), true
}
