package typechecker

import "github.com/SCKelemen/oak/semir"

// System-register operations are ordinary compiler-known arm64 functions at
// the source level. Register identity and access direction live in SemIR; the
// source never carries a runtime register enum.
func init() {
	for _, spec := range semir.Arm64SysRegs() {
		arm64Intrinsics[spec.ReadMember()] = &FunctionType{
			Parameters: nil,
			ReturnType: &PrimitiveType{Name: "u64"},
		}
		if spec.Access.CanWrite() {
			arm64Intrinsics[spec.WriteMember()] = &FunctionType{
				Parameters: []Type{&PrimitiveType{Name: "u64"}},
				ReturnType: &UnitType{},
			}
		}
	}
}
