package codegen

import (
	"fmt"

	"github.com/SCKelemen/oak/semir"
)

// ERET is emitted as a pay-for-use noreturn helper. The C bootstrap backend
// needs a syntactic carrier for Oak's uninhabited `never` type because the
// generic expression emitter writes `return eret()`. `oak_never` is therefore
// an ABI spelling only: the helper is noreturn and can never produce a value of
// that carrier. No source-level value constructor exists.
//
// __builtin_unreachable is compiler control-flow metadata after the
// architectural transfer; it emits no runtime instruction and prevents a
// synthetic C return path after ERET.
func init() {
	for _, member := range semir.Arm64ControlTransferMembers() {
		spec, ok := semir.LookupArm64ControlTransfer(member)
		if !ok {
			continue
		}
		// A carried register is a local register variable pinned to the
		// architectural register and named as an input of the asm
		// statement, so the value is in that register at the instruction;
		// the C compiler moves it there (`mov x0, xN`) and emits nothing
		// else. The handoff adds no instruction of its own.
		params, pins, inputs := "void", "", ""
		for i, reg := range spec.Carries {
			name := fmt.Sprintf("value%d", i)
			if i == 0 {
				params = ""
			} else {
				params += ", "
				inputs += ", "
			}
			params += "u64 " + name
			pins += fmt.Sprintf("  register u64 %s_%s __asm__(%q) = %s;\n", reg, name, reg, name)
			inputs += fmt.Sprintf("\"r\"(%s_%s)", reg, name)
		}
		arm64HelperSources[member] = `/* oak_never (the uninhabited bottom carrier) is emitted with the primitive typedefs; ERET never produces it */
__attribute__((noreturn)) static inline oak_never oak_arm64_` + member + `( ` + params + ` ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
` + pins + `  __asm__ volatile("` + spec.Instruction + `" :: ` + inputs + ` : "memory");
  __builtin_unreachable();
#else
#error "arm64.` + member + ` requires an AArch64 target"
#endif
}
`
	}
}
