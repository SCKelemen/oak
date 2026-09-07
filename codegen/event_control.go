package codegen

import (
	"fmt"

	"github.com/SCKelemen/oak/semir"
)

// Event-control operations are compile-time-selected, pay-for-use helpers.
// They carry no runtime opcode and inject no barriers beyond the named
// architectural instruction itself.
func init() {
	for _, member := range semir.Arm64EventControlMembers() {
		spec, ok := semir.LookupArm64EventControl(member)
		if !ok {
			continue
		}
		arm64HelperSources[member] = fmt.Sprintf(`static inline void oak_arm64_%s( void ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  __asm__ volatile("%s" ::: "memory");
#else
#error "arm64.%s requires an AArch64 target"
#endif
}
`, member, spec.Instruction, member)
	}
}
