package codegen

import "github.com/SCKelemen/oak/semir"

// ERET is emitted as a pay-for-use noreturn helper.  __builtin_unreachable is
// compiler control-flow metadata after the architectural transfer; it emits no
// runtime instruction and prevents a synthetic C return path after ERET.
func init() {
	for _, member := range semir.Arm64ControlTransferMembers() {
		spec, ok := semir.LookupArm64ControlTransfer(member)
		if !ok {
			continue
		}
		arm64HelperSources[member] = `__attribute__((noreturn)) static inline void oak_arm64_eret( void ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  __asm__ volatile("` + spec.Instruction + `" ::: "memory");
  __builtin_unreachable();
#else
#error "arm64.eret requires an AArch64 target"
#endif
}
`
	}
}
