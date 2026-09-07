package codegen

import "github.com/SCKelemen/oak/semir"

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
		arm64HelperSources[member] = `typedef u8 oak_never; /* uninhabited Oak bottom carrier; ERET never produces it */
__attribute__((noreturn)) static inline oak_never oak_arm64_eret( void ) {
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
