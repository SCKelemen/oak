package codegen

import (
	"fmt"

	"github.com/SCKelemen/oak/semir"
)

// The C bootstrap path keeps the instruction occurrence and ordinary-memory
// compiler ordering explicit. The memory clobber is not an architectural DSB,
// completion guarantee, or proof that an invalidation took effect.
const arm64TLBIHelper = `static inline void oak_arm64_%s( void ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  __asm__ volatile("%s" ::: "memory");
#else
#error "arm64.%s requires an AArch64 target"
#endif
}
`

func init() {
	for _, member := range semir.Arm64TLBIMembers() {
		spec, ok := semir.LookupArm64TLBI(member)
		if !ok {
			panic(fmt.Sprintf("arm64 TLBI catalog member %q has no specification", member))
		}
		if err := semir.ValidateArm64TLBI(spec); err != nil {
			panic(fmt.Sprintf("invalid arm64 TLBI catalog member %q: %v", member, err))
		}
		arm64HelperSources[spec.Member] = fmt.Sprintf(
			arm64TLBIHelper, spec.Member, spec.Instruction, spec.Member,
		)
	}
}
