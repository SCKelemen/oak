package codegen

import (
	"fmt"

	"github.com/SCKelemen/oak/semir"
)

// Install pay-for-use AArch64 MRS/MSR helpers into the existing machine-library
// catalog. Register identity is compile-time source identity: generated code
// carries no string/enum lookup, allocation, callback, or runtime dispatch.
func init() {
	for _, spec := range semir.Arm64SysRegs() {
		readName := spec.ReadMember()
		arm64HelperSources[readName] = fmt.Sprintf(`static inline u64 oak_arm64_%s( void ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  u64 value;
  __asm__ volatile("mrs %%0, %s" : "=r"(value) :: "memory");
  return value;
#else
#error "arm64.%s requires an AArch64 target"
#endif
}
`, readName, spec.Asm, readName)

		if spec.Access.CanWrite() {
			writeName := spec.WriteMember()
			arm64HelperSources[writeName] = fmt.Sprintf(`static inline void oak_arm64_%s( u64 value ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  __asm__ volatile("msr %s, %%0" :: "r"(value) : "memory");
#else
#error "arm64.%s requires an AArch64 target"
#endif
}
`, writeName, spec.Asm, writeName)
		}
	}
}
