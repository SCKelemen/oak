package codegen

import (
	"fmt"

	"github.com/SCKelemen/oak/semir"
)

func mmioAccessName(access semir.MmioAccess) string {
	switch access {
	case semir.MmioReadOnly:
		return "ro"
	case semir.MmioWriteOnly:
		return "wo"
	case semir.MmioReadWrite:
		return "rw"
	default:
		return "invalid"
	}
}

// init installs exact helper source for every SemIR-owned MMIO member into the
// existing pay-for-use arm64 helper catalog. Runtime representation of a typed
// register handle is exactly u64 address bits; width/access tags are erased
// after type checking and never consume storage or dispatch cycles.
func init() {
	for _, spec := range semir.Arm64MmioMembers() {
		carrier := spec.Width.Carrier()
		name := "oak_arm64_" + spec.Member
		switch spec.Operation {
		case semir.MmioConstruct:
			mask := spec.Width.Bytes() - 1
			arm64HelperSources[spec.Member] = fmt.Sprintf(`static inline u64 %s( u64 address ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  if ((address & %dULL) != 0ULL) { __builtin_trap(); }
  return address;
#else
#error "arm64 MMIO register construction requires an AArch64 target"
#endif
}
`, name, mask)
		case semir.MmioRead:
			arm64HelperSources[spec.Member] = fmt.Sprintf(`static inline %s %s( u64 address ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  return *(volatile %s *)(uintptr_t)address;
#else
#error "arm64 MMIO read requires an AArch64 target"
#endif
}
`, carrier, name, carrier)
		case semir.MmioWrite:
			arm64HelperSources[spec.Member] = fmt.Sprintf(`static inline void %s( u64 address, %s value ) {
#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)
  *(volatile %s *)(uintptr_t)address = value;
#else
#error "arm64 MMIO write requires an AArch64 target"
#endif
}
`, name, carrier, carrier)
		}
	}
}
