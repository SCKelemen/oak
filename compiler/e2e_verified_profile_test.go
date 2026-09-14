package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/target"
)

// The verified native profile (docs/spec/94-assembler.md §9, "The verified
// profile"): a program links under it only when every body the native
// backend lowered carries a proven verdict and none stayed with the C
// backend. The refusal is the burn-down list, grouped by reason.

const verifiedProfileProgram = `add3: (a: u32, b: u32, c: u32): u32 = a + b + c

clamp: (v: u32, hi: u32): u32 = v > hi ? hi | v

main: (): i32 {
  i32_bits_u32(clamp(add3(u32(1), u32(2), u32(3)), u32(4)) - u32(4))
}
`

// A shift by a non-constant count is a trusted verdict on both lanes: the
// verifier's term language has no variable shift.
const verifiedProfileHeldProgram = `shl: (x: u32, n: u32): u32 = x << n

main: (): i32 {
  i32_bits_u32(shl(u32(1), u32(3)) - u32(8))
}
`

func TestE2EVerifiedProfileLinksProvenBodies(t *testing.T) {
	for _, arch := range []string{target.ArchArm64, target.ArchRiscv64} {
		tgt := target.Target{OS: target.OSFreestanding, Arch: arch}
		image, err := New().WithSource("verified.oak", verifiedProfileProgram).WithTarget(tgt).WithVerifiedProfile().EmitExecutable().Get()
		if err != nil {
			t.Fatalf("%s: %v", tgt, err)
		}
		if len(image) == 0 {
			t.Fatalf("%s: empty image", tgt)
		}
	}
}

func TestE2EVerifiedProfileRefusesTrustedBodies(t *testing.T) {
	for _, arch := range []string{target.ArchArm64, target.ArchRiscv64} {
		tgt := target.Target{OS: target.OSFreestanding, Arch: arch}
		_, err := New().WithSource("verified.oak", verifiedProfileHeldProgram).WithTarget(tgt).WithVerifiedProfile().EmitExecutable().Get()
		if err == nil {
			t.Fatalf("%s: a trusted body linked under the verified profile", tgt)
		}
		for _, want := range []string{"verified profile: 1 bodies are not proven", "trusted: the Oak body contains a non-constant shift count (1): shl"} {
			if !strings.Contains(err.Error(), want) {
				t.Errorf("%s: refusal lacks %q:\n%s", tgt, want, err)
			}
		}
		// Without the profile the same program links: the body is trusted,
		// not refused.
		if _, err := New().WithSource("verified.oak", verifiedProfileHeldProgram).WithTarget(tgt).EmitExecutable().Get(); err != nil {
			t.Fatalf("%s: the plain native link refused a trusted body: %v", tgt, err)
		}
	}
}

// A body left to the C backend is refused with its reason.
func TestE2EVerifiedProfileRefusesCBodies(t *testing.T) {
	source := "scale: (x: f64) -> f64 = x * 2.0\n\nmain: (): i32 {\n  scale(1.0) == 2.0 ? 0 | 1\n}\n"
	_, err := New().WithSource("verified.oak", source).WithTarget(target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}).WithVerifiedProfile().EmitExecutable().Get()
	if err == nil || !strings.Contains(err.Error(), "left to the C backend: ") || !strings.Contains(err.Error(), "scale") {
		t.Fatalf("a C body linked under the verified profile, or the reason is missing: %v", err)
	}
}
