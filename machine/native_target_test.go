package machine

import (
	"github.com/SCKelemen/oak/asm"
	"testing"
)

func TestSharedNativeTargetSelection(t *testing.T) {
	for _, arch := range []string{asm.ArchArm64, asm.ArchRV64, "", "unknown", "riscv64", "wasm32"} {
		target, err := targetFor(arch)
		canonical := arch
		if canonical == "" {
			canonical = asm.ArchArm64
		}
		shared, sharedErr := asm.ResolveNativeTarget(canonical)
		if (err == nil) != (sharedErr == nil) {
			t.Fatalf("%q: machine/shared disagreement", arch)
		}
		if err == nil && target.arch != shared.Arch() {
			t.Fatalf("%q: wrong machine lane", arch)
		}
	}
}
