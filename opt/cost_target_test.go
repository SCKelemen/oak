package opt

import (
	"strings"
	"testing"
)

func TestCostsForNativeArchitectureIsExplicit(t *testing.T) {
	for _, tc := range []struct {
		arch string
		want TargetCosts
	}{
		{arch: "arm64", want: AArch64Costs},
		{arch: "rv64", want: RV64Costs},
	} {
		got, err := CostsFor(tc.arch)
		if err != nil {
			t.Fatalf("CostsFor(%q): %v", tc.arch, err)
		}
		if got != tc.want || got.Arch != tc.arch {
			t.Fatalf("CostsFor(%q) = %+v, want %+v", tc.arch, got, tc.want)
		}
	}
}

func TestCostsForRejectsUnsupportedArchitecture(t *testing.T) {
	for _, arch := range []string{"", "wasm32", "x86_64", "aarch64", "ARM64", "rv64v", "unknown"} {
		got, err := CostsFor(arch)
		if err == nil || !strings.Contains(err.Error(), "no native cost model") {
			t.Fatalf("CostsFor(%q) returned %+v, %v; expected diagnostic", arch, got, err)
		}
		if got != (TargetCosts{}) {
			t.Fatalf("CostsFor(%q) returned nonzero unsupported costs: %+v", arch, got)
		}
	}
}
