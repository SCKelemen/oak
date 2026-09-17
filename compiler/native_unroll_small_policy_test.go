package compiler

import (
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/opt"
)

func TestNativeUnrollSmallExperimentalPolicy(t *testing.T) {
	for _, tc := range []struct {
		name, enabled, skip string
		want                bool
	}{
		{"default off", "", "", false},
		{"explicit off", "0", "", false},
		{"unknown value", "true", "", false},
		{"opt in", "1", "", true},
		{"skip wins", "1", " unroll-small ", false},
		{"full strategy skipped", "1", "unroll-constant", true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			t.Setenv("OAK_NATIVE_UNROLL_SMALL", tc.enabled)
			t.Setenv("OAK_OPT_SKIP", tc.skip)
			registry := nativeSearch(asm.ArchArm64, nil).Registry
			tr, found := registry.Lookup(nativegen.TransformUnrollSmall)
			if found != tc.want {
				t.Fatalf("offered=%v, want %v", found, tc.want)
			}
			if tc.skip != "unroll-constant" {
				if _, full := registry.Lookup(nativegen.TransformUnrollConst); !full {
					t.Fatal("experimental policy removed ordinary full unrolling")
				}
			}
			if !found {
				return
			}
			if gate, ok := tr.(opt.Gated); !ok || !gate.NeedsVerdict() || tr.Proof() != opt.LawLicensed {
				t.Fatal("experimental unrolling lost its law and independent verdict gate")
			}
			if neutral, ok := tr.(opt.Neutral); ok && neutral.ShapeNeutral() {
				t.Fatal("unrolled body cannot inherit a neutral-body verdict")
			}
			if tr.Apply(opt.Identity(nativegen.Lane{Arch: asm.ArchRV64})) != nil {
				t.Fatal("small unrolling crossed into the RV64 lane")
			}
		})
	}
}
