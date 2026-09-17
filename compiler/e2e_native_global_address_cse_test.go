package compiler

import (
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/nativegen"
)

const nativeGlobalAddressCSEProgram = `
st: u32 = u32(0)
touch: (value: u32, choose: Bool): u32 {
  st = value
  prior: u32 = st
  choose ? {
    st = prior + u32(1)
  } | {
    st = prior + u32(2)
  }
  st
}
main: (): i32 {
  assert(touch(u32(10), true) == u32(11))
  assert(touch(u32(20), false) == u32(22))
  42
}
`

func TestE2ENativeGlobalAddressCSE(t *testing.T) {
	requireArm64Host(t)
	t.Setenv("OAK_NATIVE_ONLY", "touch")
	// Exercise the late emitted-assembly candidate rather than the separate
	// direct-OptIR lowering, which forwards this small fixture's global values.
	t.Setenv("OAK_OPT_SKIP", nativegen.TransformOptIR)
	comp := New().WithSource("global_address_cse.oak", nativeGlobalAddressCSEProgram).WithNativeBodies().WithNativeAsm()
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	if verdict := model.NativeVerdicts["touch"]; verdict.Kind != asm.VerdictProven {
		t.Fatalf("touch: %s: %s", verdict.Kind, verdict.Message)
	}
	var selected *asm.Function
	for _, fn := range model.AsmFunctions {
		if fn.Name == "touch" {
			selected = fn
			break
		}
	}
	if selected == nil {
		t.Fatal("missing native touch")
	}
	if nativegen.SharedGlobalAddresses(selected) == 0 {
		t.Fatalf("the proven scalar-global address must be shared:\n%s", nativegen.Describe(selected))
	}
	if nativegen.Scheduled(selected) == 0 {
		t.Fatalf("scalar-global sharing must retain its scheduled parent:\n%s", nativegen.Describe(selected))
	}
	if _, code, abnormal := buildAndRunFrom(t, "global_address_cse", comp); abnormal || code != 42 {
		t.Fatalf("native: exit=(%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "global_address_cse_c", New().WithSource("global_address_cse.oak", nativeGlobalAddressCSEProgram)); abnormal || code != 42 {
		t.Fatalf("C: exit=(%d, abnormal=%v), want 42", code, abnormal)
	}
}
