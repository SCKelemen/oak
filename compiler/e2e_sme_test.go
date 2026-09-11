package compiler

import (
	"os/exec"
	"runtime"
	"strings"
	"testing"
)

// requireSME skips where the host lacks the Scalable Matrix Extension
// (the M4 reports it through sysctl on macOS).
func requireSME(t *testing.T) {
	t.Helper()
	requireArm64Host(t)
	if runtime.GOOS != "darwin" {
		t.Skip("SME detection is implemented for macOS hosts")
	}
	out, err := exec.Command("sysctl", "-n", "hw.optional.arm.FEAT_SME").Output()
	if err != nil || strings.TrimSpace(string(out)) != "1" {
		t.Skip("host has no SME")
	}
}

// The examples/sme package: an outer-product matrix multiply on the matrix
// unit (docs/spec/94-assembler.md §9), encoded by the Oak assembler into
// the companion object and executed against its Oak body, then the same
// unit through the C toolchain's assembler, then the portable fallback.
func TestE2EExampleSMEPackage(t *testing.T) {
	requireSME(t)
	native := New().WithPackageDir("../examples/sme").WithNativeAsm()
	_, code, abnormal := buildAndRunFrom(t, "example_sme_native", native)
	if abnormal || code != 42 {
		t.Fatalf("native asm: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	viaC := New().WithPackageDir("../examples/sme")
	for _, flags := range [][]string{nil, {"-DOAK_PORTABLE_INTRINSICS"}} {
		_, code, abnormal := buildAndRunFrom(t, "example_sme", viaC, flags...)
		if abnormal || code != 42 {
			t.Fatalf("flags %v: exit = (%d, abnormal=%v), want 42", flags, code, abnormal)
		}
	}
}
