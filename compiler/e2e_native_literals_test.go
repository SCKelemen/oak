package compiler

import (
	"os"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// TestE2ENativeLiteralsVerdicts pins the verifier's verdicts on the
// literal scanner's kernel (stdlib/literals.oak): `verify_first`, whose
// body reads a frame array at the loop's index and calls `literal_at`
// inside a nested loop, is proven by coupling its three loops
// (docs/spec/94-assembler.md §8, "The literal scanner's kernel").
func TestE2ENativeLiteralsVerdicts(t *testing.T) {
	requireArm64Host(t)
	src, err := os.ReadFile("../stdlib/literals.oak")
	if err != nil {
		t.Skip(err)
	}
	var infos []string
	comp := New().WithSource("literals.oak", string(src)+"\nmain: (): u32 = u32(0)\n").WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	if _, err := comp.EmitNative(HostObjectFormat()).Get(); err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	joined := strings.Join(infos, "\n")
	if !strings.Contains(joined, "asm unit verify_first_neon_abi: proven equal to its Oak body at the bit level — 3 nested data-dependent loops coupled inductively") {
		t.Errorf("verify_first must be proven by loop coupling; diagnostics:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit longest: proven") {
		t.Errorf("longest must be proven; diagnostics:\n%s", joined)
	}
}
