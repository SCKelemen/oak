package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

const nativeOptIRProgram = `
common: (x: u32): u32 {
  left: u32 = x + u32(1)
  right: u32 = x + u32(1)
  dead: u32 = x * u32(2)
  left + right
}

main: (): i32 = i32_bits_u32(common(u32(20)))
`

func TestE2ENativeSelectsVerifiedOptimizedOptIR(t *testing.T) {
	requireArm64Host(t)
	var diagnostics []string
	comp := New().WithSource("native_optir.oak", nativeOptIRProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			diagnostics = append(diagnostics, d.Message)
		}
	})
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	joined := strings.Join(diagnostics, "\n")
	if !strings.Contains(joined, "common: optimized OptIR selected") || !strings.Contains(joined, "generic SSA operation(s) eliminated or hoisted, proven") {
		t.Fatalf("optimized SSA candidate was not selected and proven:\n%s", joined)
	}
	if verdict := model.NativeVerdicts["common"]; verdict.Kind.String() != "proven" {
		t.Fatalf("common verdict = %s (%s)", verdict.Kind, verdict.Message)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_optir", comp); abnormal || code != 42 {
		t.Fatalf("native execution = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
