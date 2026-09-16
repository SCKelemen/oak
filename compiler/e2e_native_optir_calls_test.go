package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

const nativeOptIRCallProgram = `
pub inc: (a: u32): u32 = a + u32(1)

pub optimized_call: (a: u32): u32 {
  left: u32 = a + u32(1)
  right: u32 = a + u32(1)
  dead: u32 = a * u32(2)
  inc(left + right)
}

main: (): i32 = i32_bits_u32(optimized_call(u32(19)) + u32(1))
`

func TestE2ENativeOptIRSelectsVerifiedScalarCall(t *testing.T) {
	requireArm64Host(t)
	var diagnostics []string
	comp := New().WithSource("native_optir_calls.oak", nativeOptIRCallProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			diagnostics = append(diagnostics, d.Message)
		}
	})
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	assertVerifiedOptIRCall(t, diagnostics, model)
	if _, code, abnormal := buildAndRunFrom(t, "native_optir_calls", comp); abnormal || code != 42 {
		t.Fatalf("native OptIR call execution = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2ENativeRV64OptIRSelectsVerifiedScalarCall(t *testing.T) {
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	var diagnostics []string
	comp := New().WithSource("native_rv64_optir_calls.oak", nativeOptIRCallProgram).WithTarget(bare).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			diagnostics = append(diagnostics, d.Message)
		}
	})
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	assertVerifiedOptIRCall(t, diagnostics, model)
	native, err := comp.EmitNative(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	if out := runNativeRV64Bare(t, "native_rv64_optir_calls", native); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("native RV64 OptIR call under QEMU did not exit 42:\n%s", out)
	}
}

func assertVerifiedOptIRCall(t *testing.T, diagnostics []string, model *SemanticModel) {
	t.Helper()
	joined := strings.Join(diagnostics, "\n")
	if !strings.Contains(joined, "optimized_call: optimized OptIR selected") || !strings.Contains(joined, "generic SSA change(s), proven") {
		t.Fatalf("optimized scalar-call candidate was not selected and proven:\n%s", joined)
	}
	if verdict := model.NativeVerdicts["optimized_call"]; verdict.Kind.String() != "proven" || !strings.Contains(verdict.Message, "callee") {
		t.Fatalf("optimized_call verdict = %s (%s)", verdict.Kind, verdict.Message)
	}
}
