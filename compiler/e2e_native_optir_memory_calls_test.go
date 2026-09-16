package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

const nativeOptIRMemoryCallProgram = `
state: u32 = u32(0)

inc: (value: u32): u32 = value + u32(1)

call_overwrite: (first: u32, last: u32): u32 {
  state = first
  value: u32 = inc(last)
  state = value
  value
}

main: (): i32 = i32_bits_u32(call_overwrite(u32(1), u32(41)))
`

func TestE2ENativeOptIRSelectsVerifiedNoModRefCallRegionDSE(t *testing.T) {
	requireArm64Host(t)
	comp, diagnostics := nativeOptIRMemoryCallCompilation("")
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	assertVerifiedOptIRMemoryCall(t, diagnostics, model)
	if _, code, abnormal := buildAndRunFrom(t, "native_optir_memory_calls", comp); abnormal || code != 42 {
		t.Fatalf("native no-ModRef call/region-DSE execution = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2ENativeRV64OptIRSelectsVerifiedNoModRefCallRegionDSE(t *testing.T) {
	comp, diagnostics := nativeOptIRMemoryCallCompilation(asm.ArchRV64)
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	assertVerifiedOptIRMemoryCall(t, diagnostics, model)
	native, err := comp.EmitNative(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	if len(native.Object) == 0 {
		t.Fatal("RV64 no-ModRef call/region-DSE candidate produced no object")
	}
}

func nativeOptIRMemoryCallCompilation(arch string) (Compilation, *[]string) {
	diagnostics := []string{}
	comp := New().WithSource("native_optir_memory_calls.oak", nativeOptIRMemoryCallProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			diagnostics = append(diagnostics, d.Message)
		}
	})
	if arch == asm.ArchRV64 {
		comp = comp.WithTarget(rv64Linux)
	}
	return comp, &diagnostics
}

func assertVerifiedOptIRMemoryCall(t *testing.T, diagnostics *[]string, model *SemanticModel) {
	t.Helper()
	joined := strings.Join(*diagnostics, "\n")
	if !strings.Contains(joined, "call_overwrite: optimized OptIR selected") || !strings.Contains(joined, "generic SSA change(s), proven") {
		t.Fatalf("verified no-ModRef call/region-DSE candidate was not selected:\n%s", joined)
	}
	verdict := model.NativeVerdicts["call_overwrite"]
	if verdict.Kind != asm.VerdictProven || !strings.Contains(verdict.Message, "callees taken at their Oak bodies: inc") || !strings.Contains(verdict.Message, "package state it writes (state)") {
		t.Fatalf("call_overwrite verdict = %s (%s)", verdict.Kind, verdict.Message)
	}
}
