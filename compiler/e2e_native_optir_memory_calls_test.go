package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
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

const nativeOptIRMemoryRefCallProgram = `
state: u32 = u32(0)

read_plus: (value: u32): u32 = state + value

observe_then_overwrite: (): u32 {
  state = u32(19)
  observed: u32 = read_plus(u32(1))
  state = u32(22)
  observed + state
}

main: (): i32 = i32_bits_u32(observe_then_overwrite())
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

func TestE2ENativeOptIRSelectsVerifiedRefCallRegionMemory(t *testing.T) {
	requireArm64Host(t)
	comp, diagnostics := nativeOptIRMemoryRefCallCompilation("")
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	assertVerifiedOptIRMemoryRefCall(t, diagnostics, model)
	if _, code, abnormal := buildAndRunFrom(t, "native_optir_memory_ref_calls", comp); abnormal || code != 42 {
		t.Fatalf("native Ref call/region-memory execution = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2ENativeRV64OptIRSelectsVerifiedRefCallRegionMemory(t *testing.T) {
	comp, diagnostics := nativeOptIRMemoryRefCallCompilation(asm.ArchRV64)
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	assertVerifiedOptIRMemoryRefCall(t, diagnostics, model)
	native, err := comp.EmitNative(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	if len(native.Object) == 0 {
		t.Fatal("RV64 Ref call/region-memory candidate produced no object")
	}
}

func TestE2ENativeRV64OptIRRefCallRegionMemoryUnderQEMU(t *testing.T) {
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	native, diagnostics := nativeRV64Lower(t, bare, nativeOptIRMemoryRefCallProgram)
	joined := strings.Join(diagnostics, "\n")
	if !strings.Contains(joined, "observe_then_overwrite: optimized OptIR selected") {
		t.Fatalf("verified RV64 Ref call/region-memory candidate was not selected:\n%s", joined)
	}
	if out := runNativeRV64Bare(t, "native_rv64_optir_memory_ref_calls", native); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("optimized RV64 Ref call/region-memory did not exit 42:\n%s", out)
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

func nativeOptIRMemoryRefCallCompilation(arch string) (Compilation, *[]string) {
	diagnostics := []string{}
	comp := New().WithSource("native_optir_memory_ref_calls.oak", nativeOptIRMemoryRefCallProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
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

func assertVerifiedOptIRMemoryRefCall(t *testing.T, diagnostics *[]string, model *SemanticModel) {
	t.Helper()
	joined := strings.Join(*diagnostics, "\n")
	if !strings.Contains(joined, "observe_then_overwrite: optimized OptIR selected") || !strings.Contains(joined, "generic SSA change(s), proven") {
		t.Fatalf("verified Ref call/region-memory candidate was not selected:\n%s", joined)
	}
	verdict := model.NativeVerdicts["observe_then_overwrite"]
	if verdict.Kind != asm.VerdictProven || !strings.Contains(verdict.Message, "callees taken at their Oak bodies: read_plus") || !strings.Contains(verdict.Message, "package state it writes (state)") {
		t.Fatalf("observe_then_overwrite verdict = %s (%s)", verdict.Kind, verdict.Message)
	}
}
