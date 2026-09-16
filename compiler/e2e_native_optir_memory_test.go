package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

const nativeOptIRMemoryProgram = `
state: u32 = u32(0)

overwrite: (first: u32, last: u32): u32 {
  state = first
  state = last
  last
}

main: (): i32 = i32_bits_u32(overwrite(u32(1), u32(42)))
`

const nativeOptIRLoadForwardProgram = `
state: u32 = u32(0)

read_twice: (value: u32): u32 {
  state = value
  state + state
}

main: (): i32 = i32_bits_u32(read_twice(u32(21)))
`

func TestE2ENativeOptIRSelectsVerifiedRegionDSE(t *testing.T) {
	requireArm64Host(t)
	comp, diagnostics := nativeOptIRMemoryCompilation("")
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	assertVerifiedOptIRMemory(t, diagnostics, model)
	if _, code, abnormal := buildAndRunFrom(t, "native_optir_memory", comp); abnormal || code != 42 {
		t.Fatalf("native region-DSE execution = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2ENativeRV64OptIRSelectsVerifiedRegionDSE(t *testing.T) {
	comp, diagnostics := nativeOptIRMemoryCompilation(asm.ArchRV64)
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	assertVerifiedOptIRMemory(t, diagnostics, model)
	native, err := comp.EmitNative(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	if len(native.Object) == 0 {
		t.Fatal("RV64 region-DSE candidate produced no object")
	}
}

func TestE2ENativeRV64OptIRRegionDSEUnderQEMU(t *testing.T) {
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	native, diagnostics := nativeRV64Lower(t, bare, nativeOptIRMemoryProgram)
	if joined := strings.Join(diagnostics, "\n"); !strings.Contains(joined, "overwrite: optimized OptIR selected") {
		t.Fatalf("verified RV64 region DSE candidate was not selected:\n%s", joined)
	}
	if out := runNativeRV64Bare(t, "native_rv64_optir_memory", native); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("optimized RV64 region DSE did not exit 42:\n%s", out)
	}
}

func TestE2ENativeOptIRSelectsVerifiedRegionLoadForwarding(t *testing.T) {
	requireArm64Host(t)
	diagnostics := []string{}
	comp := New().WithSource("native_optir_load_forward.oak", nativeOptIRLoadForwardProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			diagnostics = append(diagnostics, d.Message)
		}
	})
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	joined := strings.Join(diagnostics, "\n")
	if !strings.Contains(joined, "read_twice: optimized OptIR selected") || !strings.Contains(joined, "2 generic SSA change(s), proven") {
		t.Fatalf("verified region-load forwarding candidate was not selected:\n%s", joined)
	}
	if verdict := model.NativeVerdicts["read_twice"]; verdict.Kind.String() != "proven" || !strings.Contains(verdict.Message, "package state it writes (state)") {
		t.Fatalf("read_twice verdict = %s (%s)", verdict.Kind, verdict.Message)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_optir_load_forward", comp); abnormal || code != 42 {
		t.Fatalf("native region-load forwarding execution = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2ENativeRV64OptIRRegionLoadForwardingUnderQEMU(t *testing.T) {
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	native, diagnostics := nativeRV64Lower(t, bare, nativeOptIRLoadForwardProgram)
	if joined := strings.Join(diagnostics, "\n"); !strings.Contains(joined, "read_twice: optimized OptIR selected") || !strings.Contains(joined, "2 generic SSA change(s), proven") {
		t.Fatalf("verified RV64 region-load forwarding candidate was not selected:\n%s", joined)
	}
	if out := runNativeRV64Bare(t, "native_rv64_optir_load_forward", native); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("optimized RV64 region-load forwarding did not exit 42:\n%s", out)
	}
}

func nativeOptIRMemoryCompilation(arch string) (Compilation, *[]string) {
	diagnostics := []string{}
	comp := New().WithSource("native_optir_memory.oak", nativeOptIRMemoryProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			diagnostics = append(diagnostics, d.Message)
		}
	})
	if arch == asm.ArchRV64 {
		comp = comp.WithTarget(rv64Linux)
	}
	return comp, &diagnostics
}

func assertVerifiedOptIRMemory(t *testing.T, diagnostics *[]string, model *SemanticModel) {
	t.Helper()
	joined := strings.Join(*diagnostics, "\n")
	if !strings.Contains(joined, "overwrite: optimized OptIR selected") || !strings.Contains(joined, "generic SSA change(s), proven") {
		t.Fatalf("verified region DSE candidate was not selected:\n%s", joined)
	}
	verdict := model.NativeVerdicts["overwrite"]
	if verdict.Kind.String() != "proven" || !strings.Contains(verdict.Message, "package state it writes (state)") {
		t.Fatalf("overwrite verdict = %s (%s)", verdict.Kind, verdict.Message)
	}
}
