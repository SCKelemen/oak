package compiler

import (
	"encoding/binary"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

const nativeOptIRMemoryCFGProgram = `
state: u32 = u32(0)

guarded_overwrite: (flag: Bool, first: u32, last: u32): u32 {
  flag ? {
    state = first
    state = last
  } | {
    state = u32(7)
  }
  state
}

main: (): i32 {
  true_path: Bool = guarded_overwrite(true, u32(1), u32(42)) == u32(42)
  false_path: Bool = guarded_overwrite(false, u32(1), u32(42)) == u32(7)
  true_path && false_path ? i32(42) | i32(1)
}
`

const nativeOptIRMemoryAvailableLoadProgram = `
state: u32 = u32(0)

choose_loaded: (flag: Bool, value: u32): u32 {
  flag ? {
    state = value
  } | {
    previous: u32 = state
  }
  state
}

main: (): i32 {
  true_path: Bool = choose_loaded(true, u32(42)) == u32(42)
  false_path: Bool = choose_loaded(false, u32(1)) == u32(42)
  true_path && false_path ? i32(42) | i32(1)
}
`

func TestE2ENativeOptIRSelectsVerifiedRegionDSEAcrossBranch(t *testing.T) {
	requireArm64Host(t)
	comp, diagnostics := nativeOptIRMemoryCFGCompilation("")
	assertVerifiedOptIRMemoryCFG(t, comp, diagnostics)
	if _, code, abnormal := buildAndRunFrom(t, "native_optir_memory_cfg", comp); abnormal || code != 42 {
		t.Fatalf("native acyclic region-DSE execution = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2ENativeRV64OptIRSelectsVerifiedRegionDSEAcrossBranch(t *testing.T) {
	comp, diagnostics := nativeOptIRMemoryCFGCompilation(asm.ArchRV64)
	assertVerifiedOptIRMemoryCFG(t, comp, diagnostics)
	native, err := comp.EmitNative(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	if len(native.Object) < 20 || binary.LittleEndian.Uint16(native.Object[18:20]) != 243 {
		t.Fatal("verified acyclic region-DSE candidate did not produce an EM_RISCV object")
	}
}

func TestE2ENativeRV64OptIRMemoryPhiUnderQEMU(t *testing.T) {
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	native, diagnostics := nativeRV64Lower(t, bare, nativeOptIRMemoryCFGProgram)
	joined := strings.Join(diagnostics, "\n")
	if !strings.Contains(joined, "guarded_overwrite: optimized OptIR selected") || !strings.Contains(joined, "generic SSA change(s), proven") {
		t.Fatalf("verified RV64 memory-phi candidate was not selected:\n%s", joined)
	}
	if out := runNativeRV64Bare(t, "native_rv64_optir_memory_phi", native); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("optimized RV64 memory-phi program did not exit 42:\n%s", out)
	}
}

func TestE2ENativeOptIRMemoryPhiReusesAvailableLoad(t *testing.T) {
	requireArm64Host(t)
	diagnostics := []string{}
	comp := New().WithSource("native_optir_memory_available_load.oak", nativeOptIRMemoryAvailableLoadProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			diagnostics = append(diagnostics, d.Message)
		}
	})
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	assertAvailableLoadMemoryPhiSelected(t, diagnostics)
	if verdict := model.NativeVerdicts["choose_loaded"]; verdict.Kind != asm.VerdictProven {
		t.Fatalf("choose_loaded verdict = %s (%s)", verdict.Kind, verdict.Message)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_optir_memory_available_load", comp); abnormal || code != 42 {
		t.Fatalf("native available-load memory-phi execution = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2ENativeRV64OptIRMemoryPhiReusesAvailableLoadUnderQEMU(t *testing.T) {
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	native, diagnostics := nativeRV64Lower(t, bare, nativeOptIRMemoryAvailableLoadProgram)
	assertAvailableLoadMemoryPhiSelected(t, diagnostics)
	if out := runNativeRV64Bare(t, "native_rv64_optir_memory_available_load", native); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("optimized RV64 available-load memory-phi program did not exit 42:\n%s", out)
	}
}

func assertAvailableLoadMemoryPhiSelected(t *testing.T, diagnostics []string) {
	t.Helper()
	joined := strings.Join(diagnostics, "\n")
	if !strings.Contains(joined, "choose_loaded: optimized OptIR selected") || !strings.Contains(joined, "generic SSA change(s), proven") {
		t.Fatalf("verified available-load memory-phi candidate was not selected:\n%s", joined)
	}
}

func nativeOptIRMemoryCFGCompilation(arch string) (Compilation, *[]string) {
	diagnostics := []string{}
	comp := New().WithSource("native_optir_memory_cfg.oak", nativeOptIRMemoryCFGProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			diagnostics = append(diagnostics, d.Message)
		}
	})
	if arch == asm.ArchRV64 {
		comp = comp.WithTarget(rv64Linux)
	}
	return comp, &diagnostics
}

func assertVerifiedOptIRMemoryCFG(t *testing.T, comp Compilation, diagnostics *[]string) {
	t.Helper()
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	joined := strings.Join(*diagnostics, "\n")
	if !strings.Contains(joined, "guarded_overwrite: optimized OptIR selected") || !strings.Contains(joined, "generic SSA change(s), proven") {
		t.Fatalf("verified acyclic region-DSE candidate was not selected:\n%s", joined)
	}
	if verdict := model.NativeVerdicts["guarded_overwrite"]; verdict.Kind != asm.VerdictProven {
		t.Fatalf("guarded_overwrite verdict = %s (%s)", verdict.Kind, verdict.Message)
	}
}
