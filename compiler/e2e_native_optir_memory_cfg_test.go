package compiler

import (
	"encoding/binary"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
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
