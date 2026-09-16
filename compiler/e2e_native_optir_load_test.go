package compiler

import (
	"encoding/binary"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

const nativeOptIRRegionLoadProgram = `
state: u32 = u32(0)

store_then_load: (first: u32, last: u32): u32 {
  state = first
  state = last
  state
}

main: (): i32 = i32_bits_u32(store_then_load(u32(1), u32(42)))
`

func TestE2ENativeOptIRSelectsVerifiedRegionLoadAfterStore(t *testing.T) {
	requireArm64Host(t)
	comp, diagnostics := nativeOptIRRegionLoadCompilation("")
	assertVerifiedOptIRRegionLoad(t, comp, diagnostics)
	if _, code, abnormal := buildAndRunFrom(t, "native_optir_region_load", comp); abnormal || code != 42 {
		t.Fatalf("native OptIR region load execution = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2ENativeRV64OptIRSelectsVerifiedRegionLoadAfterStore(t *testing.T) {
	comp, diagnostics := nativeOptIRRegionLoadCompilation(asm.ArchRV64)
	assertVerifiedOptIRRegionLoad(t, comp, diagnostics)
	native, err := comp.EmitNative(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	if len(native.Object) < 20 || binary.LittleEndian.Uint16(native.Object[18:20]) != 243 {
		t.Fatal("verified OptIR region-load candidate did not produce an EM_RISCV object")
	}
}

func nativeOptIRRegionLoadCompilation(arch string) (Compilation, *[]string) {
	diagnostics := []string{}
	comp := New().WithSource("native_optir_region_load.oak", nativeOptIRRegionLoadProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			diagnostics = append(diagnostics, d.Message)
		}
	})
	if arch == asm.ArchRV64 {
		comp = comp.WithTarget(rv64Linux)
	}
	return comp, &diagnostics
}

func assertVerifiedOptIRRegionLoad(t *testing.T, comp Compilation, diagnostics *[]string) {
	t.Helper()
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	joined := strings.Join(*diagnostics, "\n")
	if !strings.Contains(joined, "store_then_load: optimized OptIR selected") || !strings.Contains(joined, "generic SSA change(s), proven") {
		t.Fatalf("verified OptIR region-load candidate was not selected:\n%s", joined)
	}
	if verdict := model.NativeVerdicts["store_then_load"]; verdict.Kind != asm.VerdictProven {
		t.Fatalf("store_then_load verdict = %s (%s)", verdict.Kind, verdict.Message)
	}
}
