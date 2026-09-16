package compiler

import (
	"encoding/binary"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

const nativeRV64OptIRProgram = `
common: (x: u32): u32 {
  left: u32 = x + u32(1)
  right: u32 = x + u32(1)
  dead: u32 = x * u32(2)
  left + right
}

main: (): i32 = i32_bits_u32(common(u32(20)))
`

func TestE2ENativeRV64SelectsVerifiedOptimizedOptIR(t *testing.T) {
	var diagnostics []string
	comp := New().WithSource("native_rv64_optir.oak", nativeRV64OptIRProgram).WithTarget(rv64Linux).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			diagnostics = append(diagnostics, d.Message)
		}
	})
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	joined := strings.Join(diagnostics, "\n")
	if !strings.Contains(joined, "common: optimized OptIR selected") || !strings.Contains(joined, "generic SSA change(s), proven") {
		t.Fatalf("RV64 optimized SSA candidate was not selected and proven:\n%s", joined)
	}
	if verdict := model.NativeVerdicts["common"]; verdict.Kind.String() != "proven" {
		t.Fatalf("common verdict = %s (%s)", verdict.Kind, verdict.Message)
	}
	native, err := comp.EmitNative(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	if len(native.Object) < 20 || binary.LittleEndian.Uint16(native.Object[18:20]) != 243 {
		t.Fatal("optimized OptIR did not produce an EM_RISCV object")
	}
}

func TestE2ENativeRV64OptimizedOptIRUnderQEMU(t *testing.T) {
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	native, diagnostics := nativeRV64Lower(t, bare, nativeRV64OptIRProgram)
	if joined := strings.Join(diagnostics, "\n"); !strings.Contains(joined, "common: optimized OptIR selected") {
		t.Fatalf("RV64 optimized SSA candidate was not selected:\n%s", joined)
	}
	if out := runNativeRV64Bare(t, "native_rv64_optir", native); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("optimized RV64 OptIR under QEMU did not exit 42:\n%s", out)
	}
}
