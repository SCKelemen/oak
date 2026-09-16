package compiler

import (
	"encoding/binary"
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

func TestE2ENativeOptIRRegionMemoryComposesWithSpills(t *testing.T) {
	requireArm64Host(t)
	comp, diagnostics := nativeOptIRMemorySpillCompilation("")
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	assertVerifiedOptIRMemorySpill(t, diagnostics, model)
	if _, code, abnormal := buildAndRunFrom(t, "native_optir_memory_spill", comp); abnormal || code != 42 {
		t.Fatalf("native region-memory/spill execution = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2ENativeRV64OptIRRegionMemoryComposesWithSpills(t *testing.T) {
	comp, diagnostics := nativeOptIRMemorySpillCompilation(asm.ArchRV64)
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	assertVerifiedOptIRMemorySpill(t, diagnostics, model)
	native, err := comp.EmitNative(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	if len(native.Object) < 20 || binary.LittleEndian.Uint16(native.Object[18:20]) != 243 {
		t.Fatal("verified region-memory/spill candidate did not produce an EM_RISCV object")
	}
}

func nativeOptIRMemorySpillCompilation(arch string) (Compilation, *[]string) {
	const values = 20
	var source strings.Builder
	source.WriteString("state: u32 = u32(0)\n\npressure_store: (x: u32): u32 = {\n")
	for index := 1; index <= values; index++ {
		fmt.Fprintf(&source, "  v%d: u32 = x + u32(%d)\n", index, index)
		fmt.Fprintf(&source, "  d%d: u32 = x + u32(%d)\n", index, index)
	}
	source.WriteString("  total: u32 = ")
	for index := 1; index <= values; index++ {
		if index > 1 {
			source.WriteString(" + ")
		}
		fmt.Fprintf(&source, "v%d + d%d", index, index)
	}
	source.WriteString("\n  state = total\n  state\n}\n\nmain: (): i32 = pressure_store(u32(1)) == u32(460) ? i32(42) | i32(1)\n")

	diagnostics := []string{}
	comp := New().WithSource("native_optir_memory_spill.oak", source.String()).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			diagnostics = append(diagnostics, d.Message)
		}
	})
	if arch == asm.ArchRV64 {
		comp = comp.WithTarget(rv64Linux)
	}
	return comp, &diagnostics
}

func assertVerifiedOptIRMemorySpill(t *testing.T, diagnostics *[]string, model *SemanticModel) {
	t.Helper()
	joined := strings.Join(*diagnostics, "\n")
	if !strings.Contains(joined, "pressure_store: optimized OptIR selected") || !strings.Contains(joined, "generic SSA change(s), proven") {
		t.Fatalf("verified region-memory/spill candidate was not selected:\n%s", joined)
	}
	verdict := model.NativeVerdicts["pressure_store"]
	if verdict.Kind != asm.VerdictProven || !strings.Contains(verdict.Message, "package state it writes (state)") {
		t.Fatalf("pressure_store verdict = %s (%s)", verdict.Kind, verdict.Message)
	}
	for _, function := range model.AsmFunctions {
		if function.Name == "pressure_store" {
			if function.Frame == 0 {
				t.Fatal("selected call-free region-memory body has no spill frame")
			}
			return
		}
	}
	t.Fatal("selected pressure_store body is absent from the semantic model")
}
