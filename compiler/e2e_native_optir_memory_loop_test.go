package compiler

import (
	"encoding/binary"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

const nativeOptIRMemoryLoopProgram = `
state: u32 = u32(0)

loop_store: (n: u32): u32 {
  initial: u32 = state
  i: u32 = u32(0)
  while i < n {
    dead1: u32 = i + u32(1)
    dead2: u32 = i + u32(2)
    dead3: u32 = i + u32(3)
    dead4: u32 = i + u32(4)
    dead5: u32 = i + u32(5)
    dead6: u32 = i + u32(6)
    dead7: u32 = i + u32(7)
    dead8: u32 = i + u32(8)
    dead9: u32 = i + u32(9)
    dead10: u32 = i + u32(10)
    dead11: u32 = i + u32(11)
    dead12: u32 = i + u32(12)
    state = state + u32(1)
    i = i + u32(1)
  }
  state
}

main: (): i32 = loop_store(u32(4)) == u32(4) ? i32(42) | i32(1)
`

func TestE2ENativeOptIRSelectsVerifiedRegionMemoryLoop(t *testing.T) {
	requireArm64Host(t)
	comp, diagnostics := nativeOptIRMemoryLoopCompilation("")
	assertVerifiedOptIRMemoryLoop(t, comp, diagnostics)
	if _, code, abnormal := buildAndRunFrom(t, "native_optir_memory_loop", comp); abnormal || code != 42 {
		t.Fatalf("native region-memory loop execution = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2ENativeRV64OptIRSelectsVerifiedRegionMemoryLoop(t *testing.T) {
	comp, diagnostics := nativeOptIRMemoryLoopCompilation(asm.ArchRV64)
	assertVerifiedOptIRMemoryLoop(t, comp, diagnostics)
	native, err := comp.EmitNative(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	if len(native.Object) < 20 || binary.LittleEndian.Uint16(native.Object[18:20]) != 243 {
		t.Fatal("verified region-memory loop candidate did not produce an EM_RISCV object")
	}
}

func TestE2ENativeRV64OptIRMemoryLoopPromotionUnderQEMU(t *testing.T) {
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	native, diagnostics := nativeRV64Lower(t, bare, nativeOptIRMemoryLoopProgram)
	joined := strings.Join(diagnostics, "\n")
	if !strings.Contains(joined, "loop_store: optimized OptIR selected") || !strings.Contains(joined, "generic SSA change(s), proven") {
		t.Fatalf("verified RV64 loop-promotion candidate was not selected:\n%s", joined)
	}
	if out := runNativeRV64Bare(t, "native_rv64_optir_memory_loop_promotion", native); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("optimized RV64 loop-promotion program did not exit 42:\n%s", out)
	}
}

func nativeOptIRMemoryLoopCompilation(arch string) (Compilation, *[]string) {
	diagnostics := []string{}
	comp := New().WithSource("native_optir_memory_loop.oak", nativeOptIRMemoryLoopProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			diagnostics = append(diagnostics, d.Message)
		}
	})
	if arch == asm.ArchRV64 {
		comp = comp.WithTarget(rv64Linux)
	}
	return comp, &diagnostics
}

func assertVerifiedOptIRMemoryLoop(t *testing.T, comp Compilation, diagnostics *[]string) {
	t.Helper()
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	joined := strings.Join(*diagnostics, "\n")
	if !strings.Contains(joined, "loop_store: optimized OptIR selected") || !strings.Contains(joined, "generic SSA change(s), proven") {
		projected, projectionErr := comp.OptIR().Get()
		t.Fatalf("verified region-memory loop candidate was not selected:\n%s\noptimization report: %+v\nOptIR refusals: %+v (err=%v)", joined, model.Optimizations, projected.Refusals, projectionErr)
	}
	projected, err := comp.OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	loop, ok := optIRFunction(projected, "loop_store")
	if !ok {
		t.Fatalf("loop_store was not projected: %+v", projected.Refusals)
	}
	if loop.RegionLoadForwarding.Changes() != 2 {
		t.Fatalf("loop-carried memory promotion = %+v", loop.RegionLoadForwarding)
	}
	if stores, loads := countOptIRMemoryOperations(loop.ForwardedLoads); stores != 1 || loads != 1 {
		t.Fatalf("post-loop-promotion operations = stores %d, loads %d", stores, loads)
	}
	verdict := model.NativeVerdicts["loop_store"]
	if verdict.Kind != asm.VerdictProven || !strings.Contains(verdict.Message, "package state it writes (state)") {
		t.Fatalf("loop_store verdict = %s (%s)", verdict.Kind, verdict.Message)
	}
}
