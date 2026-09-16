package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

func TestE2ENativeOptIRMemoryCleanup(t *testing.T) {
	requireArm64Host(t)
	comp := checkedNativeOptIRMemoryCleanup(t, "")
	if _, code, abnormal := buildAndRunFrom(t, "native_optir_memory_cleanup", comp); abnormal || code != 42 {
		t.Fatalf("post-memory cleanup execution = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2ENativeRV64OptIRMemoryCleanup(t *testing.T) {
	comp := checkedNativeOptIRMemoryCleanup(t, asm.ArchRV64)
	if output, err := comp.EmitNative(asm.ELF).Get(); err != nil || len(output.Object) == 0 {
		t.Fatalf("post-memory cleanup object emission failed: %v", err)
	}
}

func TestE2ENativeRV64OptIRMemoryCleanupUnderQEMU(t *testing.T) {
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	native, diagnostics := nativeRV64Lower(t, bare, optIRMemoryCleanupProgram)
	assertNativeOptIRMemoryCleanupSelected(t, diagnostics)
	if out := runNativeRV64Bare(t, "native_rv64_optir_memory_cleanup", native); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("post-memory cleanup program did not exit 42:\n%s", out)
	}
}

func checkedNativeOptIRMemoryCleanup(t *testing.T, arch string) Compilation {
	t.Helper()
	var diagnostics []string
	comp := New().WithSource("native_memory_cleanup.oak", optIRMemoryCleanupProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			diagnostics = append(diagnostics, d.Message)
		}
	})
	if arch == asm.ArchRV64 {
		comp = comp.WithTarget(rv64Linux)
	}
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	assertNativeOptIRMemoryCleanupSelected(t, diagnostics)
	for _, name := range []string{"fold_memory", "wrap_memory", "memory_free"} {
		if verdict := model.NativeVerdicts[name]; verdict.Kind != asm.VerdictProven {
			t.Fatalf("%s verdict = %s (%s)", name, verdict.Kind, verdict.Message)
		}
	}
	projected, err := comp.OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	fold, ok := optIRFunction(projected, "fold_memory")
	if !ok || fold.MemoryCleanup.Changes() == 0 || len(fold.MemoryCleanup.CFG.Blocks) != 1 {
		t.Fatalf("native compiler did not expose cleaned final CFG: %+v", fold.MemoryCleanup)
	}
	var selected *asm.Function
	for _, function := range model.AsmFunctions {
		if function.Signature != nil && function.Signature.Name.Value == "fold_memory" {
			selected = function
		}
	}
	if selected == nil || selected.Globals["ghost"].Type != "u32" {
		t.Fatal("selected body lost the source-only global's verification declaration")
	}
	_, relocations, err := asm.EncodeFunction(selected)
	if err != nil {
		t.Fatal(err)
	}
	for _, relocation := range relocations {
		if strings.Contains(relocation.Symbol, "ghost") || strings.Contains(relocation.Symbol, "poison") {
			t.Fatalf("removed memory/call path still has a machine relocation: %+v", relocation)
		}
	}
	wrong, err := New().WithSource("wrong_cleanup.oak", strings.Replace(optIRMemoryCleanupProgram, "state == u32(20)", "state == u32(21)", 1)).Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	checkedWrong := false
	for _, statement := range wrong.Tree.Root.Statements {
		if function, ok := statement.(*ast.FunctionStatement); ok && function.Name.Value == "fold_memory" {
			checkedWrong = true
			if verdict := asm.Verify(selected, selected.Signature, function.Body); verdict.Kind != asm.VerdictMismatch {
				t.Fatalf("reachable ghost write must refute the cleaned body: %s (%s)", verdict.Kind, verdict.Message)
			}
		}
	}
	if !checkedWrong {
		t.Fatal("missing changed source body for the negative verification check")
	}
	return comp
}

func assertNativeOptIRMemoryCleanupSelected(t *testing.T, diagnostics []string) {
	t.Helper()
	for _, message := range diagnostics {
		if strings.Contains(message, "fold_memory: optimized OptIR selected") && strings.Contains(message, "generic SSA change(s), proven") {
			return
		}
	}
	t.Fatalf("proven post-memory cleanup candidate was not selected:\n%s", strings.Join(diagnostics, "\n"))
}
