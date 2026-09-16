package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

func TestE2ENativeOptIRMemoryCleanupDeadStores(t *testing.T) {
	requireArm64Host(t)
	comp := checkedNativeOptIRMemoryCleanupDeadStores(t, "")
	if _, code, abnormal := buildAndRunFrom(t, "native_cleanup_dead_stores", comp); abnormal || code != 42 {
		t.Fatalf("store cleanup execution = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2ENativeRV64OptIRMemoryCleanupDeadStores(t *testing.T) {
	comp := checkedNativeOptIRMemoryCleanupDeadStores(t, asm.ArchRV64)
	if output, err := comp.EmitNative(asm.ELF).Get(); err != nil || len(output.Object) == 0 {
		t.Fatalf("store cleanup object emission failed: %v", err)
	}
}

func TestE2ENativeRV64OptIRMemoryCleanupDeadStoresUnderQEMU(t *testing.T) {
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	native, diagnostics := nativeRV64Lower(t, bare, optIRMemoryDeadStoreCleanupProgram)
	assertNativeOptIRMemoryCleanupDeadStoresSelected(t, diagnostics)
	if out := runNativeRV64Bare(t, "native_rv64_cleanup_dead_stores", native); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("store cleanup program did not exit 42:\n%s", out)
	}
}

func checkedNativeOptIRMemoryCleanupDeadStores(t *testing.T, arch string) Compilation {
	t.Helper()
	var diagnostics []string
	comp := New().WithSource("native_cleanup_dead_stores.oak", optIRMemoryDeadStoreCleanupProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
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
	assertNativeOptIRMemoryCleanupDeadStoresSelected(t, diagnostics)
	for _, name := range []string{"after_forwarding", "after_pruning", "keep_read", "keep_branch_read", "keep_effect"} {
		if verdict := model.NativeVerdicts[name]; verdict.Kind != asm.VerdictProven {
			t.Fatalf("%s verdict = %s (%s)", name, verdict.Kind, verdict.Message)
		}
	}
	selected := make(map[string]*asm.Function)
	for _, function := range model.AsmFunctions {
		if function.Signature != nil {
			selected[function.Signature.Name.Value] = function
		}
	}
	for _, test := range []struct {
		name string
		from string
		to   string
	}{
		// Same returned answer, different final global state: retaining the
		// last store remains part of equivalence, not just return-value equality.
		{"after_forwarding", "state = u32(42)", "state = u32(43)"},
		// Making the reader reachable must refute the body that removed the
		// earlier store and its producer together with the unreachable call.
		{"after_pruning", "side == u32(20)", "side == u32(21)"},
	} {
		wrong, err := New().WithSource("wrong_cleanup_stores.oak", strings.Replace(optIRMemoryDeadStoreCleanupProgram, test.from, test.to, 1)).Check().Get()
		if err != nil {
			t.Fatal(err)
		}
		checked := false
		for _, statement := range wrong.Tree.Root.Statements {
			if function, ok := statement.(*ast.FunctionStatement); ok && function.Name.Value == test.name {
				machine := selected[test.name]
				if machine == nil {
					t.Fatalf("missing selected %s body", test.name)
				}
				checked = true
				if verdict := asm.Verify(machine, machine.Signature, function.Body); verdict.Kind != asm.VerdictMismatch {
					t.Fatalf("%s changed source must refute store cleanup: %s (%s)", test.name, verdict.Kind, verdict.Message)
				}
			}
		}
		if !checked {
			t.Fatalf("missing %s source for negative verification", test.name)
		}
	}
	return comp
}

func assertNativeOptIRMemoryCleanupDeadStoresSelected(t *testing.T, diagnostics []string) {
	t.Helper()
	for _, name := range []string{"after_forwarding", "after_pruning", "keep_effect"} {
		found := false
		for _, message := range diagnostics {
			found = found || strings.Contains(message, name+": optimized OptIR selected") && strings.Contains(message, "generic SSA change(s), proven")
		}
		if !found {
			t.Fatalf("proven %s store cleanup candidate was not selected:\n%s", name, strings.Join(diagnostics, "\n"))
		}
	}
}
