package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/machine"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/target"
)

func TestE2ENativeOptIRMemoryCleanupLICM(t *testing.T) {
	requireArm64Host(t)
	comp := checkedNativeOptIRMemoryCleanupLICM(t, "")
	if _, code, abnormal := buildAndRunFrom(t, "native_memory_cleanup_licm", comp); abnormal || code != 42 {
		t.Fatalf("post-memory LICM execution = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2ENativeRV64OptIRMemoryCleanupLICM(t *testing.T) {
	comp := checkedNativeOptIRMemoryCleanupLICM(t, asm.ArchRV64)
	if output, err := comp.EmitNative(asm.ELF).Get(); err != nil || len(output.Object) == 0 {
		t.Fatalf("post-memory LICM object emission failed: %v", err)
	}
}

func TestE2ENativeRV64OptIRMemoryCleanupLICMUnderQEMU(t *testing.T) {
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	native, diagnostics := nativeRV64Lower(t, bare, optIRMemoryLICMProgram)
	assertNativeOptIRMemoryCleanupLICMSelected(t, diagnostics)
	if out := runNativeRV64Bare(t, "native_rv64_memory_cleanup_licm", native); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("post-memory LICM program did not exit 42:\n%s", out)
	}
}

func checkedNativeOptIRMemoryCleanupLICM(t *testing.T, arch string) Compilation {
	t.Helper()
	var diagnostics []string
	comp := New().WithSource("native_memory_cleanup_licm.oak", optIRMemoryLICMProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
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
	// The existing ARM64 bottom-tested candidate is cheaper on this tiny
	// loop. Keep normal cost selection; validate the SSA candidate explicitly
	// below on both targets. RV64 currently selects it in normal search too.
	if arch == asm.ArchRV64 {
		assertNativeOptIRMemoryCleanupLICMSelected(t, diagnostics)
	}
	for _, name := range []string{"sum_cap", "keep_variant"} {
		if verdict := model.NativeVerdicts[name]; verdict.Kind != asm.VerdictProven {
			t.Fatalf("%s verdict = %s (%s)", name, verdict.Kind, verdict.Message)
		}
	}
	functions := make(map[string]*ast.FunctionStatement)
	symbols := map[string]bool{"cap": true}
	for _, statement := range model.Tree.Root.Statements {
		if function, ok := statement.(*ast.FunctionStatement); ok {
			functions[function.Name.Value] = function
			symbols[function.Name.Value] = true
		}
	}
	source := functions["sum_cap"]
	if source == nil {
		t.Fatal("missing sum_cap body")
	}
	constants := constantGlobals(model.Tree.Root, model.TypeChecker)
	globals, _, _ := addressableGlobals(model.Tree.Root, model.TypeChecker, constants, nil)
	planner := newOptIRCallEffectPlanner(model.Tree.Root, model.TypeChecker, checkedOptIRGlobals(model.Tree.Root, model.TypeChecker))
	plan := nativeOptIRCandidate(source, planner, model.TypeChecker, globals)
	if plan.cfg == nil || plan.changes == 0 {
		t.Fatal("production planner did not offer a post-memory LICM candidate")
	}
	lane := nativegen.Lane{Arch: arch, Globals: globals, UseOptIR: true, Reallocate: true}
	applyNativeOptIRCandidate(&lane, plan)
	candidate, err := nativegen.CompileFor(lane, source, functions, nil, nil, constants, model.TypeChecker)
	if err != nil {
		t.Fatal(err)
	}
	if findings := asm.Check(candidate, source, symbols); len(findings) != 0 {
		t.Fatalf("SSA candidate failed seam admission: %v", findings)
	}
	if verdict := asm.Verify(candidate, source, source.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("SSA candidate was not proven: %s (%s)", verdict.Kind, verdict.Message)
	}
	if code, _, err := asm.EncodeFunction(candidate); err != nil || len(code) == 0 {
		t.Fatalf("SSA candidate encoding failed: %v", err)
	}
	metrics := nativegen.Metrics(candidate)
	if metrics.Multiplies != 1 || metrics.LoopLoads != 0 {
		t.Fatalf("expected one multiplication and no loop loads: %+v", metrics)
	}
	loops, err := machine.LoopShapes(candidate)
	if err != nil || len(loops) != 1 {
		t.Fatalf("expected one native loop: %+v, %v", loops, err)
	}
	for _, block := range loops[0].Loop.Blocks {
		for _, instruction := range block.Instrs {
			switch instruction.Asm.Mnemonic {
			case "mul", "mulw", "madd", "umaddl", "smaddl", "umull", "smull":
				t.Fatalf("multiplication remains in the native loop: %+v", instruction.Asm)
			}
		}
	}
	// A different factor must never receive a proof, even if concrete samples
	// use cap=0 and cannot expose the mismatch. An added offset also supplies
	// a counterexample on those samples, so it must get a definite mismatch.
	for _, test := range []struct {
		replacement string
		mismatch    bool
	}{
		{"cap * u32(4)", false},
		{"cap * u32(4) + u32(1)", true},
	} {
		wrong, err := New().WithSource("wrong_memory_licm.oak", strings.Replace(optIRMemoryLICMProgram, "cap * u32(3)", test.replacement, 1)).Check().Get()
		if err != nil {
			t.Fatal(err)
		}
		checked := false
		for _, statement := range wrong.Tree.Root.Statements {
			if function, ok := statement.(*ast.FunctionStatement); ok && function.Name.Value == "sum_cap" {
				checked = true
				verdict := asm.Verify(candidate, source, function.Body)
				if verdict.Kind == asm.VerdictProven || test.mismatch && verdict.Kind != asm.VerdictMismatch {
					t.Fatalf("changed loop arithmetic (%s) accepted: %s (%s)", test.replacement, verdict.Kind, verdict.Message)
				}
			}
		}
		if !checked {
			t.Fatal("missing source for negative verification")
		}
	}
	return comp
}

func assertNativeOptIRMemoryCleanupLICMSelected(t *testing.T, diagnostics []string) {
	t.Helper()
	for _, message := range diagnostics {
		if strings.Contains(message, "sum_cap: optimized OptIR selected") && strings.Contains(message, "generic SSA change(s), proven") {
			return
		}
	}
	t.Fatalf("proven post-memory LICM candidate was not selected:\n%s", strings.Join(diagnostics, "\n"))
}
