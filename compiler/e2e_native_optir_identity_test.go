package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/target"
)

func TestE2ENativeOptIRConstantIdentities(t *testing.T) {
	requireArm64Host(t)
	comp := checkedNativeOptIRConstantIdentities(t, "")
	if _, code, abnormal := buildAndRunFrom(t, "native_identities", comp); abnormal || code != 42 {
		t.Fatalf("identity execution = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2ENativeRV64OptIRConstantIdentities(t *testing.T) {
	comp := checkedNativeOptIRConstantIdentities(t, asm.ArchRV64)
	if output, err := comp.EmitNative(asm.ELF).Get(); err != nil || len(output.Object) == 0 {
		t.Fatalf("identity object emission failed: %v", err)
	}
}

func TestE2ENativeRV64OptIRConstantIdentitiesUnderQEMU(t *testing.T) {
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	native, diagnostics := nativeRV64Lower(t, bare, optIRIdentityProgram)
	assertNativeOptIRConstantIdentitiesSelected(t, diagnostics)
	if out := runNativeRV64Bare(t, "native_rv64_identities", native); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("identity program did not exit 42:\n%s", out)
	}
}

func checkedNativeOptIRConstantIdentities(t *testing.T, arch string) Compilation {
	t.Helper()
	var diagnostics []string
	comp := New().WithSource("native_identities.oak", optIRIdentityProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
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
	assertNativeOptIRConstantIdentitiesSelected(t, diagnostics)
	selected := make(map[string]*asm.Function)
	for _, function := range model.AsmFunctions {
		if function.Signature != nil {
			selected[function.Signature.Name.Value] = function
		}
	}
	for _, name := range []string{"annihilate", "subtract_self", "ones", "reflexive_branch", "keep_effect", "zero_loop", "distinct_calls"} {
		if verdict := model.NativeVerdicts[name]; verdict.Kind != asm.VerdictProven {
			t.Fatalf("%s verdict = %s (%s)", name, verdict.Kind, verdict.Message)
		}
	}
	for _, name := range []string{"annihilate", "reflexive_branch", "zero_loop"} {
		if selected[name] == nil {
			t.Fatalf("missing selected %s body", name)
		}
		metrics := nativegen.Metrics(selected[name])
		if metrics.Multiplies != 0 || metrics.Loops != 0 || metrics.Stores != 0 {
			t.Fatalf("%s retained identity work or dead loop stores: %+v", name, metrics)
		}
	}
	for _, test := range []struct{ name, from, to string }{
		{"annihilate", "value * u32(0)", "value * u32(1)"},
		{"reflexive_branch", "value <= value", "value < value"},
		{"keep_effect", "touch(value) * u32(0)", "u32(0)"},
		{"zero_loop", "n ^ n", "n ^ u32(0)"},
	} {
		wrong, err := New().WithSource("wrong_identities.oak", strings.Replace(optIRIdentityProgram, test.from, test.to, 1)).Check().Get()
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
				if verdict := asm.Verify(machine, machine.Signature, function.Body); verdict.Kind == asm.VerdictProven {
					t.Fatalf("changed source incorrectly proved against %s identity body", test.name)
				}
			}
		}
		if !checked {
			t.Fatalf("missing %s source for negative verification", test.name)
		}
	}
	return comp
}

func assertNativeOptIRConstantIdentitiesSelected(t *testing.T, diagnostics []string) {
	t.Helper()
	for _, name := range []string{"annihilate", "reflexive_branch", "keep_effect", "zero_loop"} {
		found := false
		for _, message := range diagnostics {
			found = found || strings.Contains(message, name+": optimized OptIR selected") && strings.Contains(message, "generic SSA change(s), proven")
		}
		if !found {
			t.Fatalf("proven %s identity candidate was not selected:\n%s", name, strings.Join(diagnostics, "\n"))
		}
	}
}
