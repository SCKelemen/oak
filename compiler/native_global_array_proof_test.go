package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/target"
)

// Pin the actual compiler-to-verifier type-text boundary, not a hand-written
// legacy descriptor. Native execution remains required by the existing E2E test.
func TestNativeGlobalArrayProofCanonicalBoundary(t *testing.T) {
	t.Setenv("OAK_VERIFY_CACHE", "0")
	t.Setenv("OAK_OPT_SKIP", "")
	t.Setenv("OAK_NATIVE_ONLY", "")
	t.Setenv("OAK_VERIFY_BUDGET", "")
	comp := New().WithSource("global_array.oak", nativeGlobalArrayProgram).
		WithTarget(target.Target{OS: target.OSLinux, Arch: target.ArchArm64}).WithNativeBodies().WithNativeAsm()
	comp.options.InlineHelpers = true
	tree, err := comp.Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	typeText := ""
	for _, statement := range tree.Root.Statements {
		if decl, ok := statement.(*ast.VariableDeclaration); ok && decl.Name.Value == "buf" {
			typeText = decl.Type.String()
		}
	}
	if typeText == "" {
		t.Fatal("source array declaration missing")
	}
	model, err := comp.SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, name := range []string{"write_byte", "write_two", "sum_buf"} {
		verdict, ok := model.NativeVerdicts[name]
		if !ok || verdict.Kind != asm.VerdictProven {
			t.Errorf("%s must prove: present=%v kind=%s message=%s", name, ok, verdict.Kind, verdict.Message)
		}
		found := false
		for _, fn := range model.AsmFunctions {
			if fn.Name == name {
				if global, ok := fn.Globals["buf"]; ok {
					found = true
					if global.Type != typeText || global.Size != 64 || !global.Aggregate {
						t.Errorf("%s global descriptor %+v does not preserve AST.String type %q and 64-byte allocation", name, global, typeText)
					}
				}
			}
		}
		if !found {
			t.Errorf("%s has no writable buf descriptor", name)
		}
	}
}

// These are the exact source programs from the native extern regressions.
// Check their affected summaries on every host; actual host output, exit status
// and machine execution remain required by the existing ARM64 tests.
func TestNativeExternGlobalArrayProof(t *testing.T) {
	t.Setenv("OAK_VERIFY_CACHE", "0")
	t.Setenv("OAK_OPT_SKIP", "")
	t.Setenv("OAK_NATIVE_ONLY", "emit,flush")
	t.Setenv("OAK_VERIFY_BUDGET", "")
	for _, tc := range []struct {
		name, source string
		large        bool
	}{
		{"small chunk", nativeExternCallProgram, false},
		{"large chunk", nativeExternLargeChunkProgram, true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			root := writeModule(t, map[string]string{
				"oak.mod":  "module example.com/extern_global_array_proof\noak 0.1.0\n",
				"main.oak": tc.source,
			})
			comp := New().WithPackageDir(root).
				WithTarget(target.Target{OS: target.OSLinux, Arch: target.ArchArm64}).WithNativeBodies().WithNativeAsm()
			comp.options.InlineHelpers = true
			model, err := comp.SemanticModel().Get()
			if err != nil {
				t.Fatal(err)
			}
			emit, ok := model.NativeVerdicts["emit"]
			if !ok || emit.Kind != asm.VerdictProven {
				t.Fatalf("emit must prove: present=%v kind=%s message=%s", ok, emit.Kind, emit.Message)
			}
			if tc.large {
				if !strings.Contains(emit.Message, "2 data-dependent loops coupled inductively") {
					t.Errorf("large chunk proof lost loop coupling: %s", emit.Message)
				}
				if got := model.NativeFallbacks["flush"]; got != "a frame of 4192 bytes" {
					t.Errorf("large flush fallback = %q", got)
				}
			} else {
				flush, ok := model.NativeVerdicts["flush"]
				want := "a call to host__host_uwrite_uall: the span argument bytes is not one of the caller's span parameters passed whole (its length is not a constant)"
				if !ok || flush.Kind != asm.VerdictTrusted || !strings.Contains(flush.Message, want) {
					t.Errorf("small flush must retain its exact span-length boundary: present=%v kind=%s message=%s", ok, flush.Kind, flush.Message)
				}
			}
		})
	}
}
