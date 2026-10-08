package compiler

import (
	"errors"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

// Bare names after := are looked up as operands, not introduced as ADT
// constructors. Invalid operands retain the ordinary bitwise diagnostics.
func TestInferredValueCheckingDiagnostics(t *testing.T) {
	for _, tc := range []struct{ name, source, want string }{
		{"former shorthand", "Color := Red | Blue", "undefined variable: Red"},
		{"signed operands", "a: i32 = 1\nb: i32 = 2\nmask := a | b", "requires unsigned fixed-width operands"},
		{"boolean operands", "a: Bool = true\nb: Bool = false\nmask := a | b", "requires unsigned fixed-width operands"},
		{"mixed widths", "a: u32 = 1\nb: u64 = 2\nmask := a | b", "requires same-width operands"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			comp := New().WithSource("inferred.oak", tc.source)
			if _, err := comp.Parse().Get(); err != nil {
				t.Fatalf("value expression must parse before checking: %v", err)
			}
			_, err := comp.Check().Get()
			var diagnosticErr *DiagnosticError
			if !errors.As(err, &diagnosticErr) {
				t.Fatalf("want checker diagnostic, got %v", err)
			}
			for _, d := range diagnosticErr.Diagnostics {
				if d.Category == diagnostic.CategoryType && strings.Contains(d.Message, tc.want) {
					return
				}
			}
			t.Fatalf("missing ordinary type diagnostic %q: %v", tc.want, err)
		})
	}
}

func inferredOrSource(t *testing.T) string {
	t.Helper()
	source, err := os.ReadFile(filepath.Join("testdata", "syntax", "declarations", "inferred_or.exit42.oak"))
	if err != nil {
		t.Fatal(err)
	}
	return string(source)
}

// C execution is part of TestSyntaxCorpus. These target-independent checks
// additionally require the inferred local's function to lower on both native
// lanes, rather than silently falling back to C.
func TestInferredValueNativeLowering(t *testing.T) {
	for _, arch := range []string{target.ArchArm64, target.ArchRiscv64} {
		t.Run(arch, func(t *testing.T) {
			comp := New().WithSource("inferred.oak", inferredOrSource(t)).
				WithTarget(target.Target{OS: target.OSFreestanding, Arch: arch}).WithNativeBodies()
			model, err := comp.Check().Get()
			if err != nil {
				t.Fatal(err)
			}
			if reason, fallback := model.NativeFallbacks["or_mask"]; fallback {
				t.Fatalf("inferred bitwise function fell back to C: %s", reason)
			}
			foundOR := false
			for _, fn := range model.AsmFunctions {
				if fn.Name != "or_mask" {
					continue
				}
				for _, item := range fn.Items {
					if ins, ok := item.(asm.Instruction); ok && (ins.Mnemonic == "orr" || ins.Mnemonic == "or") {
						foundOR = true
					}
				}
			}
			if !foundOR {
				t.Fatal("inferred value function has no native bitwise OR instruction")
			}
			// The verifier currently reports inferred locals as trusted because
			// their source annotation is absent. Object generation is not proof.
			verdict, ok := model.NativeVerdicts["or_mask"]
			if !ok {
				t.Fatal("missing native verification verdict")
			}
			t.Logf("or_mask native verdict: %s (%s)", verdict.Kind, verdict.Message)
			if output, err := comp.EmitNative(asm.ELF).Get(); err != nil || len(output.Object) == 0 {
				t.Fatalf("inferred bitwise native object: %v", err)
			}
			// Execute the native pipeline's portable realization on any host.
			if _, code, abnormal := buildAndRunFrom(t, "inferred_"+arch+"_portable", comp, "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
				t.Fatalf("portable native realization: exit = (%d, abnormal=%v), want 42", code, abnormal)
			}
		})
	}
}

func TestE2EInferredValueNativeARM64(t *testing.T) {
	requireArm64Host(t)
	comp := New().WithSource("inferred.oak", inferredOrSource(t)).WithNativeBodies().WithNativeAsm()
	if _, code, abnormal := buildAndRunFrom(t, "inferred_native", comp); abnormal || code != 42 {
		t.Fatalf("native inferred bitwise value: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2EInferredValueNativeRV64UnderQEMU(t *testing.T) {
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	native, _ := nativeRV64Lower(t, bare, inferredOrSource(t))
	if out := runNativeRV64Bare(t, "inferred_native_rv64", native); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("native inferred bitwise value did not exit 42:\n%s", out)
	}
}
