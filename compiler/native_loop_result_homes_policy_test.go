package compiler

import (
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/target"
)

func TestNativeLoopResultHomesExperimentalPolicy(t *testing.T) {
	for _, tc := range []struct {
		name, enabled, skip string
		want                bool
	}{
		{"default off", "", "", false},
		{"explicit off", "0", "", false},
		{"unknown value", "true", "", false},
		{"opt in", "1", "", true},
		{"skip wins", "1", " loop-result-homes ", false},
		{"other skip", "1", "loop-array-homes", true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			t.Setenv("OAK_NATIVE_LOOP_RESULT_HOMES", tc.enabled)
			t.Setenv("OAK_OPT_SKIP", tc.skip)
			tr, found := nativeSearch(asm.ArchArm64, nil).Registry.Lookup(nativegen.TransformLoopResultHomes)
			if found != tc.want {
				t.Fatalf("offered=%v, want %v", found, tc.want)
			}
			if !found {
				return
			}
			if g, ok := tr.(opt.Gated); !ok || !g.NeedsVerdict() || tr.Proof() != opt.Mechanical {
				t.Fatal("experimental candidate lost its verifier gate")
			}
			if n, ok := tr.(opt.Neutral); ok && n.ShapeNeutral() {
				t.Fatal("result homes must not inherit a neutral-body verdict")
			}
			if tr.Apply(opt.Identity(nativegen.Lane{Arch: asm.ArchRV64})) != nil {
				t.Fatal("result homes crossed into the RV64 lane")
			}
		})
	}
}

// Offering the experiment must retain proof and the integrated register path.
// A better strategy may supersede result homes; the dedicated result fixtures
// separately require them to fire. No speedup or source-to-ASL claim follows.
func TestNativeBlake3LoopResultHomesExperiment(t *testing.T) {
	t.Setenv("OAK_OPT_SKIP", "")
	t.Setenv("OAK_NATIVE_ONLY", nativeBlake3CompressName)
	t.Setenv("OAK_VERIFY_CACHE", "0")
	t.Setenv("OAK_VERIFY_BUDGET", "")
	root := nativeBlake3Module(t, [][]byte{nil})
	comp := New().WithPackageDir(root).
		WithTarget(target.Target{OS: target.OSDarwin, Arch: target.ArchArm64}).
		WithNativeBodies().WithNativeAsm()
	comp.options.InlineHelpers = true
	var first *asm.Function
	for attempt := 0; attempt < 2; attempt++ {
		t.Setenv("OAK_NATIVE_LOOP_RESULT_HOMES", []string{"0", "1"}[attempt])
		model, err := comp.SemanticModel().Get()
		if err != nil {
			t.Fatal(err)
		}
		verdict := model.NativeVerdicts[nativeBlake3CompressName]
		if verdict.Kind != asm.VerdictProven || !strings.Contains(verdict.Message, "all 8 result chunks") {
			t.Fatalf("result-home experiment did not prove: %s: %s", verdict.Kind, verdict.Message)
		}
		var selected *asm.Function
		for _, fn := range model.AsmFunctions {
			if fn.Name == nativeBlake3CompressName {
				selected = fn
			}
		}
		if selected == nil || nativegen.LoopResultHomes(selected) > 2 || nativegen.LoopArrayHomes(selected) != 0 {
			t.Fatal("missing compressor or unexpected result/frame home count")
		}
		if attempt == 0 && nativegen.LoopResultHomes(selected) != 0 {
			t.Fatal("result homes fired without experimental opt-in")
		}
		stackMemory := 0
		for _, item := range selected.Items {
			if ins, ok := item.(asm.Instruction); ok && (strings.HasPrefix(ins.Mnemonic, "ld") || strings.HasPrefix(ins.Mnemonic, "st")) {
				for _, operand := range ins.Operands {
					if mem, ok := operand.(asm.Memory); ok && mem.Base.Class == asm.ClassSP {
						stackMemory++
					}
				}
			}
		}
		// Upstream scalar replacement now beats both old result-home forms.
		// Do not force a previously measured candidate over that better body.
		if selected.Frame > 160 || stackMemory > 10 || nativegen.PromotedSlots(selected) == 0 || nativegen.Metrics(selected).Instructions > 283 {
			t.Fatalf("result-home pressure regression: frame=%d SP-memory=%d promoted=%d metrics=%s",
				selected.Frame, stackMemory, nativegen.PromotedSlots(selected), nativegen.Metrics(selected))
		}
		if first != nil && nativegen.LoopResultHomes(selected) == 0 && (first.Frame != selected.Frame || !reflect.DeepEqual(first.Items, selected.Items)) {
			t.Fatal("offering an unused result-home experiment changed the default body")
		}
		first = selected
	}
}
