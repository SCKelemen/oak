package compiler

import (
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/opt"
)

func decision(report OptimizationReport, rule OptimizationRule, kind opt.RemarkKind, function, message string) (OptimizationDecision, bool) {
	for _, item := range report.Remarks {
		if item.Transform == rule && item.Kind == kind && item.Function == function && strings.Contains(item.Message, message) {
			return item, true
		}
	}
	return OptimizationDecision{}, false
}

// The source optimizer is opt-in with executable emission. Ordinary semantic
// checking remains the program as written; an optimization request returns a
// deterministic account of the beta reductions that actually happened.
func TestOptimizationReportTracksCheckedInlining(t *testing.T) {
	plain, err := New().WithSource("inline.oak", inlineHelperProgram).Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	if len(plain.Optimizations.Remarks) != 0 {
		t.Fatalf("semantic Check unexpectedly optimized the program: %+v", plain.Optimizations.Remarks)
	}

	comp := New().WithSource("inline.oak", inlineHelperProgram)
	first, err := comp.Optimizations().Get()
	if err != nil {
		t.Fatal(err)
	}
	second, err := comp.Optimizations().Get()
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(first, second) {
		t.Fatalf("optimization reports are not deterministic:\nfirst:  %+v\nsecond: %+v", first, second)
	}
	for _, edge := range []struct{ caller, callee string }{
		{"sum_guarded", "byte_at"},
		{"sum_guarded", "weighted"},
		{"first_small", "byte_at"},
	} {
		item, ok := decision(first, OptimizationInlineLeaf, opt.Passed, edge.caller, "inlined "+edge.callee+" 1 time(s)")
		if !ok || !strings.Contains(item.Message, "optimized program re-typechecked") || len(item.Facts) != 2 {
			t.Errorf("missing checked inline %s -> %s: %+v", edge.caller, edge.callee, first.Remarks)
		}
	}
}

// A public helper is outside the private-leaf rule even when it has the same
// body shape. A report cannot make it eligible.
func TestOptimizationReportDoesNotAuthorizeIneligibleInlining(t *testing.T) {
	report, err := New().WithSource("public.oak", `
pub visible: (x: u32): u32 = x + u32(1)
main: (): i32 = i32_bits_u32(visible(u32(41)))
`).Optimizations().Get()
	if err != nil {
		t.Fatal(err)
	}
	if _, ok := decision(report, OptimizationInlineLeaf, opt.Passed, "main", "inlined visible"); ok {
		t.Fatalf("public helper was reported as inlined: %+v", report.Remarks)
	}
}
