package compiler

import (
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/target"
)

func TestNativeBuildReportMatchesActualSelection(t *testing.T) {
	comp := New().WithSource("receipt.oak", `pub add: (x: u32): u32 = x + u32(1)
main: (): i32 = i32_bits_u32(add(u32(2)))`).WithTarget(target.Target{OS: target.OSLinux, Arch: target.ArchArm64}).WithNativeAsm()
	inventory, err := comp.NativeInventory()
	if err != nil {
		t.Fatal(err)
	}
	var report NativeBuildReport
	calls := 0
	output, err := comp.WithNativeBodies().WithVerifyFresh().WithNativeBuildReport(func(value NativeBuildReport) { report = value; calls++ }).EmitNative(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	if calls != 1 || len(output.Object) == 0 || !reflect.DeepEqual(report.Inventory, inventory) || len(report.Functions) != len(inventory.Eligible) {
		t.Fatalf("missing actual native completion: calls=%d report=%+v", calls, report)
	}
	for i, row := range report.Functions {
		if row.Input != inventory.Eligible[i] || row.Status != "proven" || row.Selected == nil || row.Selected.Outcome != "proven" || len(row.Validations) == 0 || row.Considered < row.Materialized || row.Materialized < 1 {
			t.Fatalf("incorrect actual selection: %+v", row)
		}
		for _, candidate := range row.Validations {
			if candidate.Cached || len(candidate.RecipeSHA256) != 64 || len(candidate.BodySHA256) != 64 {
				t.Fatalf("incomplete/falsely warm candidate: %+v", candidate)
			}
		}
	}
}

func TestNativeBuildReportDistinguishesUnfinishedTrustAndDemotion(t *testing.T) {
	report := NativeBuildReport{Functions: []NativeBuildFunction{
		{Input: NativeBuildInput{Name: "unfinished"}, Status: "unfinished"},
		{Input: NativeBuildInput{Name: "trusted"}, Status: "unfinished"},
		{Input: NativeBuildInput{Name: "demoted"}, Status: "unfinished", Selected: &NativeBuildCandidate{Outcome: "proven"}},
	}}
	result := nativeLowering{Verdicts: map[string]asm.Verdict{"trusted": {Kind: asm.VerdictTrusted, Message: "documented real trust"}}, Fallbacks: map[string]string{"demoted": "vector callee stayed in C"}}
	finishNativeBuildReport(&report, result)
	if report.Functions[0].Status != "unfinished" || report.Functions[1].Status != "trusted" || report.Functions[1].Reason != "documented real trust" || report.Functions[2].Status != "c-fallback" || report.Functions[2].Selected.Outcome != "proven" {
		t.Fatalf("completion collapsed distinct outcomes: %+v", report)
	}
}
