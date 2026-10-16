package compiler

import (
	"reflect"
	"strings"
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

func TestNativeBuildReportObservesSuppliedVerdicts(t *testing.T) {
	inputs := []NativeBuildSuppliedInput{}
	verdicts := map[string]asm.Verdict{}
	for name, kind := range map[string]asm.VerdictKind{"proven": asm.VerdictProven, "witnessed": asm.VerdictWitnessed, "trusted": asm.VerdictTrusted, "refuted": asm.VerdictMismatch, "resource-trusted": asm.VerdictTrusted, "resource-witnessed": asm.VerdictWitnessed} {
		inputs = append(inputs, NativeBuildSuppliedInput{Input: NativeBuildInput{Name: name}, Arch: asm.ArchArm64, BodySHA256: "body"})
		verdicts[name] = asm.Verdict{Kind: kind, Message: "actual " + name, Callees: []string{"dependency"}, TransientResourceExhausted: strings.HasPrefix(name, "resource-")}
	}
	inputs = append(inputs, NativeBuildSuppliedInput{Input: NativeBuildInput{Name: "unfinished"}})
	rows := nativeBuildSuppliedRows(inputs, verdicts)
	for i, row := range rows {
		if row.Input != inputs[i].Input || row.Arch != inputs[i].Arch || row.BodySHA256 != inputs[i].BodySHA256 {
			t.Fatal("supplied identity changed")
		}
		if row.Input.Name == "unfinished" {
			if row.Status != "unfinished" || row.Reason != "" || len(row.Callees) != 0 {
				t.Fatalf("absent verdict acquired a result: %+v", row)
			}
			continue
		}
		want := strings.TrimPrefix(row.Input.Name, "resource-")
		if want == "refuted" {
			want = "error"
		}
		if row.Status != want || row.Reason != "actual "+row.Input.Name || !reflect.DeepEqual(row.Callees, []string{"dependency"}) {
			t.Fatalf("actual supplied verdict changed: %+v", row)
		}
		verdicts[row.Input.Name].Callees[0] = "mutated"
		if row.Callees[0] != "dependency" {
			t.Fatal("supplied observation aliases verdict dependencies")
		}
	}
}

func TestNativeBuildReportSuppliedUnitsAndForeignFallback(t *testing.T) {
	t.Setenv("OAK_VERIFY_ONLY", "")
	const unit = "identity: (x: u64): u64 = {\n bind x0 = x\n ret\n}\n"
	for _, arch := range []string{target.ArchArm64, target.ArchRiscv64} {
		t.Run(arch, func(t *testing.T) {
			comp := New().WithSource("identity.oak", "pub identity: (x: u64): u64 = x\nmain: (): i32 = 0").WithAsmUnit("identity.arm64.oakasm", unit).WithTarget(target.Target{OS: target.OSLinux, Arch: arch}).WithNativeAsm()
			comp.options.InlineHelpers = true
			inventory, err := comp.NativeInventory()
			if err != nil {
				t.Fatal(err)
			}
			var report NativeBuildReport
			model, err := comp.WithNativeBodies().WithVerifyFresh().WithNativeBuildReport(func(value NativeBuildReport) { report = value }).Check().Get()
			if err != nil || !reflect.DeepEqual(report.Inventory, inventory) {
				t.Fatalf("inventory/report disagreement: %v", err)
			}
			if arch == target.ArchArm64 {
				if len(report.Supplied) != 1 || report.Supplied[0].Input.Name != "identity" || report.Supplied[0].Status != "proven" || report.Supplied[0].Reason != model.NativeVerdicts["identity"].Message || len(report.Supplied[0].BodySHA256) != 64 {
					t.Fatalf("actual supplied unit omitted or changed: %+v", report.Supplied)
				}
				for _, input := range inventory.Eligible {
					if input.Name == "identity" {
						t.Fatal("supplied unit double-counted as generated")
					}
				}
			} else {
				found := false
				for _, input := range inventory.Eligible {
					found = found || input.Name == "identity"
				}
				if len(report.Supplied) != 0 || !found {
					t.Fatal("foreign fallback did not remain an ordinary body")
				}
			}
		})
	}
	// A selected body without an Oak specification remains honestly Trusted.
	var trusted NativeBuildReport
	_, err := New().WithSource("trusted.oak", "identity: (x: u64): u64\nmain: (): i32 = 0").WithAsmUnit("identity.arm64.oakasm", unit).WithTarget(target.Target{OS: target.OSLinux, Arch: target.ArchArm64}).WithNativeBodies().WithNativeBuildReport(func(value NativeBuildReport) { trusted = value }).Check().Get()
	if err != nil || len(trusted.Supplied) != 1 || trusted.Supplied[0].Status != "trusted" || !strings.Contains(trusted.Supplied[0].Reason, "no Oak fallback body") {
		t.Fatalf("bodyless unit acquired false proof: %+v, %v", trusted.Supplied, err)
	}
}

func TestNativeBuildInventoryExcludesInertDispatchUnits(t *testing.T) {
	inventory, err := New().WithSource("double.oak", foreignLaneDispatchProgram).WithAsmUnit("double.arm64.oakasm", foreignLaneUnit).WithTarget(target.Target{OS: target.OSLinux, Arch: target.ArchAmd64}).NativeInventory()
	if err != nil || len(inventory.Supplied) != 0 {
		t.Fatalf("inert dispatch metadata minted a supplied obligation: %+v, %v", inventory.Supplied, err)
	}
	for _, input := range inventory.Eligible {
		if input.Name == "double_asm" {
			t.Fatal("inert bodyless realization became generated")
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
