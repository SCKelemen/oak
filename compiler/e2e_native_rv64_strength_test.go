package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

// Strength reduction on the RV64 lane (docs/spec/90-backend.md §16): the
// same program as the AArch64 test, lowered for linux/riscv64 — the W
// forms keep the 32-bit types canonical — and every reduced body proven by
// the verifier, the variable divisor keeping its test.
func TestE2ENativeRV64StrengthReduction(t *testing.T) {
	var infos []string
	tgt := target.Target{OS: target.OSLinux, Arch: target.ArchRiscv64}
	comp := New().WithSource("strength.oak", nativeStrengthProgram).WithTarget(tgt).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	if _, err := comp.Check().Get(); err != nil {
		t.Fatal(err)
	}
	joined := strings.Join(infos, "\n")
	for _, fn := range []string{"midpoint", "page_of", "thirds", "halves", "divide", "search"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	for fn, want := range map[string]string{"midpoint": "1 constant operation(s) strength-reduced, proven", "page_of": "2 constant operation(s) strength-reduced, proven", "thirds": "2 constant operation(s) strength-reduced, proven", "halves": "1 constant operation(s) strength-reduced, proven"} {
		if !strings.Contains(joined, fn+": "+want) {
			t.Errorf("%s: want %q; diagnostics:\n%s", fn, want, joined)
		}
	}
	if strings.Contains(joined, "divide: 1 constant operation") || strings.Contains(joined, "keeps its plain arithmetic") {
		t.Errorf("a variable divisor must keep its test, and no body may fall back; diagnostics:\n%s", joined)
	}
}
