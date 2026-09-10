package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// The examples/asm package: `.oakasm` units beside the sources are
// discovered by the package build, checked, verified against their Oak
// bodies, and executed both ways — the CLI's `oak run examples/asm` path.
func TestE2EExampleAsmPackage(t *testing.T) {
	requireArm64Host(t)
	var verdicts []string
	comp := New().WithPackageDir("../examples/asm").WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "asm" && d.Severity == diagnostic.SeverityInformation {
			verdicts = append(verdicts, d.Message)
		}
	})
	for _, flags := range [][]string{nil, {"-DOAK_PORTABLE_INTRINSICS"}} {
		_, code, abnormal := buildAndRunFrom(t, "example_asm", comp, flags...)
		if abnormal || code != 42 {
			t.Fatalf("flags %v: exit = (%d, abnormal=%v), want 42", flags, code, abnormal)
		}
	}
	joined := strings.Join(verdicts, "\n")
	for _, fn := range []string{"field", "sat_add", "max32", "checksum"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Fatalf("%s must be reported proven; verdicts:\n%s", fn, joined)
		}
	}
}
