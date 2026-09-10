package testrunner

import (
	"strings"
	"testing"
	"time"
)

func TestReportFileFailureCarriesTheError(t *testing.T) {
	// A missing working directory makes the report file uncreatable; the
	// outcome must name the harness failure and carry the OS error text.
	p := &nativeProgram{bin: "/nonexistent/test", dir: t.TempDir() + "/gone", maxBytes: 64, timeout: time.Second}
	out := p.run(0, nil)
	if out.status != "fail" || out.signature != "harness:report-file" {
		t.Fatalf("outcome = %q/%q, want fail/harness:report-file", out.status, out.signature)
	}
	if !strings.Contains(out.output, "gone") {
		t.Fatalf("output %q does not name the report path", out.output)
	}
}
