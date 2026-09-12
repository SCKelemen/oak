package testrunner

import (
	"bytes"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/target"
	"github.com/SCKelemen/oak/toolchain"
)

// `oak test -target` (docs/spec/90-backend.md §2a): a foreign hosted target
// is built through its cross toolchain and every test is reported "built",
// not run; a freestanding target is refused, since the test harness is
// hosted C; and the run-dependent modes are refused with a foreign target.
func TestTargetFlagBuildsWithoutRunning(t *testing.T) {
	dir := fixture(t, map[string]string{
		"production.oak": "double: (x: u32): u32 = x + x\nmain: (): i32 = 42",
		"a_test.oak": `import(testing)
TestArithmetic: (): () { test_check(double(u32(3)) == u32(6), u32(1)) }
`,
	})
	var stdout, stderr bytes.Buffer
	if code := Main([]string{"-target", "freestanding/arm", dir}, &stdout, &stderr); code != 2 || !strings.Contains(stderr.String(), "no test harness") {
		t.Fatalf("freestanding target: code %d, stderr %q", code, stderr.String())
	}
	stdout.Reset()
	stderr.Reset()
	if code := Main([]string{"-target", "linux/arm64", "-fuzz", ".", dir}, &stdout, &stderr); code != 2 || !strings.Contains(stderr.String(), "need the host target") {
		t.Fatalf("foreign target with -fuzz: code %d, stderr %q", code, stderr.String())
	}

	// A foreign hosted target that differs from the host, whichever the host
	// is; skipped where no toolchain can target it.
	foreign := target.Target{OS: target.OSLinux, Arch: "arm64"}
	if foreign.IsHost() {
		foreign = target.Target{OS: target.OSLinux, Arch: "amd64"}
	}
	if _, err := toolchain.Resolve(foreign, toolchain.Options{}, nil, nil); err != nil {
		t.Skipf("no toolchain for %s: %v", foreign, err)
	}
	code, results, errText := runCLI(t, "-target", foreign.String(), dir)
	if code != 0 {
		t.Fatalf("code %d, stderr %s, results %+v", code, errText, results)
	}
	if len(results) != 1 || results[0].Status != "built" || results[0].Name != "TestArithmetic" {
		t.Fatalf("results = %+v, want one TestArithmetic built", results)
	}
	if !strings.Contains(results[0].Output, "built for "+foreign.String()) {
		t.Fatalf("output = %q", results[0].Output)
	}
}
