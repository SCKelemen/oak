package testrunner

import (
	"bytes"
	"path/filepath"
	"strings"
	"testing"
)

// The bundled time-source consumer (examples/timesim: a lease and a timer
// against time.TimeSource, driven by a frozen source, the timesim fault
// injector, the SimClock scheduler with crashes, and typed commands) must
// pass under the runner: every registered test reports PASS and the sim
// package's fault and generator paths compile through the module loader.
func TestTimesimExample(t *testing.T) {
	dir := filepath.Join("..", "examples", "timesim")
	var stdout, stderr bytes.Buffer
	code := Main([]string{"-runs", "40", "-timeout", "20s", dir}, &stdout, &stderr)
	if code != 0 {
		t.Fatalf("oak test examples/timesim exited %d\nstdout:\n%s\nstderr:\n%s", code, stdout.String(), stderr.String())
	}
	for _, name := range []string{"TestLeaseFixedClock", "PropertyLeaseUnderClockFaults", "SimLeaseTwoClients", "PropertyLeaseCommands", "PropertyGenerators"} {
		if !strings.Contains(stdout.String(), "PASS ") || !strings.Contains(stdout.String(), name) {
			t.Fatalf("expected PASS for %s in:\n%s", name, stdout.String())
		}
	}
}
