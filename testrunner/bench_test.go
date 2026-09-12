package testrunner

import (
	"bytes"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"testing"
)

// The runner's throughput (docs/notes/formal-methods-performance-2026-09.md
// section 4, item 9): a campaign of trivial property cases over one
// compiled package, reported as cases per second so the per-case costs show
// directly. The compile of the fixture is inside the timer, as it is for a
// user, and cached after the first run.
func BenchmarkCampaign(b *testing.B)           { benchmarkCampaign(b, true) }
func BenchmarkCampaignPerProcess(b *testing.B) { benchmarkCampaign(b, false) }

// resident runs the cases through resident harness workers (the default);
// per-process starts a process per case, the shape before them.
func benchmarkCampaign(b *testing.B, resident bool) {
	if _, err := exec.LookPath("cc"); err != nil {
		b.Skip("requires cc")
	}
	dir := b.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "a_test.oak"), []byte(campaignFixture), 0600); err != nil {
		b.Fatal(err)
	}
	const runs = 2000
	for i := 0; i < b.N; i++ {
		var stdout, stderr bytes.Buffer
		if code := Main([]string{"-json", "-run", "^PropertyAlwaysPasses$", "-runs", strconv.Itoa(runs), "-resident=" + strconv.FormatBool(resident), dir}, &stdout, &stderr); code != 0 {
			b.Fatalf("exit %d: %s", code, stderr.String())
		}
	}
	b.ReportMetric(float64(runs)*float64(b.N)/b.Elapsed().Seconds(), "cases/s")
}
