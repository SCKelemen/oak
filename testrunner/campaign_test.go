package testrunner

import (
	"bytes"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

const campaignFixture = `import(testing)
PropertyNibble: (data: []u8): () {
  test_assume(len(data) > u32(0))
  test_check((data[0] & u8(15)) != u8(7) || len(data) < u32(2), u32(7200))
}
PropertyAlwaysPasses: (data: []u8): () { testing_classify(u32(1)) }
`

// The worker count changes wall-clock time only: the failing attempt, its
// minimized input, and every count are identical.
func TestWorkersDeterministic(t *testing.T) {
	var reference Result
	var referenceInput []byte
	for _, workers := range []string{"1", "4"} {
		dir := fixture(t, map[string]string{"a_test.oak": campaignFixture})
		code, results, stderr := runCLI(t, "-run", "^PropertyNibble$", "-workers", workers, "-runs", "500", dir)
		if code != 1 || len(results) != 1 || results[0].Failure != "invariant:7200" {
			t.Fatalf("workers %s: %d %+v %s", workers, code, results, stderr)
		}
		a, err := readArtifact(results[0].Artifact, 256)
		if err != nil {
			t.Fatal(err)
		}
		if workers == "1" {
			reference, referenceInput = results[0], a.Input
			continue
		}
		r := results[0]
		if r.Cases != reference.Cases || r.Discards != reference.Discards || r.Attempts != reference.Attempts || a.Attempt != reference.Attempts-1 || !bytes.Equal(a.Input, referenceInput) {
			t.Fatalf("worker count changed the outcome:\n%+v %v\n%+v %v", reference, referenceInput, r, a.Input)
		}
	}
}

// A campaign continues the same attempt sequence across invocations and
// refuses state from a different configuration.
func TestCampaignResume(t *testing.T) {
	dir := fixture(t, map[string]string{"a_test.oak": campaignFixture})
	campaign := filepath.Join(t.TempDir(), "campaign")
	code, results, stderr := runCLI(t, "-run", "^PropertyAlwaysPasses$", "-runs", "5", "-campaign", campaign, dir)
	if code != 0 || results[0].Cases != 5 || results[0].Attempts != 5 {
		t.Fatalf("first run: %d %+v %s", code, results, stderr)
	}
	code, results, stderr = runCLI(t, "-run", "^PropertyAlwaysPasses$", "-runs", "12", "-workers", "3", "-campaign", campaign, dir)
	if code != 0 || results[0].Cases != 12 || results[0].Attempts != 12 || results[0].Classes[1] != 12 {
		t.Fatalf("resumed run: %d %+v %s", code, results, stderr)
	}
	// Already satisfied campaigns do no new work.
	code, results, _ = runCLI(t, "-run", "^PropertyAlwaysPasses$", "-runs", "12", "-campaign", campaign, dir)
	if code != 0 || results[0].Cases != 12 || results[0].Attempts != 12 {
		t.Fatalf("satisfied run: %d %+v", code, results)
	}
	entries, err := os.ReadDir(campaign)
	if err != nil || len(entries) != 1 || !strings.HasPrefix(entries[0].Name(), "PropertyAlwaysPasses-") {
		t.Fatalf("campaign state files: %v %v", entries, err)
	}
	code, results, _ = runCLI(t, "-run", "^PropertyAlwaysPasses$", "-runs", "12", "-seed", "2", "-campaign", campaign, dir)
	if code != 2 || results[0].Status != "error" || !strings.Contains(results[0].Failure, "different build, test, seed") {
		t.Fatalf("mismatched campaign accepted: %d %+v", code, results)
	}
	// A failing campaign checkpoints the consumed attempts before reporting.
	failing := filepath.Join(t.TempDir(), "failing")
	code, results, _ = runCLI(t, "-run", "^PropertyNibble$", "-runs", "500", "-shrink", "0", "-campaign", failing, dir)
	if code != 1 || results[0].Failure != "invariant:7200" || results[0].Attempts == 0 {
		t.Fatalf("failing campaign: %d %+v", code, results)
	}
	if code, _, _ := runCLI(t, "-replay", results[0].Artifact, "-campaign", failing, dir); code != 2 {
		t.Fatal("replay must not combine with a campaign")
	}
}
