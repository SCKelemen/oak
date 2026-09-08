package testrunner

import (
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

const schedSchema = `{
  "version": 1,
  "events": {
    "401": {"name": "command",
            "a": [{"name": "kind", "shift": 32, "bits": 32, "names": {"0": "admit", "5": "tick"}},
                  {"name": "target", "shift": 16, "bits": 16},
                  {"name": "value", "shift": 0, "bits": 16}],
            "b": [{"name": "ticks"}]},
    "402": {"name": "state", "a": [{"name": "packed"}]}
  }
}`

func TestTraceSchemaDescribe(t *testing.T) {
	dir := fixture(t, map[string]string{traceSchemaFile: schedSchema})
	schema, err := loadTraceSchema(dir)
	if err != nil || schema == nil {
		t.Fatal(err)
	}
	got := schema.Describe(TraceEvent{ID: 401, A: 5<<32 | 1<<16 | 7, B: 9})
	if got != "command kind=tick target=1 value=7 ticks=9" {
		t.Fatalf("decoded %q", got)
	}
	if got := schema.Describe(TraceEvent{ID: 402, A: 3}); got != "state packed=3" {
		t.Fatalf("decoded %q", got)
	}
	if got := schema.Describe(TraceEvent{ID: 999, A: 1, B: 2}); got != "id=999 a=1 b=2" {
		t.Fatalf("unknown event %q", got)
	}
	if (*TraceSchema)(nil).Describe(TraceEvent{ID: 1}) != "id=1 a=0 b=0" {
		t.Fatal("nil schema must keep the raw form")
	}
	for _, bad := range []string{
		`{"version": 2, "events": {}}`,
		`{"version": 1, "events": {"x": {"name": "e"}}}`,
		`{"version": 1, "events": {"1": {"name": "e", "a": [{"name": "f", "shift": 60, "bits": 8}]}}}`,
		`{"version": 1, "events": {"1": {"name": "e", "a": [{"name": "f", "names": {"x": "y"}}]}}}`,
		`{"version": 1, "events": {"1": {"name": "bad name"}}}`,
		`{"version": 1, "events": {}, "extra": true}`,
	} {
		dir := fixture(t, map[string]string{traceSchemaFile: bad})
		if _, err := loadTraceSchema(dir); err == nil {
			t.Fatalf("accepted invalid schema %s", bad)
		}
	}
	if schema, err := loadTraceSchema(t.TempDir()); err != nil || schema != nil {
		t.Fatalf("missing schema: %v %v", schema, err)
	}
}

// Failures and artifacts print decoded events; a tampered artifact's replay
// names the first recorded event the observed trace did not reproduce.
func TestTraceSchemaInResultsAndDivergence(t *testing.T) {
	dir := fixture(t, map[string]string{
		traceSchemaFile: schedSchema,
		"a_test.oak": `import(testing)
TestDecoded: (): () {
  testing_trace(u32(401), (u64(5) << u64(32)) | u64(3), u64(1))
  testing_trace(u32(402), u64(8), u64(0))
  test_check(false, u32(7100))
}
`})
	code, results, stderr := runCLI(t, "-shrink", "0", dir)
	if code != 1 || len(results) != 1 || results[0].Failure != "invariant:7100" {
		t.Fatalf("%d %+v %s", code, results, stderr)
	}
	want := []string{"command kind=tick target=0 value=3 ticks=1", "state packed=8"}
	if strings.Join(results[0].TraceText, "|") != strings.Join(want, "|") {
		t.Fatalf("trace text %v", results[0].TraceText)
	}
	raw, err := os.ReadFile(results[0].Artifact)
	if err != nil {
		t.Fatal(err)
	}
	var a Artifact
	if err := json.Unmarshal(raw, &a); err != nil {
		t.Fatal(err)
	}
	a.Trace[1].A = 9
	tampered := filepath.Join(dir, "tampered.json")
	raw, _ = json.Marshal(a)
	if err := os.WriteFile(tampered, raw, 0600); err != nil {
		t.Fatal(err)
	}
	code, replay, _ := runCLI(t, "-replay", tampered, dir)
	if code != 2 || replay[0].Status != "error" || replay[0].Divergence == nil {
		t.Fatalf("divergence not reported: %d %+v", code, replay)
	}
	d := replay[0].Divergence
	if d.Index != 1 || d.Recorded == nil || d.Recorded.A != 9 || d.Observed == nil || d.Observed.A != 8 {
		t.Fatalf("divergence %+v", d)
	}
	if !strings.Contains(replay[0].Failure, "diverged at event 1") {
		t.Fatalf("failure text %q", replay[0].Failure)
	}
}
