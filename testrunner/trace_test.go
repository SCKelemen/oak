package testrunner

import (
	"bytes"
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestMinimizedTraceAndExactReplay(t *testing.T) {
	dir := fixture(t, map[string]string{"trace_test.oak": `import(testing)
SimTrace: (data: []u8): () {
  storage: [1]TestChoices
  choices: [*]TestChoices = span(&storage)
  value: u8 = test_byte(choices, data)
  testing_trace(u32(42), u64(value), u64(len(data)))
  testing_trace(u32(43), ^u64(0), u64(9007199254740993))
  test_check(value < u8(7), u32(7003))
}
`})
	code, results, stderr := runCLI(t, "-runs", "4", dir)
	if code != 1 || len(results) != 1 || results[0].Failure != "invariant:7003" {
		t.Fatalf("%d %+v %s", code, results, stderr)
	}
	result := results[0]
	a, err := readArtifact(result.Artifact, 256)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(a.Input, []byte{7}) || a.TraceVersion != traceVersion || len(a.Trace) != 2 || a.Trace[0] != (TraceEvent{ID: 42, A: 7, B: 1}) || a.Trace[1].A != ^uint64(0) || a.Trace[1].B != 9007199254740993 || !sameTrace(outcome{trace: a.Trace}, outcome{trace: result.Trace}) {
		t.Fatalf("trace does not describe minimized input: %+v", a)
	}
	raw, _ := os.ReadFile(result.Artifact)
	if !bytes.Contains(raw, []byte(`"18446744073709551615"`)) {
		t.Fatalf("64-bit payload not lossless JSON: %s", raw)
	}
	code, results, stderr = runCLI(t, "-replay", result.Artifact, dir)
	if code != 1 || results[0].Failure != "reproduced invariant:7003" {
		t.Fatalf("%d %+v %s", code, results, stderr)
	}
	// Same concrete input/build/invariant, but a different observed history.
	a.Trace[0].A++
	tampered := filepath.Join(t.TempDir(), "trace.json")
	raw, _ = json.Marshal(a)
	os.WriteFile(tampered, raw, 0600)
	code, results, stderr = runCLI(t, "-replay", tampered, dir)
	if code != 2 || !strings.Contains(results[0].Failure, "trace diverged") {
		t.Fatalf("%d %+v %s", code, results, stderr)
	}
	// Old artifacts are valid regression inputs and have no trace contract.
	a.TraceVersion, a.Trace, a.TraceTruncated = 0, nil, false
	raw, _ = json.Marshal(a)
	os.WriteFile(tampered, raw, 0600)
	code, results, _ = runCLI(t, "-replay", tampered, dir)
	if code != 1 || results[0].Failure != "reproduced invariant:7003" {
		t.Fatalf("legacy replay: %d %+v", code, results)
	}
}

func TestTraceBoundsCrashAndTimeout(t *testing.T) {
	dir := fixture(t, map[string]string{"trace_test.oak": `import(testing)
TestTraceBound: (): () {
  i: u32 = u32(0)
  while i < u32(300) {
    testing_trace(u32(44), u64(i), u64(0))
    i = i + u32(1)
  }
  test_check(false, u32(7004))
}
TestTraceCrash: (): () { testing_trace(u32(45), u64(1), u64(2)); assert(false) }
TestTraceTimeout: (): () { testing_trace(u32(46), u64(3), u64(4)); while true {} }
`})
	code, results, stderr := runCLI(t, "-timeout", "100ms", "-shrink", "0", dir)
	if code != 1 || len(results) != 3 {
		t.Fatalf("%d %+v %s", code, results, stderr)
	}
	for _, r := range results {
		if r.Name == "TestTraceBound" {
			if r.Failure != "invariant:7004" || len(r.Trace) != traceLimit || !r.TraceTruncated || r.Trace[traceLimit-1].A != traceLimit-1 {
				t.Fatalf("trace bound: %+v", r)
			}
			code, replay, _ := runCLI(t, "-replay", r.Artifact, dir)
			if code != 1 || replay[0].Failure != "reproduced invariant:7004" {
				t.Fatalf("truncated replay: %d %+v", code, replay)
			}
		} else if len(r.Trace) != 1 || r.TraceTruncated || r.Status != "fail" {
			t.Fatalf("lost crash/timeout prefix: %+v", r)
		}
		if r.Name == "TestTraceTimeout" && r.Failure != "timeout" {
			t.Fatalf("timeout changed: %+v", r)
		}
	}
}

func TestTraceSchemaRejectsInvalidHistories(t *testing.T) {
	a := Artifact{TimeoutNanos: 1, Version: 1, Engine: engineVersion, Test: "TestTrace", Kind: "unit", Build: strings.Repeat("a", 64), Signature: "invariant:1"}
	for _, bad := range []Artifact{
		func() Artifact { b := a; b.TraceVersion = 2; return b }(),
		func() Artifact { b := a; b.Trace = []TraceEvent{{ID: 1}}; return b }(),
		func() Artifact { b := a; b.TraceVersion = traceVersion; b.TraceTruncated = true; return b }(),
		func() Artifact {
			b := a
			b.TraceVersion = traceVersion
			b.Trace = make([]TraceEvent, traceLimit+1)
			return b
		}(),
	} {
		path := filepath.Join(t.TempDir(), "invalid.json")
		raw, _ := json.Marshal(bad)
		os.WriteFile(path, raw, 0600)
		if _, err := readArtifact(path, 256); err == nil {
			t.Fatalf("accepted invalid trace: %+v", bad)
		}
	}
}
