package testrunner

import (
	"bytes"
	"encoding/json"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func fixture(t *testing.T, files map[string]string) string {
	t.Helper()
	dir := t.TempDir()
	for path, src := range files {
		full := filepath.Join(dir, path)
		if err := os.MkdirAll(filepath.Dir(full), 0755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(full, []byte(src), 0600); err != nil {
			t.Fatal(err)
		}
	}
	return dir
}
func runCLI(t *testing.T, args ...string) (int, []Result, string) {
	t.Helper()
	if _, err := exec.LookPath("cc"); err != nil {
		t.Skip("requires cc")
	}
	var stdout, stderr bytes.Buffer
	args = append([]string{"-json"}, args...)
	code := Main(args, &stdout, &stderr)
	var results []Result
	for _, line := range strings.Split(strings.TrimSpace(stdout.String()), "\n") {
		if line == "" {
			continue
		}
		var r Result
		if err := json.Unmarshal([]byte(line), &r); err != nil {
			t.Fatalf("invalid JSON: %v\n%s", err, line)
		}
		results = append(results, r)
	}
	return code, results, stderr.String()
}
func TestDiscoveryAndValidation(t *testing.T) {
	dir := fixture(t, map[string]string{
		"production.oak":           "TestNotRegistered: (): () {}",
		"a_test.oak":               "TestOne: (): () {}\nPropertyTwo: (data: []u8): () {}\nTesthelper: (): () {}",
		"testdata/broken_test.oak": "not valid Oak",
	})
	packages, err := Discover([]string{dir, filepath.Join(dir, "...")})
	if err != nil {
		t.Fatal(err)
	}
	if len(packages) != 1 || len(packages[0].Tests) != 2 {
		t.Fatalf("discovery: %+v", packages)
	}
	bad := fixture(t, map[string]string{"a_test.oak": "TestWrong: (x: u32): () {}"})
	if _, err := Discover([]string{bad}); err == nil {
		t.Fatal("accepted invalid signature")
	}
}
func TestNativeUnitPropertyFuzzAndSim(t *testing.T) {
	dir := fixture(t, map[string]string{
		"production.oak": "double: (x: u32): u32 = x + x\nmain: (): i32 = 42",
		"a_test.oak": `import(testing)
TestArithmetic: (): () { test_check(double(u32(3)) == u32(6), u32(1)) }
PropertyRange: (data: []u8): () {
 state: [1]TestChoices
 choices: [*]TestChoices = span(&state)
 value: u32 = test_range(choices, data, u32(5), u32(10))
 test_check(value >= u32(5) && value <= u32(10), u32(2))
 testing_classify(u32(12))
}
FuzzBytes: (data: []u8): () { test_check(len(data) <= u32(256), u32(3)) }
SimOrder: (data: []u8): () {
 q: [1]SimQueue
 e: [4]SimEvent
 c: [1]SimClock
 s: [1]TestChoices
 queue: [*]SimQueue = span(&q)
 events: [*]SimEvent = span(&e)
 clock: [*]SimClock = span(&c)
 choices: [*]TestChoices = span(&s)
 test_check(sim_schedule(queue, events, clock, SimEvent { at: u64(20), kind: u32(1), value: u32(0) }), u32(4))
 test_check(sim_schedule(queue, events, clock, SimEvent { at: u64(10), kind: u32(2), value: u32(0) }), u32(5))
 first: SimEvent = sim_next(queue, events, clock, choices, data)
 test_check(first.kind == u32(2) && clock[0].now == u64(10), u32(6))
 second: SimEvent = sim_next(queue, events, clock, choices, data)
 test_check(second.kind == u32(1) && clock[0].now == u64(20), u32(7))
}`,
	})
	code, results, stderr := runCLI(t, "-runs", "8", dir)
	if code != 0 || len(results) != 4 {
		t.Fatalf("code %d: %+v\n%s", code, results, stderr)
	}
	for _, r := range results {
		if r.Status != "pass" {
			t.Fatalf("%+v", r)
		}
	}
	code, results, stderr = runCLI(t, "-fuzz", "FuzzBytes", "-runs", "20", dir)
	if code != 0 || len(results) != 1 || results[0].Cases != 20 {
		t.Fatalf("fuzz: %d %+v %s", code, results, stderr)
	}
	code, results, stderr = runCLI(t, "-run", "PropertyRange", "-runs", "5", "-cover", "12:5", dir)
	if code != 0 {
		t.Fatalf("coverage: %d %+v %s", code, results, stderr)
	}
	code, results, _ = runCLI(t, "-run", "PropertyRange", "-runs", "5", "-cover", "13:1", dir)
	if code != 1 || !strings.Contains(results[0].Failure, "class 13") {
		t.Fatalf("missed vacuous property: %d %+v", code, results)
	}
}
func TestFailureShrinkReplayAndCorpus(t *testing.T) {
	dir := fixture(t, map[string]string{"a_test.oak": `import(testing)
TestOther: (): () {}
PropertyFails: (data: []u8): () {
 state: [1]TestChoices
 choices: [*]TestChoices = span(&state)
 value: u8 = test_byte(choices, data)
 test_check(value < u8(7), u32(7001))
}`})
	code, results, stderr := runCLI(t, "-runs", "4", dir)
	if code != 1 || len(results) != 2 {
		t.Fatalf("%d %+v %s", code, results, stderr)
	}
	var failure Result
	for _, r := range results {
		if r.Name == "PropertyFails" {
			failure = r
		}
	}
	if failure.Artifact == "" || failure.Failure != "invariant:7001" {
		t.Fatalf("%+v", failure)
	}
	a, err := readArtifact(failure.Artifact, 256)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(a.Input, []byte{7}) {
		t.Fatalf("not minimized: %v", a.Input)
	}
	code, results, stderr = runCLI(t, "-replay", failure.Artifact, dir)
	if code != 1 || len(results) != 1 || results[0].Failure != "reproduced invariant:7001" {
		t.Fatalf("replay: %d %+v %s", code, results, stderr)
	}
	// Corpus runs even with a different root seed and before the empty input.
	code, results, stderr = runCLI(t, "-run", "PropertyFails", "-runs", "1", "-seed", "999", dir)
	if code != 1 || results[0].Cases != 1 {
		t.Fatalf("corpus: %d %+v %s", code, results, stderr)
	}
	// Source drift must not silently masquerade as exact replay.
	f := filepath.Join(dir, "a_test.oak")
	data, _ := os.ReadFile(f)
	os.WriteFile(f, append(data, []byte("\nTestAdded: (): () {}\n")...), 0600)
	code, results, _ = runCLI(t, "-replay", failure.Artifact, dir)
	if code == 0 || !strings.Contains(results[0].Failure, "build mismatch") {
		t.Fatalf("drift: %d %+v", code, results)
	}
}
func TestDiscardTimeoutAndCrashIsolation(t *testing.T) {
	dir := fixture(t, map[string]string{"a_test.oak": `import(testing)
PropertyDiscard: (data: []u8): () { test_assume(false) }
TestCrash: (): () { assert(false) }
TestTimeout: (): () { while true {} }
TestSurvives: (): () { test_check(true, u32(1)) }
`})
	code, results, stderr := runCLI(t, "-runs", "1", "-max-discards", "2", "-timeout", "100ms", "-shrink", "0", dir)
	if code != 1 || len(results) != 4 {
		t.Fatalf("%d %+v %s", code, results, stderr)
	}
	states := map[string]Result{}
	for _, r := range results {
		states[r.Name] = r
	}
	if states["TestSurvives"].Status != "pass" || states["TestTimeout"].Failure != "timeout" || states["TestCrash"].Status != "fail" || states["PropertyDiscard"].Discards != 3 {
		t.Fatalf("%+v", states)
	}
}
func TestNoTestsAndInvalidFlagsFail(t *testing.T) {
	dir := t.TempDir()
	for _, args := range [][]string{{dir}, {"-runs", "0", dir}, {"-run", "[", dir}} {
		var out, err bytes.Buffer
		if Main(args, &out, &err) != 2 {
			t.Fatalf("expected error for %v", args)
		}
	}
}

func TestFuzzHarnessExportAndNativeExecution(t *testing.T) {
	dir := fixture(t, map[string]string{"a_test.oak": `import(testing)
FuzzExport: (data: []u8): () {
  test_assume(len(data) > u32(0))
  test_check(data[0] != u8(7), u32(8080))
}
`})
	output := filepath.Join(t.TempDir(), "fuzz.c")
	var stdout, stderr bytes.Buffer
	code := Main([]string{"-fuzz", "^FuzzExport$", "-emit-fuzz-harness", output, dir}, &stdout, &stderr)
	if code != 0 {
		t.Fatalf("export: %d %s", code, stderr.String())
	}
	if Main([]string{"-fuzz", "^FuzzExport$", "-emit-fuzz-harness", output, dir}, &stdout, &stderr) != 2 {
		t.Fatal("overwrote existing harness")
	}
	clang, err := exec.LookPath("clang")
	if err != nil {
		t.Skip("requires clang")
	}
	binary := filepath.Join(t.TempDir(), "fuzz")
	cmd := exec.Command(clang, "-std=c11", "-g", "-O1", "-fsanitize=fuzzer,address,undefined", "-fno-sanitize-recover=all", output, "-o", binary)
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("clang: %v\n%s", err, out)
	}
	seed := filepath.Join(t.TempDir(), "seed")
	os.WriteFile(seed, []byte{1}, 0600)
	if out, err := exec.Command(binary, "-runs=1", seed).CombinedOutput(); err != nil {
		t.Fatalf("valid seed: %v\n%s", err, out)
	}
	os.WriteFile(seed, []byte{}, 0600)
	if out, err := exec.Command(binary, "-runs=1", seed).CombinedOutput(); err != nil {
		t.Fatalf("discard: %v\n%s", err, out)
	}
	os.WriteFile(seed, []byte{7}, 0600)
	if out, err := exec.Command(binary, "-runs=1", seed).CombinedOutput(); err == nil || !strings.Contains(string(out), "Oak invariant 8080 failed") {
		t.Fatalf("missed invariant: %v\n%s", err, out)
	}
}

func TestTestingLibraryBoundaries(t *testing.T) {
	dir := fixture(t, map[string]string{"a_test.oak": `import(testing)
fill_four: (writable: [*]u8): () {
  writable[0] = u8(255)
  writable[1] = u8(255)
  writable[2] = u8(255)
  writable[3] = u8(255)
}
TestChoicesAndCapacity: (): () {
  bytes: [4]u8
  fill_four(span(&bytes))
  data: []u8 = view(&bytes)
  state: [1]TestChoices
  choices: [*]TestChoices = span(&state)
  test_check(test_range(choices, data, u32(0), u32(4294967295)) == u32(4294967295), u32(9001))
  test_check(test_byte(choices, data) == u8(0), u32(9002))
  test_check(choices[0].offset == u32(4), u32(9003))
  test_check(test_range(choices, data, u32(7), u32(7)) == u32(7), u32(9004))
  q: [1]SimQueue
  e: [1]SimEvent
  c: [1]SimClock
  queue: [*]SimQueue = span(&q)
  events: [*]SimEvent = span(&e)
  clock: [*]SimClock = span(&c)
  event: SimEvent = SimEvent { at: u64(5), kind: u32(2), value: u32(3) }
  test_check(sim_schedule(queue, events, clock, event), u32(9005))
  test_check(!sim_schedule(queue, events, clock, event), u32(9006))
  test_check(queue[0].count == u32(1) && events[0].at == u64(5), u32(9007))
  result: SimEvent = sim_next(queue, events, clock, choices, data)
  test_check(result.value == u32(3) && queue[0].count == u32(0) && clock[0].now == u64(5), u32(9008))
}
`})
	code, results, stderr := runCLI(t, dir)
	if code != 0 {
		t.Fatalf("boundaries: %d %+v %s", code, results, stderr)
	}
}

// Prove that the independent model detects a deliberately injected lost-edge
// bug in the Oak IRQ pilot, and that its operation history can be minimized.
func TestIRQMutationDetected(t *testing.T) {
	files := map[string]string{}
	for _, name := range []string{"irq.oak", "irq_test.oak"} {
		data, err := os.ReadFile(filepath.Join("..", "examples", "testing", name))
		if err != nil {
			t.Fatal(err)
		}
		files[name] = string(data)
	}
	original := "action == u32(2) ? { state[0].latched = true }"
	mutant := "action == u32(2) && !state[0].active ? { state[0].latched = true }"
	if !strings.Contains(files["irq.oak"], original) {
		t.Fatal("mutation site changed")
	}
	files["irq.oak"] = strings.Replace(files["irq.oak"], original, mutant, 1)
	files["testdata/oak/PropertyIrqHistory/lost-edge.bin"] = string([]byte{0, 2, 5, 2})
	dir := fixture(t, files)
	code, results, stderr := runCLI(t, "-run", "^PropertyIrqHistory$", "-runs", "1", dir)
	if code != 1 || len(results) != 1 || results[0].Failure != "invariant:2011" {
		t.Fatalf("mutation escaped: %d %+v %s", code, results, stderr)
	}
	a, err := readArtifact(results[0].Artifact, 256)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(a.Input, []byte{0, 2, 5, 2}) {
		t.Fatalf("unexpected minimized history: %v", a.Input)
	}
}
