package testrunner

import "testing"

// Failure classes (docs/spec/110-testing.md, "Failure classes"): a failed
// invariant is a correctness failure, a failed liveness check is a
// liveness failure, and a trap is a crash; the result names the class
// beside the signature so triage and corpus routing can differ.
func TestFailureClasses(t *testing.T) {
	dir := fixture(t, map[string]string{"classes_test.oak": `import(testing)
SimCorrectness: (data: []u8): () {
  test_check(len(data) > u32(1000), u32(41))
}
SimLiveness: (data: []u8): () {
  test_liveness(len(data) > u32(1000), u32(42))
}
SimCrash: (data: []u8): () {
  assert(len(data) > u32(1000))
}
`})
	code, results, stderr := runCLI(t, "-runs", "2", "-shrink", "0", dir)
	if code != 1 || len(results) != 3 {
		t.Fatalf("code %d results %+v\n%s", code, results, stderr)
	}
	want := map[string][2]string{
		"SimCorrectness": {"invariant:41", "correctness"},
		"SimLiveness":    {"liveness:42", "liveness"},
		"SimCrash":       {"exit:", "crash"},
	}
	for _, result := range results {
		expected, known := want[result.Name]
		if !known {
			t.Fatalf("unexpected test %s", result.Name)
		}
		if result.Status != "fail" || len(result.Failure) < len(expected[0]) || result.Failure[:len(expected[0])] != expected[0] || result.Class != expected[1] {
			t.Fatalf("%s: status %s failure %q class %q, want %q/%q", result.Name, result.Status, result.Failure, result.Class, expected[0], expected[1])
		}
	}
	for signature, class := range map[string]string{"timeout": "liveness", "harness:bad-report": "harness", "invariant:7": "correctness", "liveness:3": "liveness", "exit:signal: abort": "crash", "": ""} {
		if got := FailureClass(signature); got != class {
			t.Fatalf("FailureClass(%q) = %q, want %q", signature, got, class)
		}
	}
}
