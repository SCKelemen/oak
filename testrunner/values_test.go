package testrunner

import (
	"strings"
	"testing"
)

// E3: a test_check_eq_* failure names both values in the runner's failure
// text and in the JSON result, while the signature the shrinker minimizes
// against stays the invariant id alone.
func TestCheckValuesReported(t *testing.T) {
	dir := fixture(t, map[string]string{"a_test.oak": `import(testing)
PropertyEqFails: (data: []u8): () {
 state: [1]TestChoices
 choices: [*]TestChoices = span(&state)
 value: u8 = test_byte(choices, data)
 test_check_eq_u32(u32(value), u32(0), u32(7002))
}
TestNeFails: (): () {
 test_check_ne_bool(u32(1) < u32(2), true, u32(7003))
}
TestSignedFails: (): () {
 test_check_eq_i64(i64(0) - i64(9), i64(4), u32(7004))
}`})
	code, results, stderr := runCLI(t, "-runs", "8", dir)
	if code != 1 || len(results) != 3 {
		t.Fatalf("%d %+v %s", code, results, stderr)
	}
	byName := map[string]Result{}
	for _, r := range results {
		byName[r.Name] = r
	}
	eq := byName["PropertyEqFails"]
	if eq.Failure != "invariant:7002 (got 1, want 0)" || eq.Got != "1" || eq.Want != "0" || eq.WantNot {
		t.Fatalf("minimized value failure: %+v", eq)
	}
	ne := byName["TestNeFails"]
	if ne.Failure != "invariant:7003 (got true, want anything but true)" || !ne.WantNot {
		t.Fatalf("not-equal failure: %+v", ne)
	}
	signed := byName["TestSignedFails"]
	if signed.Failure != "invariant:7004 (got -9, want 4)" || signed.Got != "-9" {
		t.Fatalf("signed failure: %+v", signed)
	}
	// The artifact replays by signature and carries the values again.
	if eq.Artifact == "" {
		t.Fatalf("no artifact: %+v", eq)
	}
	code, results, stderr = runCLI(t, "-replay", eq.Artifact, dir)
	if code != 1 || len(results) != 1 || results[0].Failure != "reproduced invariant:7002" || results[0].Got != "1" {
		t.Fatalf("replay: %d %+v %s", code, results, stderr)
	}
	// The terminal form prints the same line.
	var stdout strings.Builder
	if Main([]string{"-run", "^TestSignedFails$", dir}, &stdout, &stdout) != 1 || !strings.Contains(stdout.String(), "invariant:7004 (got -9, want 4)") {
		t.Fatalf("terminal output:\n%s", stdout.String())
	}
}
