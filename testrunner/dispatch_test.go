package testrunner

import (
	"runtime"
	"testing"
)

// Checked dispatch claims (docs/spec/93-simd.md section 6.2): under oak
// test a pure dispatched function runs the realization the probe selected
// and its own body, and a disagreement is the correctness failure
// `dispatch:<function>:<feature>`. The fixture dispatches on `crc`, which
// every AArch64 host this suite runs on has; elsewhere the slot is inert
// and there is nothing to check, so the test asks for arm64.
func TestDispatchClaimsAreChecked(t *testing.T) {
	if runtime.GOARCH != "arm64" {
		t.Skip("the crc slot is inert off AArch64")
	}
	files := map[string]string{
		"claims.oak": `package main
// The realization disagrees with the body: the claim is false.
wrong: (x: u32): u32 dispatch { crc: wrong_realization } = x + u32(1)
wrong_realization: (x: u32): u32 = x + u32(2)
// The realization agrees: the claim holds.
right: (x: u32): u32 dispatch { crc: right_realization } = x * u32(3)
right_realization: (x: u32): u32 = x * u32(3)
main: (): i32 = 0
`,
		"claims_test.oak": `package main
import(testing)
TestRight: (): () {
  assert(right(u32(2)) == u32(6))
}
TestWrong: (): () {
  assert(wrong(u32(1)) >= u32(0))
}
`,
		"oak.mod": "module example.com/claims\noak 0.1.0\n",
	}
	dir := fixture(t, files)
	code, results, stderr := runCLI(t, "-run", "TestRight", dir)
	if code != 0 || len(results) != 1 || results[0].Status != "pass" {
		t.Fatalf("a true claim passes: %d %+v %s", code, results, stderr)
	}
	code, results, stderr = runCLI(t, "-run", "TestWrong", dir)
	if code != 1 || len(results) != 1 || results[0].Status != "fail" {
		t.Fatalf("a false claim fails the case: %d %+v %s", code, results, stderr)
	}
	if results[0].Failure != "dispatch:wrong:crc" || results[0].Class != "correctness" {
		t.Fatalf("the failure names the function and feature as a correctness failure: %+v", results[0])
	}
}
