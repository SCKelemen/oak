package prove

import "testing"

const sampleProjection = `namespace Oak.Theorems

def a (x : UInt32) (fuel : Nat) : Option (Bool) := do
  pure (x == x)
set_option linter.unusedSimpArgs false in
theorem a_holds (x : UInt32) (fuel : Nat) : a x fuel = some true := by
  unfold a
  first | rfl | decide

def b (x : UInt32) (fuel : Nat) : Option (Bool) := do
  pure (x + (1 : UInt32) > x)
set_option linter.unusedSimpArgs false in
theorem b_holds (x : UInt32) (fuel : Nat) : b x fuel = some true := by
  unfold b
  first | rfl | decide

end Oak.Theorems
`

// Lean's diagnostics are placed by line inside the statements they fall
// in; a statement without an error is proved, one with an error stays open
// and carries the message.
func TestLeanDiagnosticsPlacement(t *testing.T) {
	ranges := statementRanges(sampleProjection)
	if r, ok := ranges["a"]; !ok || r[0] != 6 || r[1] != 9 {
		t.Fatalf("a: range %v (%v)", r, ok)
	}
	if r, ok := ranges["b"]; !ok || r[0] != 13 || r[1] != 16 {
		t.Fatalf("b: range %v (%v)", r, ok)
	}
	output := "/tmp/x.lean:16:2: error: unsolved goals\n  x : UInt32\n/tmp/x.lean:17:10: warning: something\n"
	errors := leanErrors(output, ranges)
	if len(errors) != 1 || errors["b"] != "unsolved goals" {
		t.Fatalf("errors: %v", errors)
	}
	if names := statedTheorems(sampleProjection); len(names) != 2 || names[0] != "a" || names[1] != "b" {
		t.Fatalf("stated: %v", names)
	}
}
