package typechecker

import (
	"strings"
	"testing"
)

func checkAssignabilityProgram(input string) []string {
	tc := setupTypeChecker(input)
	tc.CheckProgram(parseProgram(input))
	return tc.Errors()
}

func TestNeverFlowsThroughExpectedPositions(t *testing.T) {
	errors := checkAssignabilityProgram(`
exit_value: (): u32 = arm64.eret()
choose: (take: Bool): u32 = take ? u32(7) | arm64.eret()
accept: (value: u32): u32 = value
exit_argument: (): u32 = accept(arm64.eret())
literal_exit: (): u32 {
  exit := fn(): u32 = arm64.eret()
  exit()
}
exit_assignment: (): u32 {
  value: u32 = u32(1)
  value = arm64.eret()
  value
}
`)
	if len(errors) != 0 {
		t.Fatalf("never was rejected in an expected position: %v", errors)
	}
}

func TestExpectedMatchChecksArmsBeforeJoining(t *testing.T) {
	errors := checkAssignabilityProgram(`
widen: (pick_small: Bool, small: u8): u16 = pick_small ? small | u16(9)
`)
	if len(errors) != 0 {
		t.Fatalf("representable expected match rejected: %v", errors)
	}

	errors = checkAssignabilityProgram(`
bad: (pick_number: Bool): u32 = pick_number ? u32(1) | false
`)
	if len(errors) == 0 || !strings.Contains(strings.Join(errors, "\n"), "match arm: expected type u32, got Bool") {
		t.Fatalf("incompatible expected arm errors = %v", errors)
	}
}

func TestInferredMatchRefusesImplicitUnionRepresentation(t *testing.T) {
	errors := checkAssignabilityProgram(`
bad: (pick_number: Bool): () {
  value := pick_number ? u32(1) | false
}
`)
	if len(errors) == 0 || !strings.Contains(strings.Join(errors, "\n"), "semantic join u32 | Bool has no implicit representation") {
		t.Fatalf("implicit union errors = %v", errors)
	}
}

func TestReturnAssignabilityPreservesRefinementDirection(t *testing.T) {
	errors := checkAssignabilityProgram(`
Small: type = u16 where value < u16(10)
erase: (value: Small): u16 = value
`)
	if len(errors) != 0 {
		t.Fatalf("refinement erasure rejected: %v", errors)
	}

	errors = checkAssignabilityProgram(`
Small: type = u16 where value < u16(10)
invent: (value: u16): Small = value
`)
	if len(errors) == 0 || !strings.Contains(strings.Join(errors, "\n"), "expected return type Small, got u16") {
		t.Fatalf("unchecked refinement return errors = %v", errors)
	}
}

func TestRuntimeAnyRemainsRestricted(t *testing.T) {
	errors := checkAssignabilityProgram(`
boxed: (value: u32): any = value
`)
	if len(errors) == 0 || !strings.Contains(strings.Join(errors, "\n"), "expected return type any, got u32") {
		t.Fatalf("implicit any representation errors = %v", errors)
	}
}
