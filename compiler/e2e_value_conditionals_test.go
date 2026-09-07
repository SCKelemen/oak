package compiler

import "testing"

// Conditionals are expressions (docs/spec/10-syntax.md §3a): the else
// branch is first-class in value positions. Return-position Bool matches
// lower to C if/else with both branches returning; expression branches in
// value position lower to a single-evaluation ternary; statement-bearing
// block branches in initializers hoist to declaration + branch assignment.

func TestE2EValueConditionals(t *testing.T) {
	cases := map[string]struct {
		src  string
		want int
	}{
		"return position, block arms": {`
sign: (n: i32): i32 = n < 0 ? { 0 - 1 } | { 1 }

main: (): i32 = sign(0 - 5) + sign(9) + 40
`, 40},
		"return position, expr arms": {`
sign: (n: i32): i32 = n < 0 ? 0 - 1 | 1

main: (): i32 = sign(0 - 5) + sign(9) + 40
`, 40},
		"initializer, expr arms": {`
main: (): i32 {
  n: i32 = 7
  s: i32 = n < 0 ? 0 - 1 | 1
  s + 41
}
`, 42},
		"initializer, block arms with statements": {`
main: (): i32 {
  n: i32 = 7
  s: i32 = n < 0 ? {
    penalty: i32 = 2
    0 - penalty
  } | {
    bonus: i32 = 3
    bonus + 1
  }
  s + 39
}
`, 43},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			code, abnormal := buildAndRun(t, "valcond", tc.src)
			if abnormal || code != tc.want {
				t.Fatalf("exit = (%d, abnormal=%v), want %d", code, abnormal, tc.want)
			}
		})
	}
}
