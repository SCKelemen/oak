package machine

import (
	"fmt"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

// Compare the hint with direct loop execution, independently of the closed
// form used by the recognizer. Small values keep both W and X arithmetic
// nonwrapping while covering empty loops, nonzero starts, inclusive bounds,
// uneven strides, and the generator's top- and bottom-tested spellings.
func TestExactTripsAgainstExecution(t *testing.T) {
	cases := 0
	for _, bottom := range []bool{false, true} {
		for _, inclusive := range []bool{false, true} {
			for _, register := range []asm.Register{w(9), x(9)} {
				t.Run(fmt.Sprintf("bottom=%v/inclusive=%v/%s", bottom, inclusive, register.Text), func(t *testing.T) {
					for start := int64(0); start < 6; start++ {
						for bound := int64(0); bound < 13; bound++ {
							for step := int64(1); step < 6; step++ {
								want := 0
								for index := start; index < bound || (inclusive && index == bound); index += step {
									want++
								}
								body := exactTripFixture(bottom, inclusive, register, start, bound, step)
								shape := exactTripShape(t, body)
								if shape == nil || shape.ExactTrips != want {
									t.Fatalf("start=%d bound=%d step=%d: shape=%+v, executed %d trips", start, bound, step, shape, want)
								}
								cases++
							}
						}
					}
				})
			}
		}
	}
	if cases != 3120 {
		t.Fatalf("exercised %d cases, want 3120", cases)
	}
}
