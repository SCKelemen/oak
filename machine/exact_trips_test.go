package machine

import (
	"fmt"
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

func exactTripFixture(bottom, inclusive bool, reg asm.Register, start, bound, step int64) *asm.Function {
	var initial asm.Operand = imm(start)
	if start == 0 {
		initial = w(31)
		if reg.Class == asm.ClassX {
			initial = x(31)
		}
	}
	exit, again := "hs", "lo"
	if inclusive {
		exit, again = "hi", "ls"
	}
	items := []asm.Item{ins("mov", reg, initial)}
	if bottom {
		items = append(items, ins("cmp", reg, imm(bound)), bcond(exit, "done"))
	}
	items = append(items, label("loop"))
	if !bottom {
		items = append(items, ins("cmp", reg, imm(bound)), bcond(exit, "done"))
	}
	items = append(items, ins("add", w(10), w(10), imm(1)), ins("add", reg, reg, imm(step)))
	if bottom {
		items = append(items, ins("cmp", reg, imm(bound)), bcond(again, "loop"))
	} else {
		items = append(items, ins("b", sym("loop")))
	}
	items = append(items, label("done"), ins("mov", w(0), w(10)), ins("ret"))
	return fn(items...)
}

func exactTripShape(t *testing.T, function *asm.Function) *LoopShape {
	t.Helper()
	before := cloneFunction(function)
	shapes, err := LoopShapes(function)
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(function, before) {
		t.Fatal("exact-trip analysis mutated its input")
	}
	for _, shape := range shapes {
		if shape.Header == "loop" {
			return shape
		}
	}
	return nil
}

func TestExactTripsTopAndBottom(t *testing.T) {
	for _, bottom := range []bool{false, true} {
		for _, reg := range []asm.Register{w(9), x(9)} {
			for _, test := range []struct {
				start, bound, step int64
				inclusive          bool
				want               int
			}{
				{start: 0, bound: 7, step: 1, want: 7},
				{start: 0, bound: 8, step: 1, want: 8},
				{start: 2, bound: 10, step: 3, want: 3},
				{start: 0, bound: 10, step: 3, want: 4},
				{start: 1, bound: 7, step: 3, inclusive: true, want: 3},
				{start: 7, bound: 7, step: 1, inclusive: true, want: 1},
				{start: 0, bound: 0, step: 1, inclusive: true, want: 1},
			} {
				t.Run(fmt.Sprintf("bottom=%v/%s/%d-%d-step%d/inclusive=%v", bottom, reg.Text, test.start, test.bound, test.step, test.inclusive), func(t *testing.T) {
					shape := exactTripShape(t, exactTripFixture(bottom, test.inclusive, reg, test.start, test.bound, test.step))
					if shape == nil || shape.ExactTrips != test.want {
						t.Fatalf("shape %+v, want %d exact trips", shape, test.want)
					}
				})
			}
		}
	}
}

func TestExactTripsUsesActualExitNotFirstCompare(t *testing.T) {
	function := fn(
		ins("mov", w(9), w(31)), ins("cmp", w(9), imm(7)), bcond("hs", "done"),
		label("loop"),
		ins("cmp", w(9), imm(6)), bcond("hs", "skip"),
		ins("add", w(10), w(10), imm(2)),
		label("skip"),
		ins("add", w(9), w(9), imm(1)),
		ins("cmp", w(9), imm(7)), bcond("lo", "loop"),
		label("done"), ins("mov", w(0), w(10)), ins("ret"),
	)
	shape := exactTripShape(t, function)
	if shape == nil || shape.ExactTrips != 7 || shape.BoundImm != 6 || shape.MaxTrips != 6 {
		t.Fatalf("exact count must read the exit while preserving existing heuristic fields: %+v", shape)
	}
}

func TestExactTripsRejectsUncertainArithmetic(t *testing.T) {
	for _, bottom := range []bool{false, true} {
		for _, test := range []struct {
			name               string
			reg                asm.Register
			start, bound, step int64
			inclusive          bool
		}{
			{name: "zero-trips", reg: w(9), start: 7, bound: 7, step: 1},
			{name: "start-past-bound", reg: w(9), start: 8, bound: 7, step: 1},
			{name: "zero-step", reg: w(9), bound: 7},
			{name: "negative-step", reg: w(9), bound: 7, step: -1},
			{name: "negative-start", reg: w(9), start: -1, bound: 7, step: 1},
			{name: "negative-bound", reg: w(9), bound: -1, step: 1},
			{name: "oversized-start", reg: w(9), start: 1 << 32, bound: 7, step: 1},
			{name: "oversized-bound", reg: w(9), bound: 1 << 32, step: 1},
			{name: "oversized-step", reg: w(9), bound: 7, step: 1 << 32},
			{name: "final-word-wrap", reg: w(9), start: 1<<32 - 3, bound: 1<<32 - 1, step: 4},
			{name: "inclusive-word-wrap", reg: w(9), start: 1<<32 - 1, bound: 1<<32 - 1, step: 1, inclusive: true},
			{name: "trip-count-overflows-int", reg: x(9), bound: 1<<63 - 1, step: 1, inclusive: true},
		} {
			t.Run(fmt.Sprintf("bottom=%v/%s", bottom, test.name), func(t *testing.T) {
				shape := exactTripShape(t, exactTripFixture(bottom, test.inclusive, test.reg, test.start, test.bound, test.step))
				if shape != nil && shape.ExactTrips != 0 {
					t.Fatalf("uncertain arithmetic received exact trips: %+v", shape)
				}
			})
		}
	}
}

func TestExactTripsRejectsChangedInstructionShapes(t *testing.T) {
	for _, kind := range []string{"initial-width", "increment-width", "parameter-start", "movz-too-wide", "shifted-bound", "shifted-step", "register-bound", "signed-exit", "wrong-exit-direction", "flags-overwritten", "call", "system-wait", "extra-index-write"} {
		t.Run(kind, func(t *testing.T) {
			// A callee-saved index ensures a call refusal cannot depend only
			// on the call clobbering a caller-saved induction register.
			function := exactTripFixture(false, false, w(19), 0, 7, 1)
			function.Clobbers = append(function.Clobbers, x(19))
			switch kind {
			case "initial-width":
				function.Items[0] = ins("mov", x(19), x(31))
			case "increment-width":
				function.Items[5] = ins("add", x(19), x(19), imm(1))
			case "parameter-start":
				function.Items[0] = ins("mov", w(19), w(0))
			case "movz-too-wide":
				function.Items[0] = ins("movz", w(19), imm(1<<16))
			case "shifted-bound":
				function.Items[2] = ins("cmp", w(19), asm.Immediate{Value: 7, Shift: 12})
			case "shifted-step":
				function.Items[5] = ins("add", w(19), w(19), asm.Immediate{Value: 1, Shift: 12})
			case "register-bound":
				function.Items[2] = ins("cmp", w(19), w(1))
			case "signed-exit":
				function.Items[3] = bcond("ge", "done")
			case "wrong-exit-direction":
				function.Items[3] = bcond("lo", "done")
			case "flags-overwritten":
				items := append([]asm.Item(nil), function.Items[:3]...)
				items = append(items, ins("adds", w(10), w(10), imm(1)))
				function.Items = append(items, function.Items[3:]...)
			case "call":
				function.Items[4] = ins("bl", sym("callee"))
			case "system-wait":
				function.Items[4] = ins("wfi")
			case "extra-index-write":
				function.Items[4] = ins("mov", w(19), imm(2))
			}
			shape := exactTripShape(t, function)
			if shape != nil && shape.ExactTrips != 0 {
				t.Fatalf("unsupported instruction shape received exact trips: %+v", shape)
			}
		})
	}
}

func TestExactTripsRejectsIncompleteControlFlow(t *testing.T) {
	for _, kind := range []string{"early-exit", "early-return", "conditional-increment", "nested-cycle", "multiple-latches", "multiple-preheaders", "alternate-entry", "undominated-start", "increment-before-top-test"} {
		t.Run(kind, func(t *testing.T) {
			prefix := []asm.Item{ins("mov", w(9), w(31))}
			body := []asm.Item{ins("add", w(10), w(10), imm(1))}
			increment := []asm.Item{ins("add", w(9), w(9), imm(1)), ins("b", sym("loop"))}
			var extra []asm.Item
			switch kind {
			case "early-exit":
				body = append(body, ins("cbz", w(1), sym("done")))
			case "early-return":
				body = append(body, ins("cbz", w(1), sym("early")))
				extra = []asm.Item{label("early"), ins("ret")}
			case "conditional-increment":
				body = append(body, ins("cbz", w(1), sym("latch")))
				increment = []asm.Item{ins("add", w(9), w(9), imm(1)), label("latch"), ins("b", sym("loop"))}
			case "nested-cycle":
				body = []asm.Item{label("inner"), ins("add", w(10), w(10), imm(1)), ins("cbnz", w(1), sym("inner"))}
			case "multiple-latches":
				body = append(body, ins("cbz", w(1), sym("other-latch")))
				increment = append(increment, label("other-latch"), ins("add", w(9), w(9), imm(1)), ins("b", sym("loop")))
			case "multiple-preheaders":
				prefix = append(prefix, ins("cbz", w(1), sym("loop")), label("preheader"), ins("b", sym("loop")))
			case "alternate-entry":
				prefix = append(prefix, ins("cbz", w(1), sym("body")))
				body = append([]asm.Item{label("body")}, body...)
			case "undominated-start":
				prefix = []asm.Item{ins("cbz", w(1), sym("preheader")), ins("mov", w(9), w(31)), label("preheader")}
			case "increment-before-top-test":
				increment = []asm.Item{ins("b", sym("loop"))}
			}
			items := append(prefix, label("loop"))
			if kind == "increment-before-top-test" {
				items = append(items, ins("add", w(9), w(9), imm(1)))
			}
			items = append(items, ins("cmp", w(9), imm(7)), bcond("hs", "done"))
			items = append(items, body...)
			items = append(items, increment...)
			items = append(items, label("done"), ins("mov", w(0), w(10)), ins("ret"))
			items = append(items, extra...)
			shape := exactTripShape(t, fn(items...))
			if shape != nil && shape.ExactTrips != 0 {
				t.Fatalf("incomplete loop received exact trips: %+v", shape)
			}
		})
	}
}

func TestExactTripsDoesNotPromoteRemainderOrRV64Hints(t *testing.T) {
	function := fn(
		ins("mov", w(9), w(31)),
		label("main"), ins("cmp", w(9), w(20)), bcond("hi", "loop"),
		ins("add", w(9), w(9), imm(4)), ins("b", sym("main")),
		label("loop"), ins("cmp", w(9), w(20)), bcond("hs", "done"),
		ins("add", w(9), w(9), imm(1)), ins("b", sym("loop")),
		label("done"), ins("mov", w(0), w(9)), ins("ret"),
	)
	shape := exactTripShape(t, function)
	if shape == nil || shape.MaxTrips != 3 || shape.ExactTrips != 0 {
		t.Fatalf("pattern-derived remainder bound became exact: %+v", shape)
	}
	shape = exactTripShape(t, rvfn(
		ins("li", rx(5), imm(0)), ins("li", rx(6), imm(7)),
		label("loop"), ins("bgeu", rx(5), rx(6), sym("done")),
		ins("addi", rx(5), rx(5), imm(1)), ins("j", sym("loop")),
		label("done"), ins("ret"),
	))
	if shape == nil || shape.ExactTrips != 0 {
		t.Fatalf("AArch64 exact-trip analysis ran on RV64: %+v", shape)
	}
}

// A guard's branch into the trap block is not an exit the count reads: a
// counted loop whose body checks a bound (`cmp; b.hs trap`) or tests a
// register into the trap (`cbz`) trips as often as the loop without the
// guard, and the cost model charges both alike — the choice between a
// guarded body and one whose guards a proof removed must not read the
// guard as the loop ending early.
func TestExactTripsIgnoreTrapExits(t *testing.T) {
	for _, kind := range []string{"span-guard", "register-trap"} {
		t.Run(kind, func(t *testing.T) {
			function := exactTripFixture(false, false, w(9), 0, 16, 1)
			var guard []asm.Item
			switch kind {
			case "span-guard":
				guard = []asm.Item{ins("cmp", w(2), w(1)), bcond("hs", "trap")}
			case "register-trap":
				guard = []asm.Item{ins("cbz", w(1), sym("trap"))}
			}
			// The guard goes first in the body; the trap block after the return.
			items := append([]asm.Item{}, function.Items[:4]...)
			items = append(items, guard...)
			items = append(items, function.Items[4:]...)
			items = append(items, label("trap"), ins("brk", imm(0)))
			function.Items = items
			shape := exactTripShape(t, function)
			if shape == nil || shape.ExactTrips != 16 {
				t.Fatalf("a guarded counted loop keeps its exact trips: %+v", shape)
			}
		})
	}
}

