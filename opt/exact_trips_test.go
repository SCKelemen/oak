package opt

import (
	"strings"
	"testing"
)

func TestCostDistinguishesExactAndBoundedTrips(t *testing.T) {
	costs := TargetCosts{Arithmetic: 1, LoopWeight: 256}
	for _, stride := range []int{1, 2, 4, 8} {
		for _, trips := range []int{1, 8, 512} {
			m := Metrics{Instructions: 10, LoopInstructions: 10, Loops: 1,
				LoopBodies: []LoopMetrics{{Instructions: 10, Stride: stride, MaxTrips: trips, ExactTrips: trips}}}
			if got, want := costs.Estimate(m), float64(10*trips); got != want {
				t.Fatalf("stride=%d exact=%d cost=%v, want %v", stride, trips, got, want)
			}
		}
		m := Metrics{Instructions: 10, LoopInstructions: 10, Loops: 1,
			LoopBodies: []LoopMetrics{{Instructions: 10, Stride: stride, MaxTrips: 8}}}
		if got := costs.Estimate(m); got != 40 {
			t.Fatalf("upper bound changed policy: stride=%d cost=%v, want 40", stride, got)
		}
		m.LoopBodies[0].MaxTrips = 0
		if got, want := costs.Estimate(m), 2560/float64(stride); got != want {
			t.Fatalf("unknown trips changed policy: stride=%d cost=%v, want %v", stride, got, want)
		}
	}
}

func TestCostMultipliesNestedExactTrips(t *testing.T) {
	m := Metrics{Instructions: 16, LoopInstructions: 12, Loops: 2,
		LoopBodies: []LoopMetrics{
			{Instructions: 5, ExactTrips: 3},
			{Instructions: 7, ExactTrips: 8, Depth: 1, Outer: 1},
		}}
	if got, want := (TargetCosts{Arithmetic: 1, LoopWeight: 256}).Estimate(m), float64(4+5*3+7*3*8); got != want {
		t.Fatalf("nested exact cost=%v, want %v", got, want)
	}
}

func TestExactTripMetricsDescribeAndFreeze(t *testing.T) {
	m := Metrics{LoopBodies: []LoopMetrics{{MaxTrips: 8, ExactTrips: 8}}}
	if text := m.String(); !strings.Contains(text, "exactly 8 trips") || strings.Contains(text, "<= 8 trips") {
		t.Fatalf("exact count is not distinguished: %s", text)
	}
	frozen := freezeMetrics(m)
	m.LoopBodies[0].ExactTrips = 1
	if frozen.LoopBodies[0].ExactTrips != 8 {
		t.Fatal("artifact snapshot aliased exact-trip metrics")
	}
	m.LoopBodies[0].ExactTrips = 0
	if !strings.Contains(m.String(), "<= 8 trips") {
		t.Fatal("unknown exact count hid the separate upper bound")
	}
}
