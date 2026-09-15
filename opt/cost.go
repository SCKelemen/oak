package opt

import (
	"fmt"
	"strings"
)

// Metrics are the structural measurements of one materialized body
// (docs/notes/optimizer-search-2026-09.md §9): the counts an optimization
// remark reports before and after, and the input of the cost model. The
// Loop* counts are the subset of each count inside some loop, and
// LoopBodies each loop's own counts, so a loop body weighs more than
// straight-line code and a wider trip less per element.
type Metrics struct {
	Instructions int
	Branches     int // conditional and unconditional branches, not calls or returns
	Loads        int
	Stores       int
	Calls        int
	Multiplies   int
	Divides      int
	// Guards are conditional branches to the body's trap block: bounds
	// checks, zero-divisor tests, and the other checks a proof may remove.
	Guards int
	Loops  int

	LoopInstructions int
	LoopBranches     int
	LoopLoads        int
	LoopStores       int
	LoopGuards       int

	// LoopBodies are the loops in body order; an inner loop's items count
	// in its outer loops too, as they run that many times more.
	LoopBodies []LoopMetrics
}

// LoopMetrics are one loop's counts and what the body's shape says of its
// trips: Stride is how many elements one trip advances the loop's index
// (1 when unknown), read from the index register's increment, and
// MaxTrips bounds the trips when the shape does (a remainder loop after a
// strided main loop over the same index runs fewer than the stride), 0
// when unbounded. Both are the cost model's hints, not facts.
type LoopMetrics struct {
	Instructions int
	Branches     int
	Loads        int
	Stores       int
	Guards       int
	Stride       int
	MaxTrips     int
}

// String spells the metrics in one line.
func (m Metrics) String() string {
	parts := []string{fmt.Sprintf("instructions %d", m.Instructions), fmt.Sprintf("branches %d", m.Branches), fmt.Sprintf("loads %d", m.Loads), fmt.Sprintf("stores %d", m.Stores)}
	if m.Calls > 0 {
		parts = append(parts, fmt.Sprintf("calls %d", m.Calls))
	}
	if m.Multiplies > 0 {
		parts = append(parts, fmt.Sprintf("multiplies %d", m.Multiplies))
	}
	if m.Divides > 0 {
		parts = append(parts, fmt.Sprintf("divides %d", m.Divides))
	}
	parts = append(parts, fmt.Sprintf("guards %d", m.Guards))
	for _, loop := range m.LoopBodies {
		shape := fmt.Sprintf("loop[%d instructions, %d branches, %d loads, %d stores, %d guards", loop.Instructions, loop.Branches, loop.Loads, loop.Stores, loop.Guards)
		if loop.Stride > 1 {
			shape += fmt.Sprintf(", stride %d", loop.Stride)
		}
		if loop.MaxTrips > 0 {
			shape += fmt.Sprintf(", <= %d trips", loop.MaxTrips)
		}
		parts = append(parts, shape+"]")
	}
	if m.Loops > 0 && len(m.LoopBodies) == 0 {
		parts = append(parts, fmt.Sprintf("loops %d (instructions %d, branches %d, loads %d, guards %d)", m.Loops, m.LoopInstructions, m.LoopBranches, m.LoopLoads, m.LoopGuards))
	}
	return strings.Join(parts, ", ")
}

// Delta spells the change from before to after, one row per count that
// moved, in the layout of the optimization report.
func Delta(before, after Metrics) string {
	rows := []struct {
		name   string
		before int
		after  int
	}{
		{"instructions", before.Instructions, after.Instructions},
		{"branches", before.Branches, after.Branches},
		{"loads", before.Loads, after.Loads},
		{"stores", before.Stores, after.Stores},
		{"calls", before.Calls, after.Calls},
		{"multiplies", before.Multiplies, after.Multiplies},
		{"divides", before.Divides, after.Divides},
		{"guards", before.Guards, after.Guards},
		{"loop instructions", before.LoopInstructions, after.LoopInstructions},
		{"loop branches", before.LoopBranches, after.LoopBranches},
		{"loop loads", before.LoopLoads, after.LoopLoads},
		{"loop guards", before.LoopGuards, after.LoopGuards},
	}
	var out []string
	for _, row := range rows {
		if row.before != row.after {
			out = append(out, fmt.Sprintf("%-18s %d -> %d", row.name+":", row.before, row.after))
		}
	}
	if len(out) == 0 {
		return "unchanged"
	}
	return strings.Join(out, "\n")
}

// CostModel estimates a body's cost from its metrics. Cost is not
// correctness (docs/notes/optimizer-search-2026-09.md §8): the model
// chooses among admitted candidates and is outside the trusted base.
type CostModel interface {
	Name() string
	Estimate(m Metrics) float64
}

// TargetCosts is the first target-cost model: static per-class weights,
// straight-line code at weight one and a loop body at LoopWeight trips
// (fewer when its shape bounds them, divided by the elements one trip
// advances), so a candidate that shortens a loop body by one instruction
// beats one that shortens the prologue by several, and a wider trip pays
// per element. The weights are heuristics to be calibrated from
// microbenchmarks; nothing semantic depends on them.
type TargetCosts struct {
	Arch       string
	Arithmetic float64 // any instruction not otherwise classed
	Multiply   float64
	Divide     float64
	Load       float64
	Store      float64
	Branch     float64
	Guard      float64 // a conditional branch to the trap: predicted, but a compare and a branch
	Call       float64
	LoopWeight float64
}

// AArch64Costs are the AArch64 lane's initial weights (an Apple M-series
// or Neoverse-class core: 4-cycle loads, 2-cycle multiplies, 10+ cycle
// divides, cheap predicted branches).
var AArch64Costs = TargetCosts{Arch: "arm64", Arithmetic: 1, Multiply: 3, Divide: 12, Load: 4, Store: 2, Branch: 1, Guard: 1.5, Call: 8, LoopWeight: 32}

// RV64Costs are the RV64 lane's initial weights (an in-order or modest
// out-of-order core: slower multiplies and divides, fewer addressing
// modes so loads carry their address arithmetic separately).
var RV64Costs = TargetCosts{Arch: "rv64", Arithmetic: 1, Multiply: 4, Divide: 20, Load: 4, Store: 2, Branch: 1.5, Guard: 2, Call: 8, LoopWeight: 32}

// CostsFor returns the lane's weights; an unknown lane gets AArch64's.
func CostsFor(arch string) TargetCosts {
	if arch == "rv64" {
		return RV64Costs
	}
	return AArch64Costs
}

// Name identifies the model in remarks.
func (t TargetCosts) Name() string { return "static-" + t.Arch }

// Estimate is the weighted sum of the metrics: straight-line code at
// weight one, each loop body at LoopWeight per trip — bounded by the trips
// its shape allows, divided by the elements a trip advances — so a loop
// unrolled four ways counts a quarter per element and its remainder loop
// counts its few trips, not a loop's weight. Without per-loop bodies the
// aggregate loop counts weigh LoopWeight.
func (t TargetCosts) Estimate(m Metrics) float64 {
	weight := t.LoopWeight
	if weight < 1 {
		weight = 1
	}
	classed := m.Branches + m.Loads + m.Stores + m.Calls + m.Multiplies + m.Divides
	total := t.weigh(m.Instructions-classed, m.Branches, m.Loads, m.Stores, m.Guards) +
		float64(m.Multiplies)*t.Multiply +
		float64(m.Divides)*t.Divide +
		float64(m.Calls)*t.Call
	if len(m.LoopBodies) == 0 {
		loop := t.weigh(m.LoopInstructions-m.LoopBranches-m.LoopLoads-m.LoopStores, m.LoopBranches, m.LoopLoads, m.LoopStores, m.LoopGuards)
		return total - loop + loop*weight
	}
	// The straight-line share is what no loop holds; the loop share is
	// each body at its own trip weight.
	inLoops := t.weigh(m.LoopInstructions-m.LoopBranches-m.LoopLoads-m.LoopStores, m.LoopBranches, m.LoopLoads, m.LoopStores, m.LoopGuards)
	cost := total - inLoops
	for _, loop := range m.LoopBodies {
		trips := weight
		if loop.MaxTrips > 0 && float64(loop.MaxTrips) < trips {
			// A bounded loop runs anywhere from none to its bound: its
			// expected trips, so a remainder loop after an unrolled main
			// loop is charged its share and not its worst case.
			trips = float64(loop.MaxTrips) / 2
		}
		if loop.Stride > 1 {
			trips /= float64(loop.Stride)
		}
		cost += t.weigh(loop.Instructions-loop.Branches-loop.Loads-loop.Stores, loop.Branches, loop.Loads, loop.Stores, loop.Guards) * trips
	}
	return cost
}

// weigh prices the plain instruction classes; a guard is a branch already
// counted, plus its compare.
func (t TargetCosts) weigh(other, branches, loads, stores, guards int) float64 {
	if other < 0 {
		other = 0
	}
	return float64(other)*t.Arithmetic +
		float64(loads)*t.Load +
		float64(stores)*t.Store +
		float64(branches)*t.Branch +
		float64(guards)*(t.Guard-t.Branch)
}
