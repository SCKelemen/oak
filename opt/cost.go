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
	// Stalls estimate the cycles an in-order core waits for a producer
	// within a block (a load's result used the next instruction):
	// machine.StallEstimate.
	Stalls int

	LoopInstructions int
	LoopBranches     int
	LoopLoads        int
	LoopStores       int
	LoopGuards       int
	LoopStalls       int

	// LoopBodies are the loops in body order, each with its own items: a
	// nested loop's items are its own, not its outer loops', and the cost
	// model charges them by its trips times its outer loops' (Outer), as
	// they run that many times more.
	LoopBodies []LoopMetrics
}

// LoopMetrics are one loop's counts and what the body's shape says of its
// trips: Stride is how many elements one trip advances the loop's index
// (1 when unknown), read from the index register's increment, and
// MaxTrips estimates a trip bound from the recognized shape (including a
// smaller-vector cleanup after a wider main loop), 0 when unknown. It counts
// trips, not elements. Both are cost hints, not proof facts.
type LoopMetrics struct {
	Instructions int
	Branches     int
	Loads        int
	Stores       int
	Guards       int
	Stalls       int
	Stride       int
	MaxTrips     int
	// Depth is how many loops enclose this one; Outer the 1-based index
	// in LoopBodies of the innermost of them, 0 at the top level. An
	// inner loop's body runs its own trips for every trip of its outer
	// loops, so its items weigh the product (Estimate).
	Depth int
	Outer int
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
	if m.Stalls > 0 {
		parts = append(parts, fmt.Sprintf("stalls %d", m.Stalls))
	}
	for _, loop := range m.LoopBodies {
		shape := fmt.Sprintf("loop[%d instructions, %d branches, %d loads, %d stores, %d guards", loop.Instructions, loop.Branches, loop.Loads, loop.Stores, loop.Guards)
		if loop.Stalls > 0 {
			shape += fmt.Sprintf(", %d stalls", loop.Stalls)
		}
		if loop.Stride > 1 {
			shape += fmt.Sprintf(", stride %d", loop.Stride)
		}
		if loop.MaxTrips > 0 {
			shape += fmt.Sprintf(", <= %d trips", loop.MaxTrips)
		}
		if loop.Depth > 0 {
			shape += fmt.Sprintf(", depth %d", loop.Depth)
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
		{"stalls", before.Stalls, after.Stalls},
		{"loop instructions", before.LoopInstructions, after.LoopInstructions},
		{"loop branches", before.LoopBranches, after.LoopBranches},
		{"loop loads", before.LoopLoads, after.LoopLoads},
		{"loop guards", before.LoopGuards, after.LoopGuards},
		{"loop stalls", before.LoopStalls, after.LoopStalls},
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
// LoopWeight is the assumed scalar-iteration/element budget of a dynamic loop,
// and it decides how a bounded remainder loop weighs against the main
// loop it follows: at 32 trips a fifteen-trip tail is half the work, so a
// main loop strided sixteen ways could never pay for its tail. Calibrated
// to 256 from the reduction microbenchmark (2026-09-16,
// benchmarks/native/README.md "Reduction vectorization"): over 2^20 u32
// elements the sixteen-element vector form runs at 0.064 ns an element
// against the eight-element form's 0.106 and the scalar unrolling's
// 0.17, and only at 256 does the model order the three as measured. The
// loops Oak's workloads run — the kernels over 2^20 elements, the page
// tables' 2048, the frame scan's 64 MiB — are longer still; 256 is the
// conservative end of the range where the per-element term dominates the
// tail for every stride the compiler emits.
//
// straight-line code at weight one and a loop body at LoopWeight trips
// (fewer when its shape bounds them, divided by the elements one trip
// advances, multiplied by the trips of every loop around it), so a
// candidate that shortens a loop body by one instruction beats one that
// shortens the prologue by several, one that shortens an inner loop
// beats one that shortens its outer loop, and a wider trip pays per
// element. The weights are heuristics to be calibrated from
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
	Stall      float64 // one estimated stall cycle (machine.StallEstimate)
	LoopWeight float64
}

// AArch64Costs are the AArch64 lane's initial weights (an Apple M-series
// or Neoverse-class core: 4-cycle loads, 2-cycle multiplies, 10+ cycle
// divides, cheap predicted branches).
var AArch64Costs = TargetCosts{Arch: "arm64", Arithmetic: 1, Multiply: 3, Divide: 12, Load: 4, Store: 2, Branch: 1, Guard: 1.5, Call: 8, Stall: 0.5, LoopWeight: 256}

// RV64Costs are the RV64 lane's initial weights (an in-order or modest
// out-of-order core: slower multiplies and divides, fewer addressing
// modes so loads carry their address arithmetic separately).
var RV64Costs = TargetCosts{Arch: "rv64", Arithmetic: 1, Multiply: 4, Divide: 20, Load: 4, Store: 2, Branch: 1.5, Guard: 2, Call: 8, Stall: 1, LoopWeight: 256}

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
		float64(m.Calls)*t.Call +
		float64(m.Stalls)*t.Stall
	if len(m.LoopBodies) == 0 {
		loop := t.weigh(m.LoopInstructions-m.LoopBranches-m.LoopLoads-m.LoopStores, m.LoopBranches, m.LoopLoads, m.LoopStores, m.LoopGuards) + float64(m.LoopStalls)*t.Stall
		return total - loop + loop*weight
	}
	// The straight-line share is what no loop holds; the loop share is
	// each body at its own trip weight.
	inLoops := t.weigh(m.LoopInstructions-m.LoopBranches-m.LoopLoads-m.LoopStores, m.LoopBranches, m.LoopLoads, m.LoopStores, m.LoopGuards) + float64(m.LoopStalls)*t.Stall
	cost := total - inLoops
	// Each loop's own trips; a nested loop's body runs them for every
	// trip of its outer loops, so its factor is the product along the
	// chain (an inner loop's instruction weighs LoopWeight squared: a
	// probe loop inside a loop over probes runs its body that often).
	factors := make([]float64, len(m.LoopBodies))
	for k, loop := range m.LoopBodies {
		trips := weight
		// Convert the default element budget to trips before considering an
		// explicit trip bound. MaxTrips already includes the loop's stride.
		if loop.Stride > 1 {
			trips /= float64(loop.Stride)
		}
		if loop.MaxTrips > 0 && float64(loop.MaxTrips) < trips {
			// A bounded loop runs anywhere from none to its bound: its
			// expected trips, so a remainder loop after an unrolled main
			// loop is charged its share and not its worst case.
			trips = float64(loop.MaxTrips) / 2
		}
		factors[k] = trips
		if loop.Outer > 0 && loop.Outer-1 < k {
			factors[k] *= factors[loop.Outer-1]
		}
		cost += (t.weigh(loop.Instructions-loop.Branches-loop.Loads-loop.Stores, loop.Branches, loop.Loads, loop.Stores, loop.Guards) + float64(loop.Stalls)*t.Stall) * factors[k]
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
