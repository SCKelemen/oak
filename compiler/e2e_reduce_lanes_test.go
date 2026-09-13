package compiler

import (
	"strings"
	"testing"
)

// The lane rule as an order (docs/spec/55-parallelism.md section 4; the ml
// pilot's F2): reduce.lanes folds element i into lane (i / run) % count in
// index order from zero and combines the lanes through the xor butterfly,
// lane 0's value the result. One lane is reduce.left; a non-commutative
// combine pins the grouping; over floats the lane rule, the tree, and the
// chain are three values on one input, each the same bits in the
// interpreter and the C.
const lanesProgram = `package main

r := import("reduce")

// combine is not commutative or associative, so the grouping shows in the value.
combine: (a: u32, b: u32): u32 = a * 31 + b
plus: (a: f32, b: f32): f32 laws { associative, commutative, identity(0.0) } = a + b

main: (): i32 = {
  xs: [8]u32 = [1, 2, 3, 4, 5, 6, 7, 8]
  fs: [5]f32 = [16777216.0, 1.0, 1.0, 1.0, 1.0]
  zero: f32 = 0.0
  // Four lanes, runs of one: lane l folds xs[l], xs[l + 4] from 0.
  l0: u32 = combine(combine(0, 1), 5)
  l1: u32 = combine(combine(0, 2), 6)
  l2: u32 = combine(combine(0, 3), 7)
  l3: u32 = combine(combine(0, 4), 8)
  // The butterfly at offsets 2 then 1: (l0 with l2, l1 with l3), then those two.
  four: u32 = combine(combine(l0, l2), combine(l1, l3))
  got4: u32 = r.lanes(view(&xs), u32(0), combine, 4, 1)
  // Two lanes, runs of two: lane 0 folds xs[0], xs[1], xs[4], xs[5].
  m0: u32 = combine(combine(combine(combine(0, 1), 2), 5), 6)
  m1: u32 = combine(combine(combine(combine(0, 3), 4), 7), 8)
  got22: u32 = r.lanes(view(&xs), u32(0), combine, 2, 2)
  // One lane is the left fold.
  one: u32 = r.lanes(view(&xs), u32(0), combine, 1, 1)
  lft: u32 = r.left(view(&xs), u32(0), combine)
  // Floats: 2^24 + 1 rounds to 2^24; the three orders are three values.
  laned: f32 = r.lanes(view(&fs), zero, plus, 4, 1)
  treed: f32 = r.tree(view(&fs), zero, plus)
  chained: f32 = 0.0
  order bounded {
    chained = r.reduce(view(&fs), zero, plus)
  }
  // Zero starts every lane: an empty view is the butterfly of eight sevens.
  empty: [0]f32 = []
  seven: f32 = 7.0
  none: f32 = r.lanes(view(&empty), seven, plus, 8, 3)
  got4 == four && got22 == combine(m0, m1) && one == lft && laned == 16777218.0 && treed == 16777220.0 && chained == 16777216.0 && none == 56.0 ? 42 | 1
}
`

func TestE2EReduceLanes(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": lanesProgram})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	emitted, err := New().WithPackageDir(root).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"oak_reduce__lanes_u32(", "oak_reduce__lanes_f32(", "oak_reduce__lane_uof("} {
		if !strings.Contains(emitted, want) {
			t.Fatalf("missing %q in the C:\n%s", want, emitted)
		}
	}
	// The lane count is a power of two, at most 256, and the run is positive.
	for name, args := range map[string]string{"three lanes": "3, 1", "too many": "512, 1", "no run": "4, 0"} {
		bad := strings.Replace(lanesProgram, "r.lanes(view(&xs), u32(0), combine, 4, 1)", "r.lanes(view(&xs), u32(0), combine, "+args+")", 1)
		root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": bad})
		if code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root)); !abnormal && code == 42 {
			t.Fatalf("%s must trap, got exit %d", name, code)
		}
	}
}
