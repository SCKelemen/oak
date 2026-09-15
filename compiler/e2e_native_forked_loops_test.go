package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A fork whose two sides each run a loop, then a loop both sides reach:
// the machine's paths run the sides one after the other, and without a
// join the first side runs on through the shared loop before the other
// side's loop is summarized — the loop events then stand in another
// order than the Oak body lowers them (sides first, then what follows),
// and the coupling, which pairs the k-th event of each side, sees the
// loops nesting differently. The executor now notices sibling events out
// of layout order and runs again merging at the joins (the guards' trap
// paths not counted against a meeting point), so the events are
// numbered as the Oak side's and the three loops couple
// (docs/spec/94-assembler.md §8, "count and find_from").
const nativeForkedLoopsProgram = `
weigh: (a: []u32, n: u32, flag: u32): u32 {
  acc: u32 = u32(0)
  i: u32 = u32(0)
  flag == u32(0) ? {
    while i < n && i < len(a) {
      acc = acc + a[i]
      i = i + u32(1)
    }
  } | {
    while i < n && i < len(a) {
      acc = acc + u32(2) * a[i]
      i = i + u32(1)
    }
  }
  j: u32 = u32(0)
  while j < n {
    acc = acc + j
    j = j + u32(1)
  }
  acc
}

main: (): i32 {
  xs: [4]u32 = [u32(1), u32(2), u32(3), u32(4)]
  assert(weigh(view(&xs), u32(4), u32(0)) == u32(16))
  assert(weigh(view(&xs), u32(4), u32(1)) == u32(26))
  42
}
`

func TestE2ENativeForkedLoopsOrder(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("forked.oak", nativeForkedLoopsProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_forked_loops", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("forked loops: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if !strings.Contains(joined, "asm unit weigh: proven equal to its Oak body at the bit level — 3 data-dependent loops coupled inductively") {
		t.Errorf("weigh's three loops must couple in the Oak body's order; diagnostics:\n%s", joined)
	}
}
