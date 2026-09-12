package compiler

import (
	"strings"
	"testing"
)

// Stateful reductions (docs/spec/55-parallelism.md section 4, the ml
// pilot's F2/F3): an order is a function. fold is the sequential order with
// a state, tree_map the binary-counter order over lifted elements, and for
// an associative merge the two are one value (Oak.Reduce.fold_eq_tree_map).
// The merge here is the running (max, count-of-max) of a window — the shape
// of the online-softmax merge, over integers so the check is exact.
const reduceStateProgram = `package main

r := import("reduce")

Top: type = struct { m: i32, c: u32 }

lift: (x: i32): Top effects { } = Top { m: x, c: 1 }

merge: (a: Top, b: Top): Top effects { } =
  a.m > b.m ? a | b.m > a.m ? b | Top { m: a.m, c: a.c + b.c }

step: (s: Top, x: i32): Top effects { } = merge(s, lift(x))

add_wide: (acc: i64, x: i32): i64 effects { } = acc + i64(x)

main: (): i32 = {
  xs: [7]i32 = [3, 9, -2, 9, 4, 9, 1]
  v: []i32 = view(&xs)
  seq: Top = r.fold(v, lift(v[0]), step)
  tree: Top = r.tree_map(v, Top { m: 0, c: 0 }, lift, merge)
  sum: i64 = r.fold(v, i64(0), add_wide)
  seq.m != 9 ? 10 | seq.c != 3 ? 11 | tree.m != 9 ? 12 | tree.c != 3 ? 13 | sum != 33 ? 14 | 42
}
`

func TestE2EReduceFoldAndTreeMap(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": reduceStateProgram})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	// A step that performs an effect is not a fold step.
	bad := strings.Replace(reduceStateProgram, "step: (s: Top, x: i32): Top effects { } = merge(s, lift(x))",
		"host_read: (x: c.UInt32): c.UInt32 effects { Host.Read } = c.extern(\"oak_host_read\")\nstep: (s: Top, x: i32): Top = merge(s, lift(x + i32_bits_u32(u32(host_read(c.UInt32(0))))))", 1)
	root = writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": bad})
	_, err := New().WithPackageDir(root).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "OAK-E0105") {
		t.Fatalf("an effectful step must fail the empty row: %v", err)
	}
}
