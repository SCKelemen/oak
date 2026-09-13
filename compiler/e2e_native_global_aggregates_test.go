package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Package-global records and arrays through the native backend (the OS
// pilot's N9: `table.slots[slot].field`, `marks[i] = v`). A top-level
// record or written array is addressed storage: `adrp`/`add :lo12:` name
// it, and it is a record or array place at that address — fields at
// their offsets, elements under the constant guard — which the checker
// bounds as a region of the aggregate's size. The functions lower
// natively and agree with the C backend.
const nativeGlobalAggregatesProgram = `
Slot: type = struct { slot: u32, owner: u32 }
Table: type = struct { slots: [8]Slot, count: u32 }

table: Table
marks: [16]u32
depth: u32 = u32(0)

lookup: (i: u32): u32 {
  i < u32(8) ? { table.slots[i].slot + table.count } | { u32(0) }
}

mark: (i: u32, v: u32): () {
  i < u32(16) ? {
    marks[i] = v
    table.count = table.count + u32(1)
    depth = depth + u32(1)
  } | { }
}

place: (i: u32, s: u32, o: u32): () {
  i < u32(8) ? { table.slots[i].slot = s; table.slots[i].owner = o } | { }
}

main: (): i32 {
  mark(u32(3), u32(40))
  place(u32(2), u32(5), u32(9))
  a: u32 = lookup(u32(2))            // 5 + 1
  // 6 + 40 + 9 + 1 = 56
  i32_bits_u32(a + marks[u32(3)] + table.slots[u32(2)].owner + depth)
}
`

func TestE2ENativeGlobalAggregates(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("aggregates.oak", nativeGlobalAggregatesProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_aggregates", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 56 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 56\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"lookup", "mark", "place", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s must lower natively over package-global aggregates; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_aggregates_c", New().WithSource("aggregates.oak", nativeGlobalAggregatesProgram)); abnormal || code != 56 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 56", code, abnormal)
	}
}
