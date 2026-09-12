package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Arrays of records through the native backend (docs/spec/94-assembler.md
// §9, eleventh increment): `pool: [N]Rec` locals and fields with computed
// element access — the element address derived under the constant index
// guard (`add xE, xB, wI, uxtw #s` for a power-of-two stride up to 16
// bytes, `movz`/`umaddl` otherwise) is a bounded region the checker
// admits field accesses through. The C backend's realization of the same
// program is the oracle, which also pins the element stride to C's.
const nativeRecordArrayProgram = `
Node: type = struct {
  value: u32
  next: u32
}

// A 12-byte record: the stride goes through umaddl.
Cell: type = struct {
  a: u32
  b: u32
  c: u32
}

Grid: type = struct {
  rows: [3]Cell
  count: u32
}

// A link pool walked by index: node i points at node next.
walk: (start: u32) -> u32 {
  pool: [4]Node
  pool[0] = Node { value: 10, next: 2 }
  pool[1] = Node { value: 20, next: 3 }
  pool[2] = Node { value: 30, next: 1 }
  pool[3] = Node { value: 40, next: 3 }
  i: u32 = start
  acc: u32 = u32(0)
  steps: u32 = u32(0)
  while steps < u32(3) {
    acc = acc + pool[i].value
    i = pool[i].next
    steps = steps + u32(1)
  }
  acc * u32(10) + i
}

// A field of a computed element updated in place, and a whole element read
// out into a local and passed on.
sum_cell: (c: Cell) -> u32 = c.a + c.b + c.c

fill_cells: (k: u32) -> u32 {
  cells: [3]Cell = [Cell { a: 1, b: 2, c: 3 }, Cell { a: 4, b: 5, c: 6 }, Cell { a: 7, b: 8, c: 9 }]
  i: u32 = u32(0)
  while i < len(cells) {
    cells[i].b = cells[i].b * k
    i = i + u32(1)
  }
  picked: Cell = cells[k]
  sum_cell(picked) * u32(100) + sum_cell(cells[u32(0)])
}

// An array of records inside a record, addressed by a computed index.
grid_total: (g: Grid) -> u32 {
  acc: u32 = u32(0)
  i: u32 = u32(0)
  while i < g.count {
    acc = acc + g.rows[i].a * g.rows[i].c
    i = i + u32(1)
  }
  acc
}

main: (): i32 {
  assert(walk(u32(0)) == u32(603))
  assert(fill_cells(u32(2)) == u32(3208))
  g: Grid = Grid { rows: [Cell { a: 1, b: 0, c: 2 }, Cell { a: 3, b: 0, c: 4 }, Cell { a: 5, b: 0, c: 6 }], count: u32(3) }
  assert(grid_total(g) == u32(44))
  g.rows[u32(1)].a = 10
  g.count = u32(2)
  assert(grid_total(g) == u32(42))
  42
}
`

func TestE2ENativeRecordArrays(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("record_arrays.oak", nativeRecordArrayProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_record_arrays", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native record arrays: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"walk", "sum_cell", "fill_cells", "grid_total", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_record_arrays_c", New().WithSource("record_arrays.oak", nativeRecordArrayProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_record_arrays_portable", New().WithSource("record_arrays.oak", nativeRecordArrayProgram).WithNativeBodies(), "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
		t.Fatalf("portable realization: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
