package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Spans and views of records through the native backend
// (docs/spec/94-assembler.md §9, twelfth increment): `pool: []Node` and
// `[*]Node` parameters and locals, elements addressed through the span
// element idiom (the index guarded against the length register, then
// `add xE, xB, wI, uxtw #s` or `movz`/`umaddl` by the record's stride),
// writable only through a span. The C backend's realization of the same
// program is the oracle.
const nativeRecordSpanProgram = `
Node: type = struct {
  value: u32
  next: u32
}

Cell: type = struct {
  a: u32
  b: u32
  c: u32
}

// A link pool passed as a view and walked by index.
walk: (pool: []Node, start: u32, steps: u32) -> u32 {
  i: u32 = start
  acc: u32 = u32(0)
  k: u32 = u32(0)
  while k < steps {
    acc = acc + pool[i].value
    i = pool[i].next
    k = k + u32(1)
  }
  acc * u32(10) + i
}

// A span of 12-byte records filled in place (umaddl stride), an element
// replaced whole, and one read out.
renumber: (cells: [*]Cell, k: u32) -> u32 {
  i: u32 = u32(0)
  while i < len(cells) {
    cells[i].b = cells[i].a * k
    i = i + u32(1)
  }
  cells[u32(1)] = Cell { a: 100, b: 200, c: 300 }
  last: Cell = cells[len(cells) - u32(1)]
  last.a + last.b + last.c
}

sum_b: (cells: []Cell) -> u32 {
  acc: u32 = u32(0)
  i: u32 = u32(0)
  while i < len(cells) {
    acc = acc + cells[i].b
    i = i + u32(1)
  }
  acc
}

// A subslice over a record view (8-byte stride) walked by a leaf.
tail_values: (pool: []Node) -> u32 {
  rest: []Node = subslice(pool, u32(1), len(pool) - u32(1))
  walk(rest, u32(1), u32(2))
}

main: (): i32 {
  pool: [4]Node = [Node { value: 10, next: 2 }, Node { value: 20, next: 3 }, Node { value: 30, next: 1 }, Node { value: 40, next: 0 }]
  assert(walk(view(&pool), u32(0), u32(3)) == u32(603))
  cells: [3]Cell = [Cell { a: 1, b: 0, c: 3 }, Cell { a: 4, b: 0, c: 6 }, Cell { a: 7, b: 0, c: 9 }]
  assert(renumber(span(&cells), u32(2)) == u32(30))
  assert(sum_b(view(&cells)) == u32(216))
  assert(tail_values(view(&pool)) == u32(601))
  42
}
`

func TestE2ENativeRecordSpans(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("record_spans.oak", nativeRecordSpanProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_record_spans", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native record spans: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"walk", "renumber", "sum_b", "tail_values", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_record_spans_c", New().WithSource("record_spans.oak", nativeRecordSpanProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_record_spans_portable", New().WithSource("record_spans.oak", nativeRecordSpanProgram).WithNativeBodies(), "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
		t.Fatalf("portable realization: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
