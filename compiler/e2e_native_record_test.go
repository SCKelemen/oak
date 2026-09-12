package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Record locals through the native backend (docs/spec/94-assembler.md §9,
// sixth increment): a declared record type is placed by
// semir.RecordLayoutWithSpec — the numbers the C backend asserts against the
// C compiler — and a local of that type lives in the frame; fields are read
// and written at their own width and offset (a Bool field is the 4-byte C
// enum), a record copies slot-wise. The C backend's realization of the same
// program is the oracle.
const nativeRecordProgram = `
Point: type = struct {
  x: i32
  y: i32
}

Mixed: type = struct {
  tag: u8
  count: u16
  flag: Bool
  big: u64
  ratio: f64
}

manhattan: (dx: i32, dy: i32) -> i32 {
  p: Point = Point { x: dx, y: dy }
  p.x < i32(0) ? { p.x = -p.x } | { }
  p.y < i32(0) ? { p.y = -p.y } | { }
  p.x + p.y
}

// Narrow fields updated in a loop, a Bool field written from a comparison
// and read as a condition.
accumulate: (n: u32) -> u64 {
  m: Mixed = Mixed { tag: u8(7), count: u16(0), flag: false, big: u64(0), ratio: 0.5 }
  i: u32 = u32(0)
  while i < n {
    m.count = m.count + u16(1)
    m.big = m.big + u64(m.count)
    i = i + u32(1)
  }
  m.flag = m.count == u16_trunc_u32(n)
  m.flag ? m.big + u64(m.tag) | u64(0)
}

// A copy is a distinct value.
copy_point: () -> i32 {
  p: Point = Point { x: 3, y: 4 }
  q: Point = p
  q.x = 10
  p.x * 100 + q.x + q.y
}

// Whole-record assignment.
swap_in: () -> i32 {
  a: Point = Point { x: 1, y: 2 }
  b: Point = Point { x: 30, y: 40 }
  a = b
  b.y = 5
  a.x + a.y + b.y
}

scaled: () -> f64 {
  m: Mixed = Mixed { tag: u8(0), count: u16(0), flag: true, big: u64(1), ratio: 0.5 }
  m.ratio = m.ratio * 4.0
  m.ratio + f64_round_u64(m.big)
}

main: (): i32 {
  assert(manhattan(-3, 4) == 7)
  assert(manhattan(3, -4) == 7)
  assert(accumulate(u32(4)) == u64(17))
  assert(accumulate(u32(0)) == u64(7))
  assert(copy_point() == 314)
  assert(swap_in() == 75)
  assert(scaled() == 3.0)
  42
}
`

func TestE2ENativeRecords(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("records.oak", nativeRecordProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_records", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native records: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"manhattan", "accumulate", "copy_point", "swap_in", "scaled", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	for _, fn := range []string{"manhattan", "copy_point", "swap_in"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s must be proven equal to its Oak body (record locals as aggregates, tiled frame slots); diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_records_c", New().WithSource("records.oak", nativeRecordProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_records_portable", New().WithSource("records.oak", nativeRecordProgram).WithNativeBodies(), "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
		t.Fatalf("portable realization: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
