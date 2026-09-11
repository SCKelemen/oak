package compiler

import "testing"

// defer (docs/spec/10-syntax.md section 4b): deferred statements run at
// the end of the enclosing block in reverse order, after the block's value
// is computed, at the end of every loop iteration, and before a break
// leaves the block; the statement is evaluated when it runs.
const deferProgram = `
main: (): i32 {
  acc: u32 = u32(0)
  ok: Bool = true
  ok ? {
    defer acc = acc * u32(10) + u32(1)
    defer acc = acc * u32(10) + u32(2)
    acc = acc * u32(10) + u32(3)
  } | { }
  assert(acc == u32(321))

  before: u32 = acc
  doubled: u32 = ok ? {
    defer acc = acc + u32(1)
    acc * u32(2)
  } | { u32(0) }
  assert(doubled == before * u32(2))
  assert(acc == before + u32(1))

  i: u32 = u32(0)
  hits: u32 = u32(0)
  while i < u32(3) {
    defer i = i + u32(1)
    hits = hits + u32(1)
  }
  assert(i == u32(3))
  assert(hits == u32(3))

  j: u32 = u32(0)
  while true {
    defer j = j + u32(100)
    j = j + u32(1)
    j > u32(200) ? { break } | { }
  }
  assert(j == u32(303))

  late: u32 = u32(1)
  ok ? {
    defer acc = acc + late
    late = u32(50)
  } | { }
  assert(acc == before + u32(51))
  42
}
`

func TestE2EDeferInterpreted(t *testing.T) {
	if got := interpretChecked(t, deferProgram); got != 42 {
		t.Fatalf("interpreter returned %d, want 42", got)
	}
}

func TestE2EDeferCompiled(t *testing.T) {
	code, abnormal := buildAndRun(t, "defer", deferProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
