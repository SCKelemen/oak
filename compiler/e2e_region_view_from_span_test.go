package compiler

import (
	"strings"
	"testing"
)

// A ring buffer read in place (docs/spec/50-borrowing.md section 8c,
// increment 5): run returns a read-only view of the visible slots of one
// ring behind a span parameter, and the consumer reads it without a copy,
// then releases the run. The returned view is an array field of an
// element of the span — `view(&s[dom].slots)[h:end]` — and at the caller
// it is a reborrow of the span argument, which is suspended while it lives.
const regionViewFromSpanProgram = `
Ring: type = struct {
  head: u64
  tail: u64
  slots: [16]u64
}

run[R]: (s: Span[Ring, R], dom: u32): View[u64, R] {
  h: u64 = s[dom].head & u64(15)
  end: u64 = h + (s[dom].tail - s[dom].head)
  end > u64(16) ? { end = u64(16) }
  view(&s[dom].slots)[u32_trunc_u64(h):u32_trunc_u64(end)]
}

release: (s: [*]Ring, dom: u32, n: u64): () {
  s[dom].head = s[dom].head + n
}

drain_sum: (s: [*]Ring, dom: u32): u64 {
  total: u64 = u64(0)
  taken: u64 = u64(0)
  {
    r: []u64 = run(s, dom)
    i: u32 = u32(0)
    while i < len(r) {
      total = total + r[i]
      i = i + u32(1)
    }
    taken = u64(len(r))
  }
  release(s, dom, taken)
  total
}

main: (): i32 {
  rings: [2]Ring
  i: u32 = u32(0)
  while i < u32(8) { rings[1].slots[i] = u64(i) + u64(1); i = i + u32(1) }
  rings[1].tail = u64(8)
  sum: u64 = drain_sum(span(&rings), u32(1))
  assert(rings[1].head == u64(8))
  assert(drain_sum(span(&rings), u32(1)) == u64(0))
  i32_bits_u32(u32_trunc_u64(sum) + u32(6))
}
`

func TestE2ERegionViewFromSpan(t *testing.T) {
	output, err := New().WithSource("ring.oak", regionViewFromSpanProgram).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	// The view is the slots' own storage: no copy into a buffer.
	if !strings.Contains(output, ".slots.v") {
		t.Fatalf("run does not return a view of the slots in place:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "ring_view", regionViewFromSpanProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if interpreted := interpretChecked(t, regionViewFromSpanProgram); interpreted != 42 {
		t.Fatalf("interpreter returned %d", interpreted)
	}
}

func TestRegionViewFromSpanRejections(t *testing.T) {
	run := `
Ring: type = struct { head: u64, tail: u64, slots: [16]u64 }
run[R]: (s: Span[Ring, R], dom: u32): View[u64, R] = view(&s[dom].slots)
`
	cases := []struct{ name, src, want string }{
		{"span written while the view lives", run + `
use: (s: [*]Ring): u64 {
  r: []u64 = run(s, 0)
  s[0].head = 1
  r[0]
}
main: (): i32 { 0 }`, "OAK-B0107"},
		{"write through the returned view", run + `
use: (s: [*]Ring): () {
  r: []u64 = run(s, 0)
  r[0] = 1
}
main: (): i32 { 0 }`, "read-only view"},
		{"view of a local in a span region", `
local_run[R]: (s: Span[u64, R]): View[u64, R] {
  local: [4]u64 = [4]u64{ 1, 2, 3, 4 }
  view(&local)
}
main: (): i32 { 0 }`, "OAK-B0113"},
		{"view of another parameter", `
Ring: type = struct { head: u64, tail: u64, slots: [16]u64 }
pick[R]: (s: Span[Ring, R], other: [*]Ring): View[u64, R] = view(&other[0].slots)
main: (): i32 { 0 }`, "OAK-B0113"},
	}
	for _, c := range cases {
		_, err := New().WithSource("reject.oak", c.src).Check().Get()
		if err == nil || !strings.Contains(err.Error(), c.want) {
			t.Fatalf("%s: err = %v, want %q", c.name, err, c.want)
		}
	}
}
