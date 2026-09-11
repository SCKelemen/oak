package compiler

import (
	"strings"
	"testing"
)

// `break` leaves the innermost while (docs/spec/85-discipline.md section 3):
// from a conditional arm, out of an inner loop only, and out of a bounded
// canonical loop early — which keeps the loop bounded, so the strict profile
// still certifies it. Both realizations agree.
const breakProgram = `
first_zero: (v: []u8): u32 {
  i: u32 = 0
  n: u32 = len(v)
  found: u32 = n
  while i < n {
    v[i] == u8(0) ? { found = i
      break }
    i = i + u32(1)
  }
  found
}
inner_only: (): u32 {
  outer: u32 = 0
  total: u32 = 0
  while outer < u32(3) {
    inner: u32 = 0
    while inner < u32(10) {
      inner == u32(2) ? { break }
      total = total + u32(1)
      inner = inner + u32(1)
    }
    outer = outer + u32(1)
  }
  total
}
main: (): i32 {
  data: [5]u8 = [5]u8{ 3, 1, 0, 4, 0 }
  assert(first_zero(view(&data)) == u32(2))
  full: [2]u8 = [2]u8{ 1, 1 }
  assert(first_zero(view(&full)) == u32(2))
  assert(inner_only() == u32(6))
  42
}
`

func TestE2EBreak(t *testing.T) {
	code, abnormal := buildAndRun(t, "break", breakProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	if interpreted := interpretChecked(t, breakProgram); interpreted != 42 {
		t.Fatalf("interpreter returned %d", interpreted)
	}
	// A bounded loop with a break stays certified under the strict profile.
	if _, err := New().WithProfile("strict").WithSource("break.oak", breakProgram).EmitC().Get(); err != nil {
		t.Fatalf("strict profile rejected a bounded loop with a break: %v", err)
	}
}

func TestBreakOutsideLoopIsRejected(t *testing.T) {
	cases := map[string]string{
		"top level of a function":           "f: (): u32 {\n  break\n  u32(1)\n}\nmain: (): i32 { 0 }",
		"inside a conditional arm, no loop": "f: (b: Bool): u32 {\n  b ? { break }\n  u32(1)\n}\nmain: (): i32 { 0 }",
	}
	for name, src := range cases {
		_, err := New().WithSource("reject.oak", src).Check().Get()
		if err == nil || !strings.Contains(err.Error(), "break outside a while loop") {
			t.Fatalf("%s: err = %v, want the break rejected", name, err)
		}
	}
}
