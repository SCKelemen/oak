package compiler

import "testing"

// An unsafe block inside a function body is an ordinary scope to the C
// backend. Before the inbound-buffer work the statement emitter had no case
// for it and dropped the body behind a TODO comment, so an unsafe block
// compiled to nothing while the interpreter ran it; this pins the fix in
// the compiled form and in the interpreter.
const unsafeBlockProgram = `
main: (): i32 {
  buf: [4]u8
  total: u32 = 0
  unsafe {
    s: [*]u8 = span(&buf)
    s[0] = u8(40)
    s[1] = u8(2)
    i: u32 = 0
    while i < u32(4) {
      total = total + u32(s[i])
      i = i + u32(1)
    }
  }
  i32_bits_u32(total)
}
`

func TestE2EUnsafeBlockExecutes(t *testing.T) {
	code, abnormal := buildAndRun(t, "unsafeblock", unsafeBlockProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if got := interpretChecked(t, unsafeBlockProgram); got != 42 {
		t.Fatalf("interpreter returned %d, want 42", got)
	}
}
