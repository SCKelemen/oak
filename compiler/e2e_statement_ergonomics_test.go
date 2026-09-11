package compiler

import (
	"strings"
	"testing"
)

// Statement ergonomics (docs/spec/10-syntax.md sections 3c, 4a, 4b): a bare
// block statement scopes its bindings, a line that begins with `-` is a new
// statement, and a typed function literal is a plain code pointer that
// lowers to a lifted C function. Verified in running machine code.

func TestE2EBareBlockStatementScopes(t *testing.T) {
	// The inner y is gone after the block; x keeps the assignment.
	exit, abnormal := buildAndRun(t, "bare_block", `
main: (): u32 {
  x: u32 = 1
  {
    y: u32 = 41
    x = x + y
  }
  {
    y: u32 = 100
    _ = y
  }
  x
}
`)
	if abnormal || exit != 42 {
		t.Fatalf("bare block: exit %d abnormal %v", exit, abnormal)
	}
	// A binding declared inside the block is not visible after it.
	_, err := New().WithSource("bare_block_scope.oak", `
main: (): u32 {
  {
    y: u32 = 1
  }
  y
}
`).Check().Get()
	if err == nil || !strings.Contains(err.Error(), "y") {
		t.Fatalf("a block-local binding must not escape its block: %v", err)
	}
}

func TestE2ELineStartMinusBeginsStatement(t *testing.T) {
	// `-x == u32(...)` on its own line is a negation, not `1 - x`.
	exit, abnormal := buildAndRun(t, "line_start_minus", `
main: (): u32 {
  x: i32 = 3
  y: u32 = 1
  -x == 0 - 3 ? { y = 42 }
  y
}
`)
	if abnormal || exit != 42 {
		t.Fatalf("line-start minus: exit %d abnormal %v", exit, abnormal)
	}
	// An operator at the END of a line still continues the expression.
	exit, abnormal = buildAndRun(t, "line_end_minus", `
main: (): u32 {
  x: u32 = 50 -
    8
  x
}
`)
	if abnormal || exit != 42 {
		t.Fatalf("line-end minus: exit %d abnormal %v", exit, abnormal)
	}
}

func TestE2ETypedFunctionLiterals(t *testing.T) {
	exit, abnormal := buildAndRun(t, "typed_literals", `
apply: (f: (u32) -> u32, x: u32): u32 = f(x)
twice: (f: (u32) -> u32, x: u32): u32 = f(f(x))

main: (): u32 {
  inc := fn(x: u32): u32 = x + 1
  add: (u32, u32) -> u32 = fn(a: u32, b: u32): u32 { a + b }
  say := fn(): () = {}
  say()
  total: u32 = apply(inc, 10)
  total = twice(fn(x: u32): u32 = x * 2, total)
  add(total, 0) - 2
}
`)
	if abnormal || exit != 42 {
		t.Fatalf("typed literals: exit %d abnormal %v", exit, abnormal)
	}
	// The declared types are checked: a body of the wrong type is an error.
	_, err := New().WithSource("typed_literal_mismatch.oak", `
main: (): u32 {
  f := fn(x: u32): u32 = true
  f(1)
}
`).Check().Get()
	if err == nil || !strings.Contains(err.Error(), "expected return type") {
		t.Fatalf("a typed literal body must match its return annotation: %v", err)
	}
	// A parameter typed in the literal is used at that type, not i32.
	_, err = New().WithSource("typed_literal_param.oak", `
main: (): u32 {
  f := fn(x: u64): u32 = u32_trunc_u64(x)
  f(u64(1))
}
`).Check().Get()
	if err != nil {
		t.Fatalf("typed literal parameters take their declared types: %v", err)
	}
}
