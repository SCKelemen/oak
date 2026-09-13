package compiler

import (
	"strings"
	"testing"
)

// Left-to-right evaluation (docs/spec/10-syntax.md §3d): operands, call
// arguments, record fields, array elements, index operands and slice bounds
// evaluate left to right, whatever the C compiler's own preference. The
// interpreter is the reference; the C backend sequences side-effecting
// operands into temporaries (codegen/sequence.go). Each program below
// computes a value that differs under right-to-left evaluation — gcc's
// order for call arguments on x86-64, which made TestRingsAtomicBorrowRules
// return 1 for 3 on CI — and both realizations must agree with the
// specified value.
func TestE2EEvaluationOrderIsLeftToRight(t *testing.T) {
	// next bumps a counter through a span and returns the new value, so
	// the order of two calls is visible in what each returns.
	prelude := `next: (c: [*]u32): u32 {
  c[0] = c[0] + 1
  c[0]
}
pair: (a: u32, b: u32): u32 = a * 10 + b
Pt: type = struct {
  x: u32
  y: u32
}
`
	cases := []struct {
		name string
		body string // the body of main, computing a u32 in `s: [1]u32`
		want int64
		seq  bool // whether the C must carry sequencing temporaries
	}{
		{"infix operands", "next(span(&s)) * 10 + next(span(&s))", 12, true},
		// `pair` is an inlinable helper (compiler/inline.go): its arguments
		// are hoisted into typed temporaries, one statement each in call
		// order, so the sequencing is the statements' and no temporary of
		// the C emitter's own is needed.
		{"call arguments", "pair(next(span(&s)), next(span(&s)))", 12, false},
		{"nested groups", "pair(next(span(&s)) * 10 + next(span(&s)), next(span(&s)))", 123, true},
		{"record fields", "p: Pt = Pt { x: next(span(&s)), y: next(span(&s)) }\n  p.x * 10 + p.y", 12, true},
		{"array elements", "a: [2]u32 = [2]u32{ next(span(&s)), next(span(&s)) }\n  a[0] * 10 + a[1]", 12, true},
		{"read after a writing sibling", "next(span(&s)) * 10 + s[0]", 11, true},
		{"read before a writing sibling", "s[0] * 10 + next(span(&s))", 1, true},
		{"return position", "next(span(&s)) * 10 + next(span(&s))", 12, true},
		{"conditional arm", "r: u32 = s[0] == 0 ? | true => next(span(&s)) * 10 + next(span(&s)) | false => 0\n  r", 12, true},
		{"short-circuit right operand", "ok: Bool = next(span(&s)) > 0 && next(span(&s)) * 10 + next(span(&s)) == 23\n  ok ? | true => 1 | false => 0", 1, true},
		{"while condition", "while next(span(&s)) * 100 + next(span(&s)) < 400 {\n    _ = 0\n  }\n  s[0]", 6, true},
		{"assert operand", "assert(next(span(&s)) * 10 + next(span(&s)) == 12)\n  s[0]", 2, true},
		{"one effect stays inline", "next(span(&s)) + 1", 2, false},
		{"pure calls stay inline", "a: u32 = 7\n  b: u32 = 5\n  v: []u32 = view(&s)\n  u32(u8_trunc_u32(a)) + u32(u8_trunc_u32(b)) + len(v)", 13, false},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			program := prelude + "main: (): u32 {\n  s: [1]u32\n  " + c.body + "\n}\n"
			if got := interpretChecked(t, program); got != c.want {
				t.Fatalf("interpreter: %d, want %d", got, c.want)
			}
			output, err := New().WithSource("order.oak", program).EmitC().Get()
			if err != nil {
				t.Fatalf("compilation failed: %v", err)
			}
			if has := strings.Contains(output, "oak__seq_"); has != c.seq {
				t.Fatalf("sequencing temporaries present = %v, want %v:\n%s", has, c.seq, output)
			}
			if strings.Contains(output, "__typeof__") {
				t.Fatalf("temporary without a C spelling:\n%s", output)
			}
			_, exit, abnormal := buildAndRunOutput(t, "order_"+strings.ReplaceAll(c.name, " ", "_"), program)
			if abnormal || int64(exit) != c.want {
				t.Fatalf("compiled: exit %d abnormal %v, want %d\n%s", exit, abnormal, c.want, output)
			}
		})
	}
}

// The expression that found the gap (TestRingsAtomicBorrowRules on CI,
// 2026-09-13): two calls that each bump a counter through a span and store
// into an atomic, summed with a relaxed load of that atomic. Left to right
// the calls return 0 and 1 and the load sees 2; gcc's right-to-left
// argument order read the load first and returned 1.
func TestE2EEvaluationOrderRingsCase(t *testing.T) {
	program := `Cursor: type = struct {
  tail: Atomic[u32]
  n: u32
}
bump: (c: [*]Cursor, cells: [*]Atomic[u32]): u32 {
  atomic_store_release(c[0].tail, atomic_load_relaxed(cells[0]) + u32(1))
  atomic_fetch_add_relaxed(cells[0], u32(1))
}
main: (): u32 {
  state: [1]Cursor
  cells: [2]Atomic[u32]
  bump(span(&state), span(&cells)) + bump(span(&state), span(&cells)) + atomic_load_relaxed(state[0].tail)
}
`
	if got := interpretChecked(t, program); got != 3 {
		t.Fatalf("interpreter: %d, want 3", got)
	}
	output, err := New().WithSource("rings_order.oak", program).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, line := range []string{
		"u32 oak__seq_0 = oak_bump(",
		"u32 oak__seq_1 = oak_bump(",
		"u32 oak__seq_2 = atomic_load_explicit(",
		"return oak_add_u32( oak_add_u32( oak__seq_0, oak__seq_1 ), oak__seq_2 )",
	} {
		if !strings.Contains(output, line) {
			t.Fatalf("emitted C lacks %q:\n%s", line, output)
		}
	}
	_, exit, abnormal := buildAndRunOutput(t, "rings_order", program)
	if abnormal || exit != 3 {
		t.Fatalf("compiled: exit %d abnormal %v, want 3", exit, abnormal)
	}
}
