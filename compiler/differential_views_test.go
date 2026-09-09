package compiler

import (
	"testing"

	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// interpret runs a program in the evaluator and then calls main().
func interpret(t *testing.T, src string) int64 {
	t.Helper()
	env := object.NewEnvironment()
	for _, text := range []string{src, "main()"} {
		p := parser.New(layout.New(scanner.New(text)))
		program := p.ParseProgram()
		if errors := p.Errors(); len(errors) != 0 {
			t.Fatalf("parse: %v", errors)
		}
		result := evaluator.Eval(program, env)
		if err, isErr := result.(*object.Error); isErr {
			t.Fatalf("interpreter error: %s", err.Message)
		}
		if text == "main()" {
			integer, ok := result.(*object.Integer)
			if !ok {
				t.Fatalf("main() returned %s", result.Inspect())
			}
			return integer.Value
		}
	}
	return 0
}

// The differential witness for views, spans, subslice, and the extent
// programs: the interpreter and the compiled C agree on the result.
func TestDifferentialViewsSubsliceExtents(t *testing.T) {
	programs := map[string]string{
		"subslice": `
tail_sum: (v: []u64): u64 {
  rest: []u64 = subslice(v, u32(1), u32(2))
  rest[u32(0)] + rest[u32(1)]
}

fill_tail: (s: [*]u64): u64 {
  rest: [*]u64 = subslice(s, u32(2), u32(2))
  rest[u32(0)] = u64(30)
  rest[u32(1)] = u64(7)
  rest[u32(0)] + rest[u32(1)]
}

main: (): i32 {
  regs: [4]u64
  regs[u32(1)] = u64(40)
  regs[u32(2)] = u64(2)
  v: []u64 = view(&regs)
  assert(tail_sum(v) == u64(42))
  buf: [4]u64
  s: [*]u64 = span(&buf)
  assert(fill_tail(s) == u64(37))
  42
}
`,
		"extents": `
pair_sum: (v: []u64): u64 {
  total: u64 = 0
  i: u32 = 0
  while i + u32(1) < len(v) {
    total = total + v[i] + v[i + u32(1)]
    i = i + u32(2)
  }
  total
}

main: (): i32 {
  regs: [4]u64
  regs[u32(0)] = u64(10)
  regs[u32(1)] = u64(20)
  regs[u32(2)] = u64(5)
  regs[u32(3)] = u64(7)
  v: []u64 = view(&regs)
  assert(pair_sum(v) == u64(42))
  s: []u64 = regs[u32(1):u32(3)]
  assert(s[u32(0)] + s[u32(1)] == u64(25))
  42
}
`,
	}
	for name, src := range programs {
		t.Run(name, func(t *testing.T) {
			code, abnormal := buildAndRun(t, "diff_"+name, src)
			if abnormal || code != 42 {
				t.Fatalf("compiled: exit = (%d, abnormal=%v), want 42", code, abnormal)
			}
			if got := interpret(t, src); got != 42 {
				t.Fatalf("interpreted: %d, want 42", got)
			}
		})
	}
}
