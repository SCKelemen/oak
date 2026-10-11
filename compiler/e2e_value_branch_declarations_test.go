package compiler

import (
	"strings"
	"testing"
)

// Declaration-bearing branches are values in every expression position
// (docs/spec/10-syntax.md section 3a). In particular, the final assignment
// inside a statement arm must not put its declarations inside a C ternary.
func TestE2EValueBranchDeclarations(t *testing.T) {
	cases := []struct {
		name string
		src  string
		out  string
	}{
		{"last assignment in statement branch", `
conditional_assignment: (enabled: Bool, choose: Bool, input: u32): u32 {
  out: u32 = u32(0)
  enabled ? {
    out = choose ? {
      value: u32 = input + u32(1)
      value
    } | { input }
  } | { }
  out
}
main: (): i32 {
  assert(conditional_assignment(true, true, u32(41)) == u32(42))
  assert(conditional_assignment(true, false, u32(41)) == u32(41))
  assert(conditional_assignment(false, true, u32(41)) == u32(0))
  42
}
`, ""},
		{"nested declarations and sibling scopes", `
pick: (choose: Bool): u32 {
  out: u32 = u32(0)
  true ? {
    out = choose ? {
      items: [2]u32 = [2]u32{ u32(1), u32(2) }
      inner: u32 = choose ? {
        bonus: u32 = items[u32(1)]
        bonus + u32(10)
      } | { u32(90) }
      inner
    } | {
      items: [3]u32 = [3]u32{ u32(3), u32(4), u32(5) }
      items[u32(2)]
    }
  }
  items: [1]u32 = [1]u32{ u32(7) }
  out + items[u32(0)]
}
main: (): i32 {
  assert(pick(true) == u32(19))
  assert(pick(false) == u32(12))
  42
}
`, ""},
		{"condition once and left to right effects", `
putchar: (ch: c.Int): c.Int = c.extern("putchar")
mark: (ch: i32): i32 {
  _ = putchar(c.Int(ch))
  ch
}
main: (): i32 {
  sum: i32 = mark(65) + (mark(66) > 0 ? {
    chosen: i32 = mark(67)
    chosen
  } | {
    skipped: i32 = mark(88)
    skipped
  }) + mark(68)
  assert(sum == 200)
  last: i32 = mark(69) < 0 ? {
    skipped: i32 = mark(88)
    skipped
  } | {
    chosen: i32 = mark(70)
    chosen
  }
  assert(last == 70)
  42
}
`, "ABCDEF"},
		{"enclosing local read before branch write", `
main: (): i32 {
  x: i32 = 10
  first: i32 = x + (true ? {
    x = 20
    local: i32 = 2
    local
  } | 0)
  assert(first == 12)
  assert(x == 20)
  second: i32 = (true ? {
    x = 30
    local: i32 = 3
    local
  } | 0) + x
  assert(second == 33)
  42
}
`, ""},
		{"short circuit and skipped traps", `
fail: (x: i32): i32 {
  assert(x == 99)
  x
}
main: (): i32 {
  a: Bool = false && (true ? {
    bad: i32 = fail(0)
    bad > 0
  } | false)
  b: Bool = true || (false ? false | {
    bad: i32 = fail(0)
    bad > 0
  })
  assert(!a && b)
  value: i32 = 1 + (true ? {
    good: i32 = 41
    good
  } | {
    bad: i32 = fail(0)
    bad
  })
  assert(value == 42)
  42
}
`, ""},
		{"loop condition reevaluates declarations", `
main: (): i32 {
  i: u32 = u32(0)
  hits: u32 = u32(0)
  while (i < u32(3) ? {
    next: u32 = i + u32(1)
    i = next
    true
  } | false) {
    hits = hits + u32(1)
  }
  assert(i == u32(3))
  assert(hits == u32(3))
  42
}
`, ""},
		{"aggregate result and call argument", `
Point: type = struct { x: i32, y: i32 }
total: (p: Point): i32 = p.x + p.y
pick: (choose: Bool): i32 = total(choose ? {
  point: Point = Point { x: 20, y: 22 }
  point
} | {
  point: Point = Point { x: 30, y: 12 }
  point
})
main: (): i32 {
  assert(pick(true) == 42)
  assert(pick(false) == 42)
  42
}
`, ""},
		{"scalar match arms", `
pick: (n: i32): i32 = 1 + (n ?
  | 0 => { value: i32 = 41; value }
  | _ => { value: i32 = 42; value })
main: (): i32 {
  assert(pick(0) == 42)
  assert(pick(1) == 43)
  42
}
`, ""},
		{"defer follows branch value", `
putchar: (ch: c.Int): c.Int = c.extern("putchar")
mark: (ch: i32): i32 {
  _ = putchar(c.Int(ch))
  ch
}
main: (): i32 {
  value: i32 = 1 + (true ? {
    defer mark(68)
    chosen: i32 = mark(86)
    chosen
  } | {
    skipped: i32 = mark(88)
    skipped
  })
  assert(value == 87)
  42
}
`, "VD"},
		{"atomic storage paths retain identity and index order", `
Node: type = struct { cell: Atomic[u32] }
next: (count: [*]u32): u32 {
  count[u32(0)] = count[u32(0)] + u32(1)
  count[u32(0)] - u32(1)
}
main: (): i32 {
  cell: Atomic[u32]
  atomic_store_relaxed(cell, true ? {
    value: u32 = u32(42)
    value
  } | u32(0))
  assert(atomic_load_relaxed(cell) == u32(42))
  nodes: [2]Node
  i: u32 = u32(0)
  atomic_store_relaxed(nodes[i].cell, true ? {
    i = u32(1)
    value: u32 = u32(43)
    value
  } | u32(0))
  assert(atomic_load_relaxed(nodes[u32(0)].cell) == u32(43))
  assert(atomic_load_relaxed(nodes[u32(1)].cell) == u32(0))
  cells: [2]Atomic[u32]
  count: [1]u32
  atomic_store_relaxed(cells[next(span(&count))], true ? {
    value: u32 = next(span(&count)) + u32(40)
    value
  } | u32(0))
  assert(count[u32(0)] == u32(2))
  assert(atomic_load_relaxed(cells[u32(0)]) == u32(41))
  assert(atomic_load_relaxed(cells[u32(1)]) == u32(0))
  42
}
`, ""},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			comp := New().WithSource("value_branch.oak", tc.src)
			output, err := comp.EmitC().Get()
			if err != nil {
				t.Fatalf("compilation failed: %v", err)
			}
			if strings.Contains(output, "__typeof__") {
				t.Fatalf("value branch temporary lost its checked C type:\n%s", output)
			}
			stdout, code, abnormal := buildAndRunFrom(t, "value_branch", comp)
			if abnormal || code != 42 || stdout != tc.out {
				t.Fatalf("compiled: exit=%d abnormal=%v stdout=%q; want 42, false, %q", code, abnormal, stdout, tc.out)
			}
		})
	}
}
