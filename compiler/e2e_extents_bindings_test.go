package compiler

import (
	"strings"
	"testing"
)

// Extent facts, fourth increment: facts flow through bindings. An upper
// bound `n <= len(v)` combined with a guard `i < n` proves v[i]; a Bool
// binding remembers the facts of the condition assigned to it (and
// `valid = valid && more` strengthens them), so `valid ? { ... }` and
// `while ... && valid` see them. These are the verification decoder's
// idioms (typechecker/extents.go).
func TestE2EExtentFactsFlowThroughBindings(t *testing.T) {
	src := `
check_hints: (hints: []u32, hint_count: u32, starts: []u32, clause_count: u32): u32 {
  valid: Bool = clause_count <= len(starts)
  valid = valid && hint_count <= len(hints)
  total: u32 = 0
  i: u32 = 0
  while i < hint_count && valid {
    id: u32 = hints[i]
    valid = id < clause_count
    valid ? {
      total = total + starts[id]
    }
    i = i + 1
  }
  valid ? { total } | { 0 }
}
main: (): i32 {
  hints: [3]u32 = [3]u32{ 0, 2, 1 }
  starts: [4]u32 = [4]u32{ 10, 20, 12, 99 }
  hv: []u32 = hints[0:3]
  sv: []u32 = starts[0:4]
  assert(check_hints(hv, 3, sv, 3) == 42)
  assert(check_hints(hv, 3, sv, 2) == 0)
  42
}
`
	output, err := New().WithSource("bindings.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	// hints[i] under i < hint_count <= len(hints); starts[id] under
	// id < clause_count <= len(starts) remembered by valid.
	if strings.Contains(output, "oak_view_index_u32( ") {
		t.Fatalf("a binding-guarded access remained checked:\n%s", output)
	}
	if got := strings.Count(output, ".base[ "); got != 2 {
		t.Fatalf("expected 2 proven view accesses, found %d:\n%s", got, output)
	}
	code, abnormal := buildAndRun(t, "bindings", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// The kills: a plain reassignment replaces a Bool binding's facts, a bound
// binding reassigned in the loop drops the binding-borne fact for the
// body, and a fact through `||` is never derived.
func TestE2EExtentBindingFactsKilled(t *testing.T) {
	cases := []struct{ name, src string }{
		{"plain-reassignment", `
f: (v: []u32, n: u32, i: u32, flag: Bool): u32 {
  valid: Bool = n <= len(v) && i < n
  valid = flag
  valid ? { v[i] } | { 0 }
}
main: (): i32 { 42 }
`},
		{"bound-moves-in-loop", `
f: (v: []u32, n: u32): u32 {
  valid: Bool = n <= len(v)
  total: u32 = 0
  i: u32 = 0
  while i < n && valid {
    total = total + v[i]
    n = n + 1
    i = i + 1
  }
  total
}
main: (): i32 { 42 }
`},
		{"or-condition", `
f: (v: []u32, n: u32, i: u32, flag: Bool): u32 {
  valid: Bool = (n <= len(v) && i < n) || flag
  valid ? { v[i] } | { 0 }
}
main: (): i32 { 42 }
`},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			output, err := New().WithSource(c.name+".oak", c.src).EmitC().Get()
			if err != nil {
				t.Fatalf("compilation failed: %v", err)
			}
			if !strings.Contains(output, "oak_view_index_u32( ") || strings.Contains(output, ".base[ ") {
				t.Fatalf("%s: the access must stay checked:\n%s", c.name, output)
			}
		})
	}
}

// A binding of len(v) is an upper bound for indices into v
// (Oak.Extents.bound_through_upper): the canonical strict loop
// `n: u32 = len(x); while i < n { x[i] }` is discharged, and a later
// reassignment of the bound binding keeps the access checked.
func TestE2EExtentLenBindingBoundsTheLoop(t *testing.T) {
	src := `
sum_all: (x: []f32): f32 {
  n: u32 = len(x)
  acc: f32 = 0.0
  i: u32 = 0
  while i < n {
    acc = acc + x[i]
    i = i + 1
  }
  acc
}
main: (): i32 {
  xs: [4]f32 = [1.0, 2.0, 3.0, 4.0]
  sum_all(view(&xs)) == 10.0 ? 42 | 1
}
`
	output, err := New().WithSource("len_binding.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if strings.Contains(output, "oak_view_index_f32( x") {
		t.Fatalf("the loop-bounded access remained checked:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "len_binding", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	reassigned := `
sum_all: (x: []f32): f32 {
  n: u32 = len(x)
  acc: f32 = 0.0
  i: u32 = 0
  while i < n {
    acc = acc + x[i]
    i = i + 1
  }
  n = n + 1
  acc
}
main: (): i32 = 0
`
	output, err = New().WithSource("len_binding_killed.oak", reassigned).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if !strings.Contains(output, "oak_view_index_f32( x") {
		t.Fatalf("a reassigned bound binding must keep the access checked:\n%s", output)
	}
}
