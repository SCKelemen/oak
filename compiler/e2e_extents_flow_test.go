package compiler

import (
	"strings"
	"testing"
)

// Extent facts, third increment: facts are flow-sensitive. A guard's fact
// holds until the statement that assigns a participating binding, the right
// operand of && sees its guard's facts, a loop
// that assigns a binding invalidates enclosing facts about it before it
// runs, and kills in one match arm do not reach sibling arms but do reach
// the statements after the match (typechecker/extents.go).
func TestE2EExtentFactsFlowThroughScopes(t *testing.T) {
	src := `
is_space: (b: u8): Bool {
  b == 32 || b == 9
}
skip_spaces: (text: []u8, start: u32): u32 {
  pos: u32 = start
  while pos < len(text) && is_space(text[pos]) {
    pos = pos + 1
  }
  pos
}
classify: (text: []u8, pos: u32): u32 {
  kind: u32 = 0
  pos < len(text) ? {
    text[pos] == 10 ? { kind = 1 } | {
      kind = 2
      end: u32 = pos
      while end < len(text) && text[end] != 10 {
        end = end + 1
      }
      kind = kind + end - pos
    }
  }
  kind
}
main: (): i32 {
  bytes: [8]u8
  bytes[0] = 32
  bytes[1] = 9
  bytes[2] = 65
  bytes[3] = 66
  bytes[4] = 10
  text: []u8 = bytes[0:8]
  assert(skip_spaces(text, 0) == 2)
  assert(skip_spaces(text, 2) == 2)
  assert(classify(text, 4) == 1)
  assert(classify(text, 2) == 4)
  assert(classify(text, 8) == 0)
  42
}
`
	output, err := New().WithSource("extents3.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	// text[pos] in skip_spaces' && condition, text[pos] as the arm
	// scrutinee, text[end] in the inner loop's && condition.
	if strings.Contains(output, "oak_view_index_u8( ") {
		t.Fatalf("a guarded access remained checked:\n%s", output)
	}
	if got := strings.Count(output, ".base[ "); got != 3 {
		t.Fatalf("expected 3 proven view accesses, found %d:\n%s", got, output)
	}
	code, abnormal := buildAndRun(t, "extents3", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// The kills: an access after the assignment in the same arm, an access in a
// loop nested under an outer guard when the loop moves the index, an access
// after a match whose arm moved the index, and the wrapping guard `i + 1 <
// len(v)` all keep their checks.
func TestE2EExtentFactsKilledByAssignments(t *testing.T) {
	cases := []struct{ name, src string }{
		{"after-assignment-in-arm", `
f: (v: []u8, i: u32): u32 {
  out: u32 = 0
  i < len(v) ? {
    i = i + 1
    out = u32(v[i])
  }
  out
}
main: (): i32 { 42 }
`},
		{"loop-under-outer-guard", `
f: (v: []u8, i: u32, n: u32): u32 {
  out: u32 = 0
  i < len(v) ? {
    k: u32 = 0
    while k < n {
      out = out + u32(v[i])
      i = i + 1
      k = k + 1
    }
  }
  out
}
main: (): i32 { 42 }
`},
		{"after-match-that-moved-index", `
f: (v: []u8, i: u32, flag: Bool): u32 {
  out: u32 = 0
  i < len(v) ? {
    flag ? { i = i + 1 } | { out = 1 }
    out = out + u32(v[i])
  }
  out
}
main: (): i32 { 42 }
`},
		{"wrapping-offset-guard", `
f: (v: []u8, i: u32): u32 {
  out: u32 = 0
  i + 1 < len(v) ? { out = u32(v[i]) }
  out
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
			if !strings.Contains(output, "oak_view_index_u8( ") || strings.Contains(output, ".base[ ") {
				t.Fatalf("%s: the access must stay checked:\n%s", c.name, output)
			}
		})
	}
	// Sibling arms are independent: a kill in the first arm leaves the
	// second arm's access proven.
	output, err := New().WithSource("siblings.oak", `
f: (v: []u8, i: u32, flag: Bool): u32 {
  out: u32 = 0
  i < len(v) ? {
    flag ? { i = i + 1 } | { out = u32(v[i]) }
  }
  out
}
main: (): i32 { 42 }
`).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(output, "oak_view_index_u8( ") || strings.Count(output, ".base[ ") != 1 {
		t.Fatalf("the sibling arm's access must be proven:\n%s", output)
	}
}
