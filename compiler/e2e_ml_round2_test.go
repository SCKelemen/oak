package compiler

import (
	"strings"
	"testing"
)

// The ml pilot's second request list
// (docs/notes/ml-language-requests-2026-09-round2.md).

// F24: a top-level owner is visible to every function, above or below
// its declaration.
func TestE2EOwnerDeclaredLater(t *testing.T) {
	src := `
total: (): u32 = {
  v: []u32 = view(&TABLE)
  acc: u32 = 0
  i: u32 = 0
  n: u32 = len(v)
  while i < n {
    acc = acc + v[i]
    i = i + 1
  }
  acc
}

TABLE: [4]u32 = [1, 2, 3, 36]

main: (): i32 = total() == 42 ? 42 | 1
`
	code, abnormal := buildAndRun(t, "owner_later", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// F7: realized-ness in the type. A typestate protocol over a record that
// also carries a region parameter: the transition returns the record in
// its next state over the same region, an operation that needs its
// operand realized takes Node[R, Realized], and a wrong order is a type
// error.
const realizedProgram = `
Node[R, S]: type = struct { data: View[f32, R], n: u32 }

Realize: protocol = {
  resource Node
  initial Lazy
  realize: Lazy -> Realized via realize(consumed x)
}

realize[R]: (x: Node[R, Lazy]): Node[R, Realized] = Node { data: x.data, n: x.n + 1 }

total[R]: (x: Node[R, Realized]): f32 = {
  acc: f32 = 0.0
  i: u32 = 0
  m: u32 = len(x.data)
  while i < m {
    acc = acc + x.data[i]
    i = i + 1
  }
  acc
}

main: (): i32 = {
  xs: [3]f32 = [1.0, 2.0, 3.0]
  lazy: Node[Lazy] = Node { data: view(&xs), n: 0 }
  ready: Node[Realized] = realize(lazy)
  total(ready) == 6.0 && ready.n == 1 ? 42 | 1
}
`

func TestE2ERealizedTypestateOverRegionRecord(t *testing.T) {
	code, abnormal := buildAndRun(t, "realized", realizedProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	wrongOrder := strings.Replace(realizedProgram, "total(ready) == 6.0 && ready.n == 1 ? 42 | 1", "total(lazy) == 6.0 ? 42 | 1", 1)
	if _, err := New().WithSource("realized_wrong.oak", wrongOrder).EmitC().Get(); err == nil {
		t.Fatal("an unrealized operand must be a type error")
	}
}

// F1: a kernel's statement order is the emitted order — the loads a body
// writes after its multiplies stay after them.
func TestKernelsPreserveStatementOrder(t *testing.T) {
	src := `
kernel ordered: (gid: u32, x: []f32, y: []f32, out: [*]f32): () = {
  gid < len(out) && gid < len(x) && gid < len(y) ? {
    a: f32 = x[gid]
    p: f32 = a * a
    b: f32 = y[gid]
    q: f32 = p * b
    c: f32 = x[gid] + y[gid]
    out[gid] = q + c
  }
}
main: (): i32 = 0
`
	result, err := New().WithSource("ordered.oak", src).EmitMetal().Get()
	if err != nil {
		t.Fatal(err)
	}
	body := result.Source[strings.Index(result.Source, "kernel void ordered"):]
	previous := -1
	for _, line := range []string{
		"float a = x[gid];",
		"float p = (a * a);",
		"float b = y[gid];",
		"float q = (p * b);",
		"float c = (x[gid] + y[gid]);",
		"out[gid] = (q + c);",
	} {
		at := strings.Index(body, line)
		if at < 0 || at < previous {
			t.Fatalf("statement %q missing or out of order in:\n%s", line, body)
		}
		previous = at
	}
}

// F4: a captured step — a function value stored in a record field — is
// checked against the field's effect row where the record is built, and a
// read of a rowed field is a rowed value.
func TestE2EEffectRowsOnRecordFields(t *testing.T) {
	src := `
Step: type = struct { run: (u32) -> u32 effects { } }
inc: (x: u32): u32 = x + 1
launch: (s: Step, x: u32): u32 forbids { Host.Read } = {
  f: (u32) -> u32 effects { } = s.run
  f(x)
}
main: (): i32 = {
  s: Step = Step { run: inc }
  launch(s, 41) == 42 ? 42 | 1
}
`
	code, abnormal := buildAndRun(t, "step_record", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	hostReading := `
host_read: (x: c.UInt32): c.UInt32 effects { Host.Read } = c.extern("oak_host_read")
peek: (x: u32): u32 = u32(host_read(c.UInt32(x)))
Step: type = struct { run: (u32) -> u32 effects { } }
main: (): i32 = {
  s: Step = Step { run: peek }
  0
}
`
	msg := effectError(t, "step_record_host", hostReading, CodeEffectRow)
	for _, want := range []string{"field run of Step", "performs Host.Read", "peek -> host_read"} {
		if !strings.Contains(msg, want) {
			t.Fatalf("missing %q: %s", want, msg)
		}
	}
	// A rowed field read into a narrower row is rejected; an unrowed field
	// read stays unknown.
	wider := `
Step: type = struct { run: (u32) -> u32 effects { Host.Read } }
inc: (x: u32): u32 = x + 1
use: (s: Step): u32 = {
  f: (u32) -> u32 effects { } = s.run
  f(1)
}
main: (): i32 = 0
`
	effectError(t, "step_record_wider", wider, CodeEffectRow)
	unrowed := `
Step: type = struct { run: (u32) -> u32 }
inc: (x: u32): u32 = x + 1
use: (s: Step): u32 = {
  f: (u32) -> u32 effects { } = s.run
  f(1)
}
main: (): i32 = 0
`
	msg = effectError(t, "step_record_unrowed", unrowed, CodeEffectRow)
	if !strings.Contains(msg, "has no effect row") {
		t.Fatalf("unrowed field must be unknown: %s", msg)
	}
}
