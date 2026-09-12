package compiler

import (
	"strings"
	"testing"
)

// Capturing closures (docs/spec/60-effects-allocation.md §11;
// compiler/closures.go): a typed literal that captures scalar, string, view
// or span parameters and annotated locals of its enclosing function, passed
// directly to a top-level function that only calls its function parameter,
// is specialized away — the callee is cloned for the call site and the
// captured values travel as arguments. Both realizations run the result.
const closureProgram = `package main

scale_all: (f: (u32) -> u32, v: []u32, out: [*]u32): () {
  assert(len(v) == len(out))
  i: u32 = u32(0)
  while i < len(v) {
    out[i] = f(v[i])
    i = i + u32(1)
  }
}

fold: (f: (u32, u32) -> u32, v: []u32, seed: u32): u32 {
  acc: u32 = seed
  i: u32 = u32(0)
  while i < len(v) {
    acc = f(acc, v[i])
    i = i + u32(1)
  }
  acc
}

each_index: (f: (u32) -> (), n: u32): () {
  i: u32 = u32(0)
  while i < n {
    f(i)
    i = i + u32(1)
  }
}

run: (base: u32): u32 {
  data: [3]u32 = [3]u32{ u32(1), u32(2), u32(3) }
  out: [3]u32
  k: u32 = u32(3)
  // captures k (an annotated local) and base (a parameter)
  scale_all(fn(x: u32): u32 = x * k + base, view(&data), span(&out))
  assert(out[0] == u32(13) && out[1] == u32(16) && out[2] == u32(19))
  cap: u32 = u32(40)
  // a two-parameter literal capturing one local, into a different callee
  folded: u32 = fold(fn(acc: u32, x: u32): u32 = acc + x > cap ? cap | acc + x, view(&out), u32(0))
  // a view captured and indexed inside the literal
  weights: []u32 = view(&data)
  weighted: u32 = fold(fn(acc: u32, x: u32): u32 = acc + x * weights[u32(0)], view(&out), u32(0))
  assert(weighted == u32(48))
  // a span captured and written inside a unit-returning literal
  squares: [3]u32
  target: [*]u32 = span(&squares)
  each_index(fn(i: u32): () { target[i] = (i + u32(1)) * (i + u32(1)) }, u32(3))
  assert(target[u32(0)] == u32(1) && target[u32(1)] == u32(4) && target[u32(2)] == u32(9))
  folded
}

main: (): i32 {
  i32_bits_u32(run(u32(10)) + u32(2))
}
`

func closureModule(t *testing.T, program string) string {
	t.Helper()
	return writeModule(t, map[string]string{
		"oak.mod":  "module example.com/closures\noak 0.1.0\n",
		"main.oak": program,
	})
}

func TestE2ECapturingClosureInterpreted(t *testing.T) {
	if got := interpretModule(t, closureModule(t, closureProgram)); got != 42 {
		t.Fatalf("main() returned %d, want 42", got)
	}
}

func TestE2ECapturingClosureCompiled(t *testing.T) {
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(closureModule(t, closureProgram)))
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	output, err := New().WithPackageDir(closureModule(t, closureProgram)).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	// The specialized callees and the lifted literals are plain functions;
	// no function pointer is passed at the rewritten call sites.
	for _, want := range []string{"0clos_0_scale_all", "0clos_lit_0", "0clos_1_fold", "0clos_2_fold", "0clos_3_each_index", "0clos_lit_3"} {
		if !strings.Contains(output, want) {
			t.Fatalf("specialized function %s missing from the C:\n%s", want, output)
		}
	}
}

// Every capture outside the justified shape still reaches the checker's
// rejection, with the captured names listed.
func TestE2ECapturingClosureRejections(t *testing.T) {
	cases := map[string]string{
		"unannotated local": `package main
apply: (f: (u32) -> u32, x: u32): u32 = f(x)
main: (): i32 {
  k := u32(3)
  i32_bits_u32(apply(fn(x: u32): u32 = x * k, u32(2)))
}
`,
		"record capture": `package main
Pair: type = struct { a: u32, b: u32 }
apply: (f: (u32) -> u32, x: u32): u32 = f(x)
main: (): i32 {
  p: Pair = Pair { a: u32(1), b: u32(2) }
  i32_bits_u32(apply(fn(x: u32): u32 = x + p.a, u32(2)))
}
`,
		"callee returns its parameter": `package main
keep: (f: (u32) -> u32): (u32) -> u32 = f
main: (): i32 {
  k: u32 = u32(3)
  g: (u32) -> u32 = keep(fn(x: u32): u32 = x + k)
  i32_bits_u32(g(u32(1)))
}
`,
		"literal bound before the call": `package main
apply: (f: (u32) -> u32, x: u32): u32 = f(x)
main: (): i32 {
  k: u32 = u32(3)
  g := fn(x: u32): u32 = x * k
  i32_bits_u32(apply(g, u32(2)))
}
`,
		"assigns the capture": `package main
apply: (f: (u32) -> u32, x: u32): u32 = f(x)
main: (): i32 {
  k: u32 = u32(3)
  i32_bits_u32(apply(fn(x: u32): u32 { k = k + x; k }, u32(2)))
}
`,
	}
	for name, program := range cases {
		t.Run(name, func(t *testing.T) {
			_, err := New().WithPackageDir(closureModule(t, program)).Check().Get()
			if err == nil || !strings.Contains(err.Error(), "OAK-T0401") {
				t.Fatalf("want OAK-T0401, got %v", err)
			}
		})
	}
}

// A captured span is the borrowed parameter it always was: a second span of
// the same owner at the specialized call is the borrow checker's ordinary
// exclusivity rejection, not a silent alias.
func TestE2ECapturingClosureSpanExclusivity(t *testing.T) {
	program := `package main
each_index: (f: (u32) -> (), s: [*]u32): () {
  i: u32 = u32(0)
  while i < len(s) {
    f(i)
    i = i + u32(1)
  }
}
main: (): i32 {
  data: [2]u32
  mine: [*]u32 = span(&data)
  each_index(fn(i: u32): () { mine[i] = i }, span(&data))
  0
}
`
	_, err := New().WithPackageDir(closureModule(t, program)).Check().Get()
	if err == nil {
		t.Fatal("two writable spans of one owner at the specialized call were accepted")
	}
}
