package compiler

import (
	"strings"
	"testing"
)

// Const-generic functions (docs/spec/20-types.md §11.0/§11.2): a type
// parameter with an integer kind is a value parameter. It is inferred from
// an owned array argument's static length or given explicitly, each
// instantiation is its own monomorphized function, and the parameter is an
// ordinary integer constant in the body.
func TestE2EConstGenericFunctions(t *testing.T) {
	src := `
sum[N: u32]: (v: [N]u32): u32 {
  i: u32 = 0
  acc: u32 = 0
  while i < N {
    acc = acc + v[i]
    i = i + 1
  }
  acc
}
capacity[N: u32]: (v: [N]u8): u32 {
  N
}
main: (): i32 {
  a: [3]u32 = [3]u32{ 1, 2, 39 }
  b: [4]u32 = [4]u32{ 10, 10, 10, 12 }
  bytes: [8]u8
  assert(sum(a) == 42)
  assert(sum(b) == 42)
  assert(sum[3](a) == 42)
  assert(capacity(bytes) == 8)
  42
}
`
	output, err := New().WithSource("constgen.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, want := range []string{"oak_sum_3(", "oak_sum_4(", "oak_capacity_8("} {
		if !strings.Contains(output, want) {
			t.Fatalf("generated C lacks instantiation %q:\n%s", want, output)
		}
	}
	if strings.Contains(output, "oak_sum(") || strings.Contains(output, "[N]") {
		t.Fatalf("the template leaked into the generated C:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "constgen", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if interpreted := interpretChecked(t, src); interpreted != 42 {
		t.Fatalf("interpreter returned %d", interpreted)
	}
}

// A generic function over a const-parameterized record recovers both the
// type and the const argument from the record instantiation.
func TestE2EGenericOverConstRecord(t *testing.T) {
	src := `
Ring[T, N: u32]: type = struct { buffer: [N]T, head: u32 }
size[T, N: u32]: (r: Ring[T, N]): u32 {
  N
}
first[T, N: u32]: (r: Ring[T, N]): T {
  r.buffer[0]
}
main: (): i32 {
  r: Ring[u8, 8]
  r.buffer[0] = 42
  wide: Ring[u32, 4]
  assert(size(r) == 8)
  assert(size(wide) == 4)
  u32(first(r)) == 42 ? { 42 } | { 1 }
}
`
	output, err := New().WithSource("ringgen.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, want := range []string{"oak_size_u8_8(", "oak_size_u32_4(", "oak_first_u8_8("} {
		if !strings.Contains(output, want) {
			t.Fatalf("generated C lacks instantiation %q:\n%s", want, output)
		}
	}
	code, abnormal := buildAndRun(t, "ringgen", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// Misuse is rejected at the call site: a type where a const is declared, a
// literal outside the kind's range, and one const parameter bound to two
// lengths.
func TestConstGenericRejections(t *testing.T) {
	cases := []struct{ name, src, want string }{
		{"type-for-const", "f[N: u32]: (v: [N]u8): u32 { N }\nmain: (): i32 { a: [2]u8\n f[u8](a)\n 0 }", "const parameter N"},
		{"out-of-kind", "f[N: u8]: (v: [N]u8): u32 { 0 }\nmain: (): i32 { a: [300]u8\n f(a)\n 0 }", "does not fit"},
		{"two-lengths", "f[N: u32]: (a: [N]u8, b: [N]u8): u32 { N }\nmain: (): i32 { a: [2]u8\n b: [3]u8\n f(a, b)\n 0 }", "bound to both"},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			_, err := New().WithSource(c.name+".oak", c.src).Check().Get()
			if err == nil || !strings.Contains(err.Error(), c.want) {
				t.Fatalf("%s: want %q, got %v", c.name, c.want, err)
			}
		})
	}
	// An unknown interface requirement keeps its diagnostic code.
	_, err := New().WithSource("req.oak", "g[T: MissingRequirement]: (x: T): T { x }\nmain: (): i32 { 0 }").Check().Get()
	if err == nil || !strings.Contains(err.Error(), "OAK-T0101") {
		t.Fatalf("unknown requirement must still be OAK-T0101, got %v", err)
	}
}
