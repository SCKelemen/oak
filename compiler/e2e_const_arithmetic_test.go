package compiler

import (
	"strings"
	"testing"
)

// Const arithmetic in array lengths (docs/spec/20-types.md §11.0, the ml
// ask for size-indexed kernels): [M*K]T, [K*N]T, and [M*N]T in a template
// fold to literals at instantiation, in parameters, the return type, and
// body declarations alike. A product does not determine its factors, so
// matmul takes its dimensions explicitly; pad infers N from a plain
// position and returns [N+1]T.
func TestE2EConstArithmeticLengths(t *testing.T) {
	src := `
matmul[M: u32, N: u32, K: u32]: (a: [M*K]u32, b: [K*N]u32): [M*N]u32 {
  out: [M*N]u32
  i: u32 = 0
  while i < M {
    j: u32 = 0
    while j < N {
      acc: u32 = 0
      k: u32 = 0
      while k < K {
        acc = acc + a[i*K + k] * b[k*N + j]
        k = k + 1
      }
      out[i*N + j] = acc
      j = j + 1
    }
    i = i + 1
  }
  out
}
pad[N: u32]: (v: [N]u32): [N+1]u32 {
  out: [N+1]u32
  i: u32 = 0
  while i < N {
    out[i] = v[i]
    i = i + 1
  }
  out[N] = 99
  out
}
main: (): i32 {
  a: [6]u32 = [6]u32{ 1, 2, 3, 4, 5, 6 }
  b: [3]u32 = [3]u32{ 1, 1, 1 }
  c: [2]u32 = matmul[2, 1, 3](a, b)
  assert(c[0] == 6)
  assert(c[1] == 15)
  square: [4]u32 = matmul[2, 2, 2]([4]u32{ 1, 2, 3, 4 }, [4]u32{ 1, 0, 0, 1 })
  assert(square[0] == 1 && square[1] == 2 && square[2] == 3 && square[3] == 4)
  p: [4]u32 = pad(b)
  assert(len(p) == 4)
  assert(p[3] == 99)
  assert(p[0] + p[1] + p[2] + c[0] + c[1] + square[3] + 14 == 42)
  42
}
`
	output, err := New().WithSource("constarith.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, want := range []string{
		"oak_arr_u32_2 oak_matmul_2_1_3( oak_arr_u32_6 a, oak_arr_u32_3 b )",
		"oak_arr_u32_4 oak_matmul_2_2_2( oak_arr_u32_4 a, oak_arr_u32_4 b )",
		"oak_arr_u32_4 oak_pad_3( oak_arr_u32_3 v )",
		"oak_arr_u32_4 out = {0};",
	} {
		if !strings.Contains(output, want) {
			t.Fatalf("generated C lacks %q:\n%s", want, output)
		}
	}
	for _, stale := range []string{"M*", "N+1", "OAK_UNSUPPORTED"} {
		if strings.Contains(output, stale) {
			t.Fatalf("a symbolic extent reached the backend (%q):\n%s", stale, output)
		}
	}
	code, abnormal := buildAndRun(t, "constarith", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if interpreted := interpretChecked(t, src); interpreted != 42 {
		t.Fatalf("interpreter returned %d", interpreted)
	}
}

// A folded length that disagrees with the argument is a type error at the
// call, and a fold that is not a valid length rejects the instantiation.
func TestConstArithmeticRejections(t *testing.T) {
	cases := []struct{ name, src, want string }{
		{"length-mismatch", `
f[M: u32, K: u32]: (a: [M*K]u32): u32 { M }
main: (): i32 { a: [5]u32
 f[2, 3](a)
 0 }`, "[6]u32"},
		{"underflow", `
g[N: u32]: (v: [N]u32): [N-4]u32 { out: [N-4]u32
 out }
main: (): i32 { v: [2]u32
 g(v)
 0 }`, "cannot instantiate"},
		{"unbound-factor", `
h[M: u32, K: u32]: (a: [M*K]u32): u32 { M }
main: (): i32 { a: [6]u32
 h(a)
 0 }`, "K"},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			_, err := New().WithSource(c.name+".oak", c.src).Check().Get()
			if err == nil || !strings.Contains(err.Error(), c.want) {
				t.Fatalf("%s: want %q, got %v", c.name, c.want, err)
			}
		})
	}
}
