package compiler

import (
	"strings"
	"testing"
)

// Kernels (docs/spec/56-kernels.md): a `kernel` declaration is a function
// in the kernel subset that the C backend compiles as an ordinary function
// (its first parameter the grid position), the Metal emitter as a compute
// kernel, and the Lean extraction as a definition.

const kernelProgram = `
// A pure helper both kernels share.
clamp_relu: (x: f32): f32 = x < 0.0 ? 0.0 | x

// Elementwise ReLU: one thread per element.
kernel relu: (gid: u32, x: []f32, y: [*]f32): () = {
  gid < len(y) ? { y[gid] = clamp_relu(x[gid]) }
}

// y = a * x + y over a tile of elements per thread.
kernel axpy: (gid: u32, a: f32, x: []f32, y: [*]f32, tile: u32): () = {
  base: u32 = gid * tile
  k: u32 = 0
  while k < tile {
    i: u32 = base + k
    i < len(y) ? { y[i] = a * x[i] + y[i] }
    k = k + 1
  }
}

main: (): i32 = {
  xs: [4]f32 = [-1.0, 2.0, -3.0, 4.0]
  ys: [4]f32 = [0.0, 0.0, 0.0, 0.0]
  g: u32 = 0
  while g < 4 {
    relu(g, view(&xs), span(&ys))
    g = g + 1
  }
  a: f32 = 2.0
  axpy(0, a, view(&xs), span(&ys), 4)
  ys[0] == -2.0 && ys[1] == 6.0 && ys[2] == -6.0 && ys[3] == 12.0 ? 42 | 1
}
`

// The C realization: the host loop over grid positions computes the kernels.
func TestE2EKernelsRunOnTheHost(t *testing.T) {
	code, abnormal := buildAndRun(t, "kernels_host", kernelProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// The Metal realization: signatures with buffer indices, the descriptor
// lines the host binds by, checked indices raising the fault word, the
// shared helper emitted once, and the safe-math pragmas.
func TestKernelsEmitMetal(t *testing.T) {
	result, err := New().WithSource("kernels.oak", kernelProgram).EmitMetal().Get()
	if err != nil {
		t.Fatal(err)
	}
	if len(result.Kernels) != 2 || result.Kernels[0].Name != "relu" || result.Kernels[1].Name != "axpy" {
		t.Fatalf("kernels = %+v", result.Kernels)
	}
	relu := result.Kernels[0]
	if relu.Fault != 4 || len(relu.Params) != 3 || relu.Params[1].Kind != "view" || relu.Params[2].Kind != "span" || relu.Params[2].Buffers[0] != 2 {
		t.Fatalf("relu descriptor = %+v", relu)
	}
	if strings.Join(relu.Reach, " ") != "clamp_relu relu" {
		t.Fatalf("reach = %v", relu.Reach)
	}
	for _, want := range []string{
		"// oak-kernel relu: gid grid; x view f32 buffer 0,1; y span f32 buffer 2,3; fault buffer 4",
		"// oak-kernel axpy: gid grid; a scalar f32 buffer 0; x view f32 buffer 1,2; y span f32 buffer 3,4; tile scalar u32 buffer 5; fault buffer 6",
		"#pragma METAL fp math_mode(safe)",
		"kernel void relu(uint gid [[thread_position_in_grid]], device const float* x [[buffer(0)]], constant uint& x_len [[buffer(1)]], device float* y [[buffer(2)]], constant uint& y_len [[buffer(3)]], device atomic_uint* oak_fault [[buffer(4)]]) {",
		"static inline float clamp_relu(float x, device atomic_uint* oak_fault) {\n  return ((x < 0.0f) ? 0.0f : x);\n}",
		"y[oak_check(gid, y_len, oak_fault)] = clamp_relu(x[oak_check(gid, x_len, oak_fault)], oak_fault);",
		"constant float& a [[buffer(0)]]",
		"y[oak_check(i, y_len, oak_fault)] = ((a * x[oak_check(i, x_len, oak_fault)]) + y[oak_check(i, y_len, oak_fault)]);",
		"while (k < tile) {",
		"k = (k + 1u);",
	} {
		if !strings.Contains(result.Source, want) {
			t.Fatalf("missing %q in:\n%s", want, result.Source)
		}
	}
	if strings.Count(result.Source, "static inline float clamp_relu") != 1 {
		t.Fatalf("the helper must be emitted once:\n%s", result.Source)
	}
	// A program without kernels emits nothing.
	empty, err := New().WithSource("plain.oak", "main: (): i32 = 0\n").EmitMetal().Get()
	if err != nil || empty.Source != "" || len(empty.Kernels) != 0 {
		t.Fatalf("plain program: %v %+v", err, empty)
	}
}

// Integer semantics survive the translation: narrow and signed arithmetic
// wraps through unsigned casts, division and shifts go through the trapping
// helpers, conversions are casts, Bool conditionals become ternaries.
func TestKernelsEmitMetalIntegerForms(t *testing.T) {
	src := `
kernel ints: (gid: u32, a: []u8, b: [*]i32, c: [*]u64): () = {
  v: u8 = a[gid] + 200
  q: i32 = b[gid] / 3
  s: u64 = c[gid] << 3
  neg: i32 = -q
  b[gid] = q % 7 + neg
  c[gid] = s + u64(v) + (v > 100 ? u64(1) | u64(0))
}
main: (): i32 = 0
`
	result, err := New().WithSource("ints.oak", src).EmitMetal().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"uchar v = (uchar)((uchar)a[oak_check(gid, a_len, oak_fault)] + (uchar)((uchar)200));",
		"int q = oak_div_int(b[oak_check(gid, b_len, oak_fault)], 3, oak_fault);",
		"ulong s = oak_shl_ulong(c[oak_check(gid, c_len, oak_fault)], 3uL, oak_fault);",
		"int neg = (int)(0u - (uint)q);",
		"(int)((uint)oak_rem_int(q, 7, oak_fault) + (uint)neg)",
		"((v > ((uchar)100)) ? ((ulong)1uL) : ((ulong)0uL))",
	} {
		if !strings.Contains(result.Source, want) {
			t.Fatalf("missing %q in:\n%s", want, result.Source)
		}
	}
}

// Kernels are held to the subset in every build, Metal requested or not.
func TestKernelsRejectedOutsideTheSubset(t *testing.T) {
	cases := map[string][2]string{
		"first parameter": {`kernel k: (n: i32, y: [*]f32): () = { y[0] = 1.0 }
main: (): i32 = 0`, CodeKernelSubset},
		"f64": {`kernel k: (gid: u32, y: [*]f64): () = { y[gid] = 1.0 }
main: (): i32 = 0`, CodeKernelSubset},
		"fixed array": {`kernel k: (gid: u32, y: [4]f32): () = {}
main: (): i32 = 0`, CodeKernelSubset},
		"result": {`kernel k: (gid: u32, x: []f32): f32 = x[gid]
main: (): i32 = 0`, CodeKernelSubset},
		"kernel calls kernel": {`kernel a: (gid: u32, y: [*]f32): () = { y[gid] = 1.0 }
kernel b: (gid: u32, y: [*]f32): () = { a(gid, y) }
main: (): i32 = 0`, CodeKernelSubset},
		"unbounded loop": {`kernel k: (gid: u32, y: [*]f32): () = {
  i: u32 = 0
  while i != gid { i = i + 1 }
  y[0] = 1.0
}
main: (): i32 = 0`, CodeKernelLoop},
		"effect": {`host_read: (x: c.UInt32): c.UInt32 effects { Host.Read } = c.extern("oak_host_read")
peek: (x: u32): u32 = u32(host_read(c.UInt32(x)))
kernel k: (gid: u32, y: [*]u32): () = { y[gid] = peek(gid) }
main: (): i32 = 0`, CodeKernelEffect},
		"unknown effect": {`mystery: (x: c.UInt32): c.UInt32 = c.extern("mystery")
peek: (x: u32): u32 = u32(mystery(c.UInt32(x)))
kernel k: (gid: u32, y: [*]u32): () = { y[gid] = peek(gid) }
main: (): i32 = 0`, CodeKernelEffect},
	}
	for name, c := range cases {
		_, err := New().WithSource("k.oak", c[0]).EmitC().Get()
		if err == nil {
			t.Fatalf("%s: compiled; want %s", name, c[1])
		}
		if !strings.Contains(err.Error(), c[1]) {
			t.Fatalf("%s: want %s, got %v", name, c[1], err)
		}
	}
}

// The declaration prints back, and the kernel body extracts to Lean like
// any function (the Lean image is what theorems about the kernel name).
func TestKernelsSyntaxAndExtraction(t *testing.T) {
	tree, err := New().WithSource("kernels.oak", kernelProgram).Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	if printed := tree.Root.String(); !strings.Contains(printed, "kernel relu(gid: u32") {
		t.Fatalf("kernel must print back: %s", printed)
	}
	extracted, err := New().WithSource("kernels.oak", kernelProgram).EmitLean("Oak.KernelsTest").Get()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(extracted, "def relu (gid : UInt32)") || !strings.Contains(extracted, "def axpy (gid : UInt32)") {
		t.Fatalf("kernels must extract:\n%s", extracted)
	}
	// `kernel` stays an ordinary identifier elsewhere.
	if _, err := New().WithSource("ident.oak", "main: (): i32 = {\n  kernel: i32 = 42\n  kernel\n}\n").EmitC().Get(); err != nil {
		t.Fatalf("kernel as a binding name: %v", err)
	}
}
