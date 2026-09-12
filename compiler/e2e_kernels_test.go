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
		"// oak-kernel relu: gid grid; x view f32 buffer 0,1; y span f32 buffer 2,3; fault buffer 4; independence element",
		"// oak-kernel axpy: gid grid; a scalar f32 buffer 0; x view f32 buffer 1,2; y span f32 buffer 3,4; tile scalar u32 buffer 5; fault buffer 6; independence tile tile",
		"#pragma METAL fp math_mode(safe)",
		"kernel void relu(uint gid [[thread_position_in_grid]], device const float* x [[buffer(0)]], constant uint& x_len [[buffer(1)]], device float* y [[buffer(2)]], constant uint& y_len [[buffer(3)]], device atomic_uint* oak_fault [[buffer(4)]]) {",
		"static inline float clamp_relu(float x, device atomic_uint* oak_fault) {\n  return ((x < 0.0f) ? 0.0f : x);\n}",
		// The guard `gid < len(y)` discharges the store; x's length is
		// unknown, so the load stays checked.
		"y[gid] = clamp_relu(x[oak_check(gid, x_len, oak_fault)], oak_fault);",
		"constant float& a [[buffer(0)]]",
		"y[i] = ((a * x[oak_check(i, x_len, oak_fault)]) + y[i]);",
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

// Bounds checks the checker discharges (typechecker/extents.go) are elided
// in the emitted Metal: a same-length guard transfers the bound to the
// second buffer, and a canonical loop bound over a binding of len(x)
// proves every access in its body.
func TestKernelsElideProvenChecks(t *testing.T) {
	src := `
kernel saxpy: (gid: u32, a: f32, x: []f32, y: [*]f32): () = {
  len(x) == len(y) && gid < len(y) ? { y[gid] = a * x[gid] + y[gid] }
}

kernel prefix: (gid: u32, x: []f32, out: [*]f32): () = {
  n: u32 = len(x)
  acc: f32 = 0.0
  i: u32 = 0
  while i < n {
    acc = acc + x[i]
    i = i + 1
  }
  gid < len(out) ? { out[gid] = acc }
}
main: (): i32 = 0
`
	result, err := New().WithSource("elide.oak", src).EmitMetal().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"y[gid] = ((a * x[gid]) + y[gid]);",
		"acc = (acc + x[i]);",
		"out[gid] = acc;",
	} {
		if !strings.Contains(result.Source, want) {
			t.Fatalf("missing %q in:\n%s", want, result.Source)
		}
	}
	if strings.Contains(result.Source, "oak_check(") && strings.Count(result.Source, "oak_check(") > 1 {
		// The prelude defines oak_check once; no call site should remain.
		t.Fatalf("a check survived a proof:\n%s", result.Source)
	}
}

// Thread independence (docs/spec/56-kernels.md section 6, OAK-K0104): a
// span access at anything but the grid position or a tile index is
// rejected, as is a span handed to a helper or a reassigned grid position;
// the tile shape through a literal width is admitted.
func TestKernelsIndependence(t *testing.T) {
	cases := map[string]string{
		"neighbour": `kernel k: (gid: u32, y: [*]f32): () = { gid + 1 < len(y) ? { y[gid + 1] = 1.0 } }
main: (): i32 = 0`,
		"span to helper": `store: (s: [*]f32, i: u32): () = { i < len(s) ? { s[i] = 1.0 } }
kernel k: (gid: u32, y: [*]f32): () = { store(y, gid) }
main: (): i32 = 0`,
		"gid reassigned": `kernel k: (gid: u32, y: [*]f32): () = {
  gid = gid / 2
  gid < len(y) ? { y[gid] = 1.0 }
}
main: (): i32 = 0`,
		"counter not last": `kernel kern: (gid: u32, y: [*]f32, tile: u32): () = {
  k: u32 = 0
  while k < tile {
    k = k + 1
    i: u32 = gid * tile + k
    i < len(y) ? { y[i] = 1.0 }
  }
}
main: (): i32 = 0`,
		"read across tiles": `kernel kern: (gid: u32, y: [*]f32, tile: u32): () = {
  k: u32 = 0
  while k < tile {
    i: u32 = gid * tile + k
    i + 1 < len(y) ? { y[i] = y[i + 1] }
    k = k + 1
  }
}
main: (): i32 = 0`,
	}
	for name, src := range cases {
		_, err := New().WithSource("indep.oak", src).EmitC().Get()
		if err == nil {
			t.Fatalf("%s: compiled; want %s", name, CodeKernelIndependence)
		}
		if !strings.Contains(err.Error(), CodeKernelIndependence) {
			t.Fatalf("%s: want %s, got %v", name, CodeKernelIndependence, err)
		}
	}
	admitted := `
kernel quad: (gid: u32, x: []f32, y: [*]f32): () = {
  k: u32 = 0
  while k < 4 {
    i: u32 = 4 * gid + k
    i < len(y) ? { y[i] = x[gid] * y[i] }
    k = k + 1
  }
}
main: (): i32 = 0
`
	result, err := New().WithSource("quad.oak", admitted).EmitMetal().Get()
	if err != nil {
		t.Fatal(err)
	}
	if result.Kernels[0].Independence != "tile 4" || !strings.Contains(result.Source, "independence tile 4") {
		t.Fatalf("descriptor = %+v", result.Kernels[0])
	}
}

// A per-thread reduction inside a kernel: reduce.tree over a window of the
// input, its combine bound to a named function, so the grouping in Metal
// is the binary-counter tree the host computes. Exercises buffer windows
// (subslice), fixed-size thread-private arrays, specialized helpers, and
// value-position conditionals in result position.
const kernelReduceProgram = `package main

r := import("reduce")

add: (a: f32, b: f32): f32 = a + b

kernel tile_sum: (gid: u32, x: []f32, partials: [*]f32, tile: u32): () = {
  start: u32 = gid * tile
  start + tile <= len(x) && gid < len(partials) ? {
    part: []f32 = subslice(x, start, tile)
    zero: f32 = 0.0
    partials[gid] = r.tree(part, zero, add)
  }
}

main: (): i32 = {
  xs: [8]f32 = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]
  ps: [2]f32 = [0.0, 0.0]
  tile_sum(0, view(&xs), span(&ps), 4)
  tile_sum(1, view(&xs), span(&ps), 4)
  ps[0] == 10.0 && ps[1] == 26.0 ? 42 | 1
}
`

func TestE2EKernelsReduceTree(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": kernelReduceProgram})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	result, err := New().WithPackageDir(root).EmitMetal().Get()
	if err != nil {
		t.Fatal(err)
	}
	src := result.Source
	for _, want := range []string{
		"// oak-kernel tile_sum: gid grid; x view f32 buffer 0,1; partials span f32 buffer 2,3; tile scalar u32 buffer 4; fault buffer 5; independence element",
		"static inline float add(float a, float b, device atomic_uint* oak_fault) {",
		"static inline float reduce__tree_f32__add(device const float* xs, uint xs_len, float zero, device atomic_uint* oak_fault) {",
		"float stack[64] = { zero, zero,",
		"uchar levels[64] = {",
		"stack[oak_check((count - 2u), 64u, oak_fault)] = add(stack[oak_check((count - 2u), 64u, oak_fault)], stack[oak_check((count - 1u), 64u, oak_fault)], oak_fault);",
		"if (count == 0u) {\n    return zero;\n  } else {",
		"uint part_len = tile;\n    device const float* part = x + oak_subslice(start, part_len, x_len, oak_fault);",
		"partials[gid] = reduce__tree_f32__add(part, part_len, zero, oak_fault);",
	} {
		if !strings.Contains(src, want) {
			t.Fatalf("missing %q in:\n%s", want, src)
		}
	}
	// Callee-first: the bound function precedes the helper that calls it.
	if strings.Index(src, "static inline float add(") > strings.Index(src, "static inline float reduce__tree_f32__add(") {
		t.Fatalf("helpers must be emitted callee-first:\n%s", src)
	}
	// The window's loads are proven by the helper's own loop bound.
	if !strings.Contains(src, "stack[oak_check(count, 64u, oak_fault)] = xs[i];") {
		t.Fatalf("the loop-bounded load must be raw:\n%s", src)
	}
}

// The new forms fail closed where the rules require: a span window hides
// the indices independence is judged on, fixed arrays and function values
// are not kernel parameters, and a function parameter takes a named
// function.
func TestKernelsReduceTreeRejections(t *testing.T) {
	cases := map[string][2]string{
		"span window to helper": {`fill: (s: [*]f32): () = { s[0] = 1.0 }
kernel k: (gid: u32, y: [*]f32, tile: u32): () = {
  gid * tile + tile <= len(y) ? {
    w: [*]f32 = subslice(y, gid * tile, tile)
    fill(w)
  }
}
main: (): i32 = 0`, CodeKernelIndependence},
		"fixed array parameter": {`kernel k: (gid: u32, t: [4]f32, y: [*]f32): () = { y[gid] = t[0] }
main: (): i32 = 0`, CodeKernelSubset},
		"function parameter on a kernel": {`kernel k: (gid: u32, f: (f32) -> f32 effects { }, y: [*]f32): () = { y[gid] = f(1.0) }
main: (): i32 = 0`, CodeKernelSubset},
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

// Records as kernel parameters (docs/spec/56-kernels.md section 1): a
// kernel takes a Tensor2 and a MutTensor2; the Metal entry flattens each
// record into its fields' buffers and rebuilds the struct for the body,
// helpers take records by value, and a failed assert raises fault 5.
const kernelRecordProgram = `package main

t := import("tensor")

kernel relu_t[R, S]: (gid: u32, x: t.Tensor2[R], out: t.MutTensor2[S]): () = {
  gid < len(out.data) && gid < x.rows * x.cols ? {
    i: u32 = gid / x.cols
    j: u32 = gid % x.cols
    v: f32 = t.tensor_at(x, i, j)
    out.data[gid] = v < 0.0 ? 0.0 | v
  }
}

main: (): i32 = {
  xs: [4]f32 = [-1.0, 2.0, -3.0, 4.0]
  ys: [4]f32 = [0.0, 0.0, 0.0, 0.0]
  a: t.Tensor2 = t.tensor_of(view(&xs), 2, 2)
  {
    o: t.MutTensor2 = t.tensor_mut_of(span(&ys), 2, 2)
    g: u32 = 0
    while g < 4 {
      relu_t(g, a, o)
      g = g + 1
    }
  }
  ys[0] == 0.0 && ys[1] == 2.0 && ys[2] == 0.0 && ys[3] == 4.0 ? 42 | 1
}
`

func TestE2EKernelsRecordParameters(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": kernelRecordProgram})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	result, err := New().WithPackageDir(root).EmitMetal().Get()
	if err != nil {
		t.Fatal(err)
	}
	src := result.Source
	for _, want := range []string{
		"// oak-kernel relu_t: gid grid; x.data view f32 buffer 0,1; x.rows scalar u32 buffer 2; x.cols scalar u32 buffer 3; x.row_stride scalar u32 buffer 4; x.col_stride scalar u32 buffer 5; x.offset scalar u32 buffer 6; out.data span f32 buffer 7,8; out.rows scalar u32 buffer 9; out.cols scalar u32 buffer 10; out.row_stride scalar u32 buffer 11; out.col_stride scalar u32 buffer 12; out.offset scalar u32 buffer 13; fault buffer 14; independence element",
		"struct tensor__Tensor2 {\n  device const float* data;\n  uint data_len;\n  uint rows;",
		"struct tensor__MutTensor2 {\n  device float* data;\n  uint data_len;",
		"device const float* x__data [[buffer(0)]], constant uint& x__data_len [[buffer(1)]], constant uint& x__rows [[buffer(2)]]",
		"  tensor__Tensor2 x = { x__data, x__data_len, x__rows, x__cols, x__row_stride, x__col_stride, x__offset };",
		"static inline float tensor__tensor_uat(tensor__Tensor2 t, uint i, uint j, device atomic_uint* oak_fault) {",
		"if (!((i < rows) && (j < cols))) { oak_raise(oak_fault, 5u); return (uint)0; }",
		"return t.data[oak_check(tensor__tensor_uindex(t.rows, t.cols, t.row_stride, t.col_stride, t.offset, i, j, oak_fault), t.data_len, oak_fault)];",
		"out.data[gid] = ((v < 0.0f) ? 0.0f : v);",
	} {
		if !strings.Contains(src, want) {
			t.Fatalf("missing %q in:\n%s", want, src)
		}
	}
	if len(result.Kernels[0].Params) != 13 || result.Kernels[0].Params[7].Name != "out.data" || result.Kernels[0].Params[7].Kind != "span" {
		t.Fatalf("descriptor = %+v", result.Kernels[0].Params)
	}
}

// A record holding a span cannot leave the kernel's sight: handing it to a
// helper, windowing its span field, or rebuilding it in a literal is
// rejected; a record inside a record is outside the subset.
func TestKernelsRecordRejections(t *testing.T) {
	prelude := "t := import(\"tensor\")\n\n"
	cases := map[string][2]string{
		"span record to helper": {prelude + `kernel k[R, S]: (gid: u32, x: t.Tensor2[R], out: t.MutTensor2[S]): () = {
  gid < out.rows && gid < x.rows ? { t.tensor_set(out, gid, 0, t.tensor_at(x, gid, 0)) }
}
main: (): i32 = 0`, CodeKernelIndependence},
		"span field windowed": {prelude + `kernel k[S]: (gid: u32, out: t.MutTensor2[S]): () = {
  gid + 1 <= len(out.data) ? {
    w: [*]f32 = subslice(out.data, gid, 1)
    w[0] = 1.0
  }
}
main: (): i32 = 0`, CodeKernelIndependence},
		"nested record": {`Inner: type = struct { a: u32 }
Outer: type = struct { in: Inner, k: u32 }
kernel k: (gid: u32, o: Outer, y: [*]u32): () = { y[gid] = o.k }
main: (): i32 = 0`, CodeKernelSubset},
	}
	for name, c := range cases {
		root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": "package main\n\n" + c[0] + "\n"})
		_, err := New().WithPackageDir(root).EmitC().Get()
		if err == nil {
			t.Fatalf("%s: compiled; want %s", name, c[1])
		}
		if !strings.Contains(err.Error(), c[1]) {
			t.Fatalf("%s: want %s, got %v", name, c[1], err)
		}
	}
}

// A cooperative reduction (docs/spec/56-kernels.md section 7):
// reduce.group_tree in a kernel makes it a group kernel — a threadgroup per
// position — whose threads load the window into threadgroup scratch and
// combine pairwise-adjacent with doubling stride, the binary-counter
// grouping reduce.tree computes on the host (Oak.Reduce.coop_eq_tree).
const kernelGroupProgram = `package main

r := import("reduce")

add: (a: f32, b: f32): f32 = a + b

kernel group_sums: (gid: u32, x: []f32, partials: [*]f32): () = {
  n: u32 = len(x)
  lo: u32 = gid * 4
  gid < len(partials) && lo <= n ? {
    m: u32 = lo + 4 <= n ? 4 | n - lo
    zero: f32 = 0.0
    partials[gid] = r.group_tree(4, x, lo, m, zero, add)
  }
}

main: (): i32 = {
  xs: [10]f32 = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0]
  ps: [3]f32 = [0.0, 0.0, 0.0]
  g: u32 = 0
  while g < 3 {
    group_sums(g, view(&xs), span(&ps))
    g = g + 1
  }
  zero: f32 = 0.0
  total: f32 = r.tree(view(&ps), zero, add)
  ps[0] == 10.0 && ps[1] == 26.0 && ps[2] == 19.0 && total == 55.0 ? 42 | 1
}
`

func TestE2EKernelsGroupTree(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": kernelGroupProgram})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	result, err := New().WithPackageDir(root).EmitMetal().Get()
	if err != nil {
		t.Fatal(err)
	}
	src := result.Source
	for _, want := range []string{
		"// oak-kernel group_sums: gid group; x view f32 buffer 0,1; partials span f32 buffer 2,3; fault buffer 4; independence element; threadgroup 4",
		"kernel void group_sums(uint gid [[threadgroup_position_in_grid]], uint oak_lid [[thread_position_in_threadgroup]], device const float* x [[buffer(0)]]",
		"  threadgroup float oak_scratch1[4];",
		"if ((ulong)oak_lo1 + (ulong)oak_m1 > (ulong)x_len) { oak_raise(oak_fault, 4u); oak_m1 = 0u; }",
		"if (oak_m1 > 4u) { oak_raise(oak_fault, 5u); oak_m1 = 0u; }",
		"oak_scratch1[oak_lid] = (oak_lid < oak_m1) ? x[oak_lo1 + oak_lid] : oak_gt1;",
		"threadgroup_barrier(mem_flags::mem_threadgroup);",
		"for (uint oak_s = 1u; oak_s < 4u; oak_s <<= 1u) {",
		"if ((oak_lid % (2u * oak_s)) == 0u && oak_lid + oak_s < oak_m1) { oak_scratch1[oak_lid] = add(oak_scratch1[oak_lid], oak_scratch1[oak_lid + oak_s], oak_fault); }",
		"if (oak_m1 > 0u) { oak_gt1 = oak_scratch1[0]; }",
		"if (oak_lid == 0u) { partials[gid] = oak_gt1; }",
	} {
		if !strings.Contains(src, want) {
			t.Fatalf("missing %q in:\n%s", want, src)
		}
	}
	if result.Kernels[0].Threadgroup != 4 || result.Kernels[0].Params[0].Kind != "group" {
		t.Fatalf("descriptor = %+v", result.Kernels[0])
	}
}

// The group is a literal power of two shared by the kernel's calls, and
// the call belongs in a kernel body.
func TestKernelsGroupTreeRejections(t *testing.T) {
	prelude := "r := import(\"reduce\")\n\nadd: (a: f32, b: f32): f32 = a + b\n\n"
	cases := map[string]string{
		"variable group": prelude + `kernel k: (gid: u32, x: []f32, p: [*]f32, g: u32): () = {
  zero: f32 = 0.0
  gid < len(p) ? { p[gid] = r.group_tree(g, x, 0, 1, zero, add) }
}
main: (): i32 = 0`,
		"not a power of two": prelude + `kernel k: (gid: u32, x: []f32, p: [*]f32): () = {
  zero: f32 = 0.0
  gid < len(p) ? { p[gid] = r.group_tree(6, x, 0, 1, zero, add) }
}
main: (): i32 = 0`,
		"two sizes": prelude + `kernel k: (gid: u32, x: []f32, p: [*]f32): () = {
  zero: f32 = 0.0
  gid < len(p) ? { p[gid] = r.group_tree(4, x, 0, 1, zero, add) + r.group_tree(8, x, 0, 1, zero, add) }
}
main: (): i32 = 0`,
		"in a helper": prelude + `part: (x: []f32): f32 = {
  zero: f32 = 0.0
  r.group_tree(4, x, 0, 1, zero, add)
}
kernel k: (gid: u32, x: []f32, p: [*]f32): () = { gid < len(p) ? { p[gid] = part(x) } }
main: (): i32 = 0`,
	}
	for name, src := range cases {
		root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": "package main\n\n" + src + "\n"})
		_, err := New().WithPackageDir(root).EmitC().Get()
		if err == nil {
			t.Fatalf("%s: compiled; want %s", name, CodeKernelSubset)
		}
		if !strings.Contains(err.Error(), CodeKernelSubset) {
			t.Fatalf("%s: want %s, got %v", name, CodeKernelSubset, err)
		}
	}
}

// A matmul kernel over tensor records (docs/spec/56-kernels.md section 8):
// one output element per position, read through tensor_at, stored flat
// under a guard that the output is contiguous, so the store is the element
// shape the independence rule admits (Oak.Stdlib.Tensor.flat_index).
const kernelMatmulProgram = `package main

t := import("tensor")

kernel matmul_t[A, B, C]: (gid: u32, a: t.Tensor2[A], b: t.Tensor2[B], out: t.MutTensor2[C]): () = {
  contiguous: Bool = out.row_stride == out.cols && out.col_stride == 1 && out.offset == 0
  contiguous && gid < out.rows * out.cols && gid < len(out.data) && a.cols == b.rows && out.rows == a.rows && out.cols == b.cols ? {
    i: u32 = gid / out.cols
    j: u32 = gid % out.cols
    acc: f32 = 0.0
    k: u32 = 0
    n: u32 = a.cols
    while k < n {
      acc = acc + t.tensor_at(a, i, k) * t.tensor_at(b, k, j)
      k = k + 1
    }
    out.data[gid] = acc
  }
}

main: (): i32 = {
  xs: [6]f32 = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
  ys: [4]f32 = [0.0, 0.0, 0.0, 0.0]
  a: t.Tensor2 = t.tensor_of(view(&xs), 2, 3)
  bt: t.Tensor2 = t.tensor_transpose(a)
  {
    o: t.MutTensor2 = t.tensor_mut_of(span(&ys), 2, 2)
    g: u32 = 0
    while g < 4 {
      matmul_t(g, a, bt, o)
      g = g + 1
    }
  }
  ys[0] == 14.0 && ys[1] == 32.0 && ys[2] == 32.0 && ys[3] == 77.0 ? 42 | 1
}
`

func TestE2EKernelsTensorMatmul(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": kernelMatmulProgram})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	result, err := New().WithPackageDir(root).EmitMetal().Get()
	if err != nil {
		t.Fatal(err)
	}
	if result.Kernels[0].Independence != "element" {
		t.Fatalf("independence = %q", result.Kernels[0].Independence)
	}
	for _, want := range []string{
		"out.data span f32 buffer 14,15;",
		"acc = (acc + (tensor__tensor_uat(a, i, k, oak_fault) * tensor__tensor_uat(b, k, j, oak_fault)));",
		"out.data[gid] = acc;",
	} {
		if !strings.Contains(result.Source, want) {
			t.Fatalf("missing %q in:\n%s", want, result.Source)
		}
	}
}
