package compiler

import (
	"strings"
	"testing"
)

// Fusion (docs/spec/56-kernels.md section 2b; the ml pilot's F1, increment
// (d)): a kernel calls another kernel at its own position, the callee is
// inlined as a helper, and its span accesses are judged as the caller's.
// The two stages become one launch; the host runs the same two calls.
const kernelFusionProgram = `package main

kernel scale: (gid: u32, x: []f32, y: [*]f32): () = {
  gid < len(x) && gid < len(y) ? { y[gid] = x[gid] * 2.0 }
}

kernel shift: (gid: u32, y: [*]f32, out: [*]f32): () = {
  gid < len(y) && gid < len(out) ? { out[gid] = y[gid] + 1.0 }
}

kernel scale_shift: (gid: u32, x: []f32, y: [*]f32, out: [*]f32): () = {
  scale(gid, x, y)
  shift(gid, y, out)
}

main: (): i32 = {
  xs: [4]f32 = [1.0, 2.0, 3.0, 4.0]
  ys: [4]f32 = [0.0, 0.0, 0.0, 0.0]
  outs: [4]f32 = [0.0, 0.0, 0.0, 0.0]
  g: u32 = 0
  while g < 4 {
    scale_shift(g, view(&xs), span(&ys), span(&outs))
    g = g + 1
  }
  outs[0] == 3.0 && outs[3] == 9.0 && ys[2] == 6.0 ? 42 | 1
}
`

func TestE2EKernelFusion(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": kernelFusionProgram})
	if code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root)); abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	if got := interpretModule(t, root); got != 42 {
		t.Fatalf("interpreted: %d", got)
	}
	result, err := New().WithPackageDir(root).EmitMetal().Get()
	if err != nil {
		t.Fatal(err)
	}
	src := result.Source
	for _, want := range []string{
		"static inline void oak_helper__scale(uint gid, device const float* x, uint x_len, device float* y, uint y_len, device atomic_uint* oak_fault)",
		"static inline void oak_helper__shift(uint gid, device float* y, uint y_len, device float* out, uint out_len, device atomic_uint* oak_fault)",
		"kernel void scale_shift(",
		"oak_helper__scale(gid, x, x_len, y, y_len, oak_fault);",
		"oak_helper__shift(gid, y, y_len, out, out_len, oak_fault);",
	} {
		if !strings.Contains(src, want) {
			t.Fatalf("missing %q in:\n%s", want, src)
		}
	}
	// Each stage is still a kernel of its own, and the fused one is an
	// element kernel.
	if k := kernelNamed(t, result, "scale_shift"); k.Independence != "element" {
		t.Fatalf("descriptor = %+v", k)
	}
	kernelNamed(t, result, "scale")
	// Isolating ordinary helpers from lane state must preserve a kernel
	// helper's ability to fuse another kernel at the same position.
	nested := strings.Replace(kernelFusionProgram, "main: (): i32", `kernel wrapped: (gid: u32, x: []f32, y: [*]f32, out: [*]f32): () = {
  scale_shift(gid, x, y, out)
}

main: (): i32`, 1)
	if _, err := New().WithSource("nested_fusion.oak", nested).EmitMetal().Get(); err != nil {
		t.Fatalf("nested fusion: %v", err)
	}
	for name, c := range map[string][2]string{
		"another position": {"kernel a: (gid: u32, y: [*]f32): () = {\n  gid < len(y) ? { y[gid] = 1.0 }\n}\nkernel b: (gid: u32, y: [*]f32): () = {\n  a(gid + 1, y)\n}\n", "pass gid as its first argument"},
		"mixed shapes":     {"kernel a: (gid: u32, y: [*]f32): () = {\n  gid < len(y) ? { y[gid] = 1.0 }\n}\nkernel b: (gid: u32, y: [*]f32, z: [*]f32): () = {\n  k: u32 = 0\n  while k < 4 {\n    i: u32 = gid * 4 + k\n    i < len(z) ? { z[i] = 2.0 }\n    k = k + 1\n  }\n  a(gid, y)\n}\nkernel c: (gid: u32, y: [*]f32, z: [*]f32): () = {\n  k: u32 = 0\n  while k < 8 {\n    i: u32 = gid * 8 + k\n    i < len(z) ? { z[i] = 2.0 }\n    k = k + 1\n  }\n  b(gid, y, z)\n}\n", "one shape"},
		"group callee":     {"kernel a: (gid: u32, y: [*]f32): () = {\n  i: u32 = gid * 4 + lane(4)\n  i < len(y) ? { y[i] = 1.0 }\n}\nkernel b: (gid: u32, y: [*]f32): () = {\n  a(gid, y)\n}\n", "group kernel"},
		"self fusion":      {"kernel a: (gid: u32, y: [*]f32): () = {\n  a(gid, y)\n}\n", "into itself"},
	} {
		src := "package main\n\n" + c[0] + "\nmain: (): i32 = 0\n"
		root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": src})
		_, err := New().WithPackageDir(root).EmitMetal().Get()
		if err == nil || !strings.Contains(err.Error(), c[1]) {
			t.Fatalf("%s: want %q, got %v", name, c[1], err)
		}
	}
}
