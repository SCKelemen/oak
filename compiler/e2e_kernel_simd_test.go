package compiler

import (
	"strings"
	"testing"
)

// The simdgroup shuffle (docs/spec/56-kernels.md section 2a; the ml
// pilot's F1, increment (c)): simd_shuffle_xor(v, off) is lane `lane ^ off`'s
// value of v; spelled at descending offsets it is the lane-rule butterfly,
// and the host form reads partners through per-lane temps in phases of
// their own, so the interpreter, the C, and the device compute one value.
const kernelSimdProgram = `package main

kernel block_sums: (gid: u32, x: []f32, out: [*]f32): () = {
  i: u32 = gid * 8 + lane(8)
  v: f32 = 0.0
  i < len(x) ? { v = x[i] }
  v = v + simd_shuffle_xor(v, 4)
  v = v + simd_shuffle_xor(v, 2)
  v = v + simd_shuffle_xor(v, 1)
  lane(8) == 0 && gid < len(out) ? { out[gid] = v }
}

main: (): i32 = {
  // 2^24 + 1 rounds to 2^24: the butterfly gives 2^24 + 6 where a
  // sequential sum would give 2^24.
  xs: [16]f32 = [16777216.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]
  ys: [2]f32 = [0.0, 0.0]
  g: u32 = 0
  while g < 2 {
    block_sums(g, view(&xs), span(&ys))
    g = g + 1
  }
  ys[0] == 16777222.0 && ys[1] == 36.0 ? 42 | 1
}
`

func TestE2EKernelSimdShuffle(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": kernelSimdProgram})
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
	for _, want := range []string{
		"v = (v + simd_shuffle_xor(v, 4u));",
		"v = (v + simd_shuffle_xor(v, 1u));",
		"if (oak_lid == 0u) { out[gid] = v; }",
	} {
		if !strings.Contains(result.Source, want) {
			t.Fatalf("missing %q in:\n%s", want, result.Source)
		}
	}
	emitted, err := New().WithPackageDir(root).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"oak_sh1", "oak_sh3", "oak_priv_v"} {
		if !strings.Contains(emitted, want) {
			t.Fatalf("missing %q in the C:\n%s", want, emitted)
		}
	}
	for name, c := range map[string][2]string{
		"shuffle in a loop":     {"kernel k: (gid: u32, out: [*]f32): () = {\n  v: f32 = 1.0\n  n: u32 = 0\n  while n < 2 {\n    v = v + simd_shuffle_xor(v, 1)\n    n = n + 1\n  }\n  lane(4) == 0 && gid < len(out) ? { out[gid] = v }\n}\n", "top level"},
		"shuffle of an element": {"kernel k: (gid: u32, x: []f32, out: [*]f32): () = {\n  v: f32 = simd_shuffle_xor(x[0], 1)\n  lane(4) == 0 && gid < len(out) ? { out[gid] = v }\n}\n", "scalar local declared at the kernel body's top level"},
		"shuffle in a helper":   {"twice: (v: f32): f32 = v + simd_shuffle_xor(v, 1)\nkernel k: (gid: u32, out: [*]f32): () = {\n  v: f32 = 1.0\n  lane(4) == 0 && gid < len(out) ? { out[gid] = twice(v) }\n}\n", "belongs to a kernel body"},
		"offset past the group": {"kernel k: (gid: u32, out: [*]f32): () = {\n  v: f32 = 1.0\n  v = v + simd_shuffle_xor(v, 8)\n  lane(4) == 0 && gid < len(out) ? { out[gid] = v }\n}\n", "below the group size"},
	} {
		src := "package main\n\n" + c[0] + "\nmain: (): i32 = 0\n"
		root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": src})
		_, err := New().WithPackageDir(root).EmitMetal().Get()
		if err == nil || !strings.Contains(err.Error(), c[1]) {
			t.Fatalf("%s: want %q, got %v", name, c[1], err)
		}
	}
}
