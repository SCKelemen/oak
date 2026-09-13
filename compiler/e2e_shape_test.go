package compiler

import (
	"strings"
	"testing"
)

// Shape in the type (docs/spec/56-kernels.md section 8b): Mat[R, N, K]
// carries its dimensions as const parameters, inferred from the record's
// instantiation through its erased region; a vector or matrix of the wrong
// shape is a type error at the call.
const shapeProgram = `package main

s := import("shape")
t := import("tensor")

main: (): i32 = {
  w: [6]f32 = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]      // 2 x 3
  v: [6]f32 = [1.0, 0.0, 0.0, 1.0, 1.0, 1.0]      // 3 x 2
  x: [3]f32 = [1.0, 10.0, 100.0]
  out: [2]f32 = [0.0, 0.0]
  prod: [4]f32 = [0.0, 0.0, 0.0, 0.0]
  m: s.Mat[2, 3] = s.mat_of[2, 3](view(&w))
  n: s.Mat[3, 2] = s.mat_of[3, 2](view(&v))
  true ? {
    o: [*]f32 = span(&out)
    s.mat_matvec(m, x, o)                       // K = 3 from both m and x
  }
  true ? {
    p: [*]f32 = span(&prod)
    s.mat_matmul(m, n, p)                       // 2 x 3 by 3 x 2: K = 3 shared
  }
  rm: t.RowMajor2 = s.mat_row_major(m)
  st: t.Tensor2 = s.mat_tensor(m)
  s.mat_rows(m) == u32(2) && s.mat_cols(m) == u32(3) && s.mat_at(m, 1, 2) == 6.0 &&
    out[0] == 321.0 && out[1] == 654.0 &&
    prod[0] == 4.0 && prod[1] == 5.0 && prod[2] == 10.0 && prod[3] == 11.0 &&
    t.row_major_at(rm, 1, 0) == 4.0 && t.tensor_at(st, 0, 2) == 3.0 ? 42 | 1
}
`

func TestE2EShapeInTheType(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": shapeProgram})
	if code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root)); abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	if got := interpretModule(t, root); got != 42 {
		t.Fatalf("interpreted: %d", got)
	}
	// The wrong shapes are type errors, not traps.
	for name, c := range map[string][2]string{
		"vector length":   {"  x: [3]f32 = [1.0, 10.0, 100.0]", "  x: [4]f32 = [1.0, 10.0, 100.0, 1000.0]"},
		"inner dimension": {"  n: s.Mat[3, 2] = s.mat_of[3, 2](view(&v))", "  n: s.Mat[2, 3] = s.mat_of[2, 3](view(&v))"},
	} {
		bad := strings.Replace(shapeProgram, c[0], c[1], 1)
		root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": bad})
		if _, err := New().WithPackageDir(root).SemanticModel().Get(); err == nil || !strings.Contains(err.Error(), "bound to") {
			t.Fatalf("%s: a shape mismatch must be a type error naming the two lengths: %v", name, err)
		}
	}
	// A shape past the view traps at construction.
	big := strings.Replace(shapeProgram, "s.mat_of[2, 3](view(&w))", "s.mat_of[3, 3](view(&w))", 1)
	big = strings.Replace(big, "m: s.Mat[2, 3]", "m: s.Mat[3, 3]", 1)
	big = strings.Replace(big, "s.mat_matvec(m, x, o)", "", 1)
	big = strings.Replace(big, "s.mat_matmul(m, n, p)", "", 1)
	big = strings.Replace(big, "rm: t.RowMajor2 = s.mat_row_major(m)\n", "", 1)
	big = strings.Replace(big, "st: t.Tensor2 = s.mat_tensor(m)\n", "", 1)
	big = strings.Replace(big, "t := import(\"tensor\")\n", "", 1)
	big = strings.Replace(big, "s.mat_rows(m) == u32(2) && s.mat_cols(m) == u32(3) && s.mat_at(m, 1, 2) == 6.0 &&\n    out[0] == 321.0 && out[1] == 654.0 &&\n    prod[0] == 4.0 && prod[1] == 5.0 && prod[2] == 10.0 && prod[3] == 11.0 &&\n    t.row_major_at(rm, 1, 0) == 4.0 && t.tensor_at(st, 0, 2) == 3.0 ? 42 | 1", "s.mat_rows(m) == u32(3) ? 42 | 1", 1)
	root = writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": big})
	if code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root)); !abnormal {
		t.Fatalf("an oversized shape must trap, got exit %d", code)
	}
}

// The two checker fixes the shaped matrix needed: const parameters are
// recovered through a region record's erased positions, and a float
// literal in a generic body no longer fails instantiation.
func TestE2EConstParamsThroughRegionRecordsAndFloatLiterals(t *testing.T) {
	src := `package main

Pair[R, N: u32]: type = struct { data: View[f32, R] }

pair_of[R, N: u32]: (data: View[f32, R]): Pair[R, N] = {
  assert(N <= len(data))
  Pair { data: data }
}

total[R, N: u32]: (p: Pair[R, N]): f32 = {
  acc: f32 = 0.0
  i: u32 = 0
  while i < N {
    acc = acc + p.data[i]
    i = i + u32(1)
  }
  acc
}

main: (): i32 = {
  xs: [4]f32 = [1.0, 2.0, 3.0, 4.0]
  p: Pair[3] = pair_of[3](view(&xs))
  total(p) == 6.0 ? 42 | 1
}
`
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": src})
	if code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root)); abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	if got := interpretModule(t, root); got != 42 {
		t.Fatalf("interpreted: %d", got)
	}
}
