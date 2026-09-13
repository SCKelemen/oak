package compiler

import (
	"strings"
	"testing"
)

// Layout in the type (docs/spec/56-kernels.md section 8a; the ml pilot's
// F6 / 5.20): RowMajor2 and ColMajor2 carry their strides in the type.
// Transposition retypes the same storage, the general accessors see the
// strided form, and matvec_rows takes only the k-contiguous layout — a
// column-major weight does not type there.
const tensorLayoutProgram = `package main

t := import("tensor")

main: (): i32 = {
  // 2 x 3, row major: [1 2 3; 4 5 6].
  w: [6]f32 = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
  x: [3]f32 = [1.0, 10.0, 100.0]
  out: [2]f32 = [0.0, 0.0]
  m: t.RowMajor2 = t.row_major_of(view(&w), 2, 3)
  mt: t.ColMajor2 = t.row_major_transpose(m)         // 3 x 2, same storage, retyped
  back: t.RowMajor2 = t.col_major_transpose(mt)
  s: t.Tensor2 = t.row_major_tensor(m)
  st: t.Tensor2 = t.col_major_tensor(mt)
  true ? {
    o: [*]f32 = span(&out)
    t.matvec_rows(m, view(&x), o)                     // out = [321, 654]
  }
  t.row_major_at(m, 1, 2) == 6.0 && t.col_major_at(mt, 2, 1) == 6.0 && t.row_major_at(back, 1, 0) == 4.0 &&
    t.tensor_at(s, 1, 2) == 6.0 && t.tensor_at(st, 2, 1) == 6.0 && t.tensor_at(t.tensor_transpose(s), 2, 1) == 6.0 &&
    out[0] == 321.0 && out[1] == 654.0 ? 42 | 1
}
`

func TestE2ETensorLayoutTypes(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": tensorLayoutProgram})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	if got := interpretModule(t, root); got != 42 {
		t.Fatalf("interpreted: %d", got)
	}
	// The wrong layout does not type: a column-major weight is refused at
	// the call, not at run time.
	wrong := strings.Replace(tensorLayoutProgram, "t.matvec_rows(m, view(&x), o)", "t.matvec_rows(mt, view(&x), o)", 1)
	root = writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": wrong})
	if _, err := New().WithPackageDir(root).SemanticModel().Get(); err == nil || !strings.Contains(err.Error(), "RowMajor2") {
		t.Fatalf("a column-major weight must be refused by type: %v", err)
	}
	// A shape past the view traps at construction.
	big := strings.Replace(tensorLayoutProgram, "t.row_major_of(view(&w), 2, 3)", "t.row_major_of(view(&w), 2, 4)", 1)
	root = writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": big})
	if code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root)); !abnormal {
		t.Fatalf("an oversized shape must trap, got exit %d", code)
	}
}

// A kernel takes the layout-typed matrix as a record parameter, and its
// element reads are the type's index arithmetic: the Metal entry flattens
// the record into its buffers and scalars as it does Tensor2.
const kernelLayoutProgram = `package main

t := import("tensor")

kernel matvec[R]: (gid: u32, w: t.RowMajor2[R], x: []f32, out: [*]f32): () = {
  gid < w.rows && gid < len(out) && len(x) == w.cols ? {
    acc: f32 = 0.0
    n: u32 = w.cols
    k: u32 = 0
    while k < n {
      acc = acc + t.row_major_at(w, gid, k) * x[k]
      k = k + 1
    }
    out[gid] = acc
  }
}

main: (): i32 = {
  ws: [6]f32 = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
  xs: [3]f32 = [1.0, 10.0, 100.0]
  outs: [2]f32 = [0.0, 0.0]
  m: t.RowMajor2 = t.row_major_of(view(&ws), 2, 3)
  g: u32 = 0
  while g < 2 {
    matvec(g, m, view(&xs), span(&outs))
    g = g + 1
  }
  outs[0] == 321.0 && outs[1] == 654.0 ? 42 | 1
}
`

func TestE2EKernelsLayoutTypes(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": kernelLayoutProgram})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	result, err := New().WithPackageDir(root).EmitMetal().Get()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(result.Source, "kernel void matvec(") || !strings.Contains(result.Source, "w.data view f32 buffer 0,1; w.rows scalar u32 buffer 2; w.cols scalar u32 buffer 3") {
		t.Fatalf("the layout record flattens into the kernel's buffers and scalars:\n%s", result.Source)
	}
}
