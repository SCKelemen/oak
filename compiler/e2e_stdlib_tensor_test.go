package compiler

import (
	"testing"
)

// The tensor package (stdlib/tensor.oak, docs/spec/56-kernels.md section 8):
// rank-2 tensors as records over views and spans — shape, strides, offset —
// with transposition and rows as new records over the same storage, and
// matmul, relu, add, scale, and sum writing into caller-owned spans.
const tensorProgram = `package main

t := import("tensor")

main: (): i32 = {
  xs: [6]f32 = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
  ys: [4]f32 = [0.0, 0.0, 0.0, 0.0]
  zs: [6]f32 = [0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
  ok: Bool = true
  a: t.Tensor2 = t.tensor_of(view(&xs), 2, 3)
  // a = [[1, 2, 3], [4, 5, 6]]; a^T = [[1, 4], [2, 5], [3, 6]]
  at: t.Tensor2 = t.tensor_transpose(a)
  ok = ok && t.tensor_at(at, 0, 1) == 4.0 && t.tensor_at(at, 2, 0) == 3.0 && at.rows == 3 && at.cols == 2
  ok = ok && t.tensor_sum(a) == 21.0 && t.tensor_sum(at) == 21.0
  r1: t.Tensor2 = t.tensor_row(a, 1)
  ok = ok && r1.rows == 1 && r1.cols == 3 && t.tensor_at(r1, 0, 0) == 4.0 && t.tensor_sum(r1) == 15.0
  {
    // a * a^T = [[14, 32], [32, 77]]
    o: t.MutTensor2 = t.tensor_mut_of(span(&ys), 2, 2)
    t.tensor_matmul(a, at, o)
    ok = ok && t.tensor_get(o, 1, 1) == 77.0
  }
  ok = ok && ys[0] == 14.0 && ys[1] == 32.0 && ys[2] == 32.0 && ys[3] == 77.0
  {
    // relu(scale(a, -1) + a) over the same shape; add then relu clamp to 0.
    o: t.MutTensor2 = t.tensor_mut_of(span(&zs), 2, 3)
    t.tensor_scale(a, -2.0, o)
    ok = ok && t.tensor_get(o, 1, 2) == -12.0
  }
  neg: t.Tensor2 = t.tensor_of(view(&zs), 2, 3)
  ok = ok && t.tensor_sum(neg) == -42.0
  ws: [6]f32 = [0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
  {
    o: t.MutTensor2 = t.tensor_mut_of(span(&ws), 2, 3)
    t.tensor_add(a, neg, o)
    // a + (-2a) = -a; relu of it is all zeros
    ok = ok && t.tensor_get(o, 0, 0) == -1.0
    t.tensor_relu(neg, o)
    ok = ok && t.tensor_get(o, 1, 2) == 0.0
    t.tensor_fill(o, 7.0)
  }
  filled: t.Tensor2 = t.tensor_of(view(&ws), 2, 3)
  ok = ok && t.tensor_sum(filled) == 42.0
  ok ? 42 | 1
}
`

func TestE2EStdlibTensor(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": tensorProgram})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// Shape errors trap: a matmul over disagreeing shapes, an element outside
// the shape, and a shape that does not fit its view.
func TestStdlibTensorShapeTraps(t *testing.T) {
	for name, body := range map[string]string{
		"matmul shapes": `
  xs: [6]f32 = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
  ys: [4]f32 = [0.0, 0.0, 0.0, 0.0]
  a: t.Tensor2 = t.tensor_of(view(&xs), 2, 3)
  o: t.MutTensor2 = t.tensor_mut_of(span(&ys), 2, 2)
  t.tensor_matmul(a, a, o)
  0`,
		"element outside the shape": `
  xs: [6]f32 = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
  a: t.Tensor2 = t.tensor_of(view(&xs), 2, 3)
  i32(t.tensor_at(a, 2, 0) == 0.0 ? 0 | 1)`,
		"shape larger than the view": `
  xs: [6]f32 = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
  a: t.Tensor2 = t.tensor_of(view(&xs), 3, 3)
  i32_bits_u32(a.rows)`,
	} {
		src := "package main\n\nt := import(\"tensor\")\n\nmain: (): i32 = {" + body + "\n}\n"
		root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": src})
		_, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
		if !abnormal {
			t.Fatalf("%s: must trap", name)
		}
	}
}
