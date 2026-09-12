package compiler

import (
	"context"
	"encoding/binary"
	"math"
	"testing"
	"time"

	"github.com/SCKelemen/oak/codegen/metal"
	"github.com/SCKelemen/oak/codegen/metal/gpu"
)

// Kernels on the device (docs/spec/56-kernels.md section 9): the emitted
// Metal runs on this machine's GPU through the framework's run-time
// compiler and computes what the C realization computed in the host
// tests — elementwise, tiled, a per-thread reduce over a window, a
// threadgroup reduce, and a record-parameter matmul — and a trapping
// access raises the fault word instead of reading out of bounds.

func f32s(values ...float32) gpu.Arg {
	out := make([]byte, 4*len(values))
	for i, v := range values {
		binary.LittleEndian.PutUint32(out[4*i:], math.Float32bits(v))
	}
	return out
}

func u32arg(v uint32) gpu.Arg {
	out := make([]byte, 4)
	binary.LittleEndian.PutUint32(out, v)
	return out
}

func readF32s(t *testing.T, data []byte) []float32 {
	t.Helper()
	if len(data)%4 != 0 {
		t.Fatalf("%d bytes is not f32 data", len(data))
	}
	out := make([]float32, len(data)/4)
	for i := range out {
		out[i] = math.Float32frombits(binary.LittleEndian.Uint32(data[4*i:]))
	}
	return out
}

func expectF32s(t *testing.T, what string, got []float32, want ...float32) {
	t.Helper()
	if len(got) != len(want) {
		t.Fatalf("%s: got %v, want %v", what, got, want)
	}
	for i := range want {
		if got[i] != want[i] {
			t.Fatalf("%s: got %v, want %v", what, got, want)
		}
	}
}

func emitKernels(t *testing.T, program string) *metal.Result {
	t.Helper()
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": program})
	result, err := New().WithPackageDir(root).EmitMetal().Get()
	if err != nil {
		t.Fatal(err)
	}
	return result
}

func kernelNamed(t *testing.T, result *metal.Result, name string) metal.Kernel {
	t.Helper()
	for _, k := range result.Kernels {
		if k.Name == name {
			return k
		}
	}
	t.Fatalf("no kernel %s in %+v", name, result.Kernels)
	return metal.Kernel{}
}

func TestE2EKernelsOnDevice(t *testing.T) {
	if reason := gpu.Available(); reason != "" {
		t.Skip(reason)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 3*time.Minute)
	defer cancel()

	// Elementwise and tiled, from the first kernel program.
	first := emitKernels(t, "package main\n"+kernelProgram)
	res, err := gpu.Run(ctx, first.Source, kernelNamed(t, first, "relu"), 4, map[string]gpu.Arg{
		"x": f32s(-1, 2, -3, 4), "y": f32s(0, 0, 0, 0),
	})
	if err != nil {
		t.Fatal(err)
	}
	expectF32s(t, "relu", readF32s(t, res.Spans["y"]), 0, 2, 0, 4)
	if res.Fault != 0 {
		t.Fatalf("relu fault %d", res.Fault)
	}
	res, err = gpu.Run(ctx, first.Source, kernelNamed(t, first, "axpy"), 2, map[string]gpu.Arg{
		"a": f32s(2), "x": f32s(1, 2, 3, 4), "y": f32s(1, 1, 1, 1), "tile": u32arg(2),
	})
	if err != nil {
		t.Fatal(err)
	}
	expectF32s(t, "axpy", readF32s(t, res.Spans["y"]), 3, 5, 7, 9)

	// A per-thread reduce over a window: the binary-counter tree the host computes.
	reduce := emitKernels(t, kernelReduceProgram)
	res, err = gpu.Run(ctx, reduce.Source, kernelNamed(t, reduce, "tile_sum"), 2, map[string]gpu.Arg{
		"x": f32s(1, 2, 3, 4, 5, 6, 7, 8), "partials": f32s(0, 0), "tile": u32arg(4),
	})
	if err != nil {
		t.Fatal(err)
	}
	expectF32s(t, "tile_sum", readF32s(t, res.Spans["partials"]), 10, 26)

	// A threadgroup reduce: one threadgroup per position, the descriptor's
	// threadgroup size, the same grouping (Oak.Reduce.coop_eq_tree).
	group := emitKernels(t, kernelGroupProgram)
	groupSums := kernelNamed(t, group, "group_sums")
	if groupSums.Threadgroup != 4 {
		t.Fatalf("group_sums threadgroup = %d", groupSums.Threadgroup)
	}
	res, err = gpu.Run(ctx, group.Source, groupSums, 3, map[string]gpu.Arg{
		"x": f32s(1, 2, 3, 4, 5, 6, 7, 8, 9, 10), "partials": f32s(0, 0, 0),
	})
	if err != nil {
		t.Fatal(err)
	}
	expectF32s(t, "group_sums", readF32s(t, res.Spans["partials"]), 10, 26, 19)

	// Record parameters flattened into buffers: a 2x3 by its transpose.
	matmul := emitKernels(t, kernelMatmulProgram)
	res, err = gpu.Run(ctx, matmul.Source, kernelNamed(t, matmul, "matmul_t"), 4, map[string]gpu.Arg{
		"a.data": f32s(1, 2, 3, 4, 5, 6), "a.rows": u32arg(2), "a.cols": u32arg(3), "a.row_stride": u32arg(3), "a.col_stride": u32arg(1), "a.offset": u32arg(0),
		"b.data": f32s(1, 2, 3, 4, 5, 6), "b.rows": u32arg(3), "b.cols": u32arg(2), "b.row_stride": u32arg(1), "b.col_stride": u32arg(3), "b.offset": u32arg(0),
		"out.data": f32s(0, 0, 0, 0), "out.rows": u32arg(2), "out.cols": u32arg(2), "out.row_stride": u32arg(2), "out.col_stride": u32arg(1), "out.offset": u32arg(0),
	})
	if err != nil {
		t.Fatal(err)
	}
	expectF32s(t, "matmul_t", readF32s(t, res.Spans["out.data"]), 14, 32, 32, 77)

	// A trapping access: relu reads x[gid] under gid < len(y) alone, so an
	// empty x raises the index fault (code 1). The fault word is the
	// host's verdict; the spans' contents after a fault are not a result.
	res, err = gpu.Run(ctx, first.Source, kernelNamed(t, first, "relu"), 4, map[string]gpu.Arg{
		"x": f32s(), "y": f32s(7, 7, 7, 7),
	})
	if err != nil {
		t.Fatal(err)
	}
	if res.Fault != 1 {
		t.Fatalf("an out-of-range read must raise fault 1, got %d", res.Fault)
	}
}
