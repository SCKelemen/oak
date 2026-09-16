package compiler

import (
	"context"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/codegen/metal/gpu"
)

// F30: plus is a name in Metal's standard library. Keyword suffixing also
// collapsed the distinct Oak helper names thread and thread_. Each helper
// and each function-parameter specialization needs its own private symbol.
const kernelHelperNamesProgram = `
plus: (a: f32, b: f32): f32 = a + b
minus: (a: f32, b: f32): f32 = a - b
thread: (v: f32): f32 = v * 2.0
thread_: (v: f32): f32 = v + 1.0
apply: (x: f32, y: f32, f: (f32, f32) -> f32 effects { }): f32 = f(x, y)

kernel helper_names: (gid: u32, x: []f32, out: [*]f32): () = {
  gid < len(x) && gid < len(out) ? {
    a: f32 = apply(x[gid], 2.0, plus)
    b: f32 = apply(x[gid], 2.0, minus)
    out[gid] = thread(a) + thread_(b)
  }
}
main: (): i32 = {
  x: [2]f32 = [4.0, 7.0]
  out: [2]f32
  helper_names(0, view(&x), span(&out))
  helper_names(1, view(&x), span(&out))
  out[0] == 15.0 && out[1] == 24.0 ? 42 | 1
}
`

func TestE2EKernelHelperNames(t *testing.T) {
	if code, abnormal := buildAndRun(t, "helper_names", kernelHelperNamesProgram); abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	if got := interpretChecked(t, kernelHelperNamesProgram); got != 42 {
		t.Fatalf("interpreted: %d", got)
	}
	result, err := New().WithSource("helper_names.oak", kernelHelperNamesProgram).EmitMetal().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, name := range []string{"plus", "minus", "thread", "thread_u", "apply__f__plus", "apply__f__minus"} {
		if strings.Count(result.Source, "static inline float oak_helper__"+name+"(") != 1 {
			t.Errorf("helper %s must have one private definition", name)
		}
	}
	if got := strings.Join(kernelNamed(t, result, "helper_names").Reach, " "); got != "apply minus plus thread thread_ helper_names" {
		t.Fatalf("reach must keep the Oak names, got %q", got)
	}
}

func TestKernelHelperNamesOnDevice(t *testing.T) {
	if reason := gpu.Available(); reason != "" {
		t.Skip(reason)
	}
	ctx, cancel := context.WithTimeout(context.Background(), time.Minute)
	defer cancel()
	result := emitKernels(t, "package main\n"+kernelHelperNamesProgram)
	out, err := gpu.Run(ctx, result.Source, kernelNamed(t, result, "helper_names"), 2, map[string]gpu.Arg{
		"x": f32s(4, 7), "out": f32s(0, 0),
	})
	if err != nil {
		t.Fatal(err)
	}
	if out.Fault != 0 {
		t.Fatalf("fault %d", out.Fault)
	}
	expectF32s(t, "helper names", readF32s(t, out.Spans["out"]), 15, 24)
}
