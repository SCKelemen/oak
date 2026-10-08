package compiler

import "testing"

func TestE2EKernelClauseWithLayout(t *testing.T) {
	source := `
fill: (gid: u32, out: [*]u32): ()
  (kernel)
  effects { }
  gid < len(out) ? { out[gid] = gid + 42 }
main: (): i32
  values: [1]u32 = [0]
  fill(0, span(&values))
  i32_bits_u32(values[0])
`
	metal, err := New().WithSource("layout-kernel.oak", source).EmitMetal().Get()
	if err != nil {
		t.Fatal(err)
	}
	if len(metal.Kernels) != 1 || metal.Kernels[0].Name != "fill" {
		t.Fatalf("kernel metadata: %+v", metal.Kernels)
	}
	code, abnormal := buildAndRun(t, "layout_kernel", source)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
