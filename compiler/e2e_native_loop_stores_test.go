package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

// Stores through spans inside data-dependent loops (docs/spec/94-assembler.md
// §9, "Span memories through loops"): the loop summary places a memory
// marker for each span the body stores through, the coupling proof
// compares the iterations' stores pairwise, and the memories after the
// loop are compared under the coupling. A unit fill, a copy, a fill with
// a result, and a conditional store are proven on both lanes.
const nativeLoopStoresProgram = `fill: (v: [*]u32, n: u32, x: u32) -> () {
  i: u32 = u32(0)
  while i < n {
    v[i] = x
    i = i + u32(1)
  }
}

copy_into: (dst: [*]u8, src: []u8, n: u32) -> u32 {
  i: u32 = u32(0)
  while i < n {
    dst[i] = src[i]
    i = i + u32(1)
  }
  i
}

zero_odd: (v: [*]u32, n: u32) -> () {
  i: u32 = u32(0)
  while i < n {
    (v[i] & u32(1)) == u32(1) ? { v[i] = u32(0) }
    i = i + u32(1)
  }
}

main: (): i32 {
  buf: [4]u32
  bytes: [4]u8 = [4]u8{7, 8, 9, 10}
  out: [4]u8
  fill(span(&buf), u32(3), u32(5))
  n: u32 = copy_into(span(&out), view(&bytes), u32(4))
  zero_odd(span(&buf), u32(4))
  i32_bits_u32(buf[0] + buf[2] + buf[3] + u32(out[3]) + n - u32(14))
}
`

func TestE2ENativeLoopStores(t *testing.T) {
	for _, tname := range []string{"freestanding/arm64", "linux/riscv64"} {
		tgt, err := target.Parse(tname)
		if err != nil {
			t.Fatal(err)
		}
		var native []string
		sink := func(d *diagnostic.Diagnostic) {
			if strings.HasPrefix(d.Message, "native backend: ") {
				native = append(native, d.Message)
			}
		}
		comp := New().WithSource("loop_stores.oak", nativeLoopStoresProgram).WithTarget(tgt).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(sink)
		if _, err := comp.EmitC().Get(); err != nil {
			t.Fatalf("%s: native build: %v", tname, err)
		}
		joined := strings.Join(native, "\n")
		for _, fn := range []string{"fill", "copy_into", "zero_odd"} {
			verdict := ""
			for _, m := range native {
				if strings.Contains(m, "asm unit "+fn+":") {
					verdict = m
				}
			}
			if verdict == "" {
				t.Errorf("%s: %s: no native verdict:\n%s", tname, fn, joined)
				continue
			}
			if !strings.Contains(verdict, "proven equal") || !strings.Contains(verdict, "span memory it writes") {
				t.Errorf("%s: %s must be proven in its span memory through the loop: %s", tname, fn, verdict)
			}
		}
	}
	if _, exit, abnormal := buildAndRunFrom(t, "native_loop_stores", New().WithSource("loop_stores.oak", nativeLoopStoresProgram)); abnormal || exit != 0 {
		t.Fatalf("program: exit = (%d, abnormal=%v), want 0", exit, abnormal)
	}
}
