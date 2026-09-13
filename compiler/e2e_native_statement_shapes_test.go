package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

// Statement shapes the native lanes left to C in the standard library
// (docs/spec/94-assembler.md §9): a conditional with no false arm and a
// chained conditional in statement position, and an i32 element index on
// the RV64 lane (kept in its canonical sign-extended form; a negative index
// is a huge unsigned value the guard traps, as the C backend's cast does).
// Every function lowers natively on both lanes and the program agrees
// with the C build.
const nativeStatementShapesProgram = `mark_bits: (marks: [*]u32, lanes: u32) -> u32 {
  count: u32 = u32(0)
  bits: u32 = lanes
  while bits != u32(0) && count < len(marks) {
    marks[count] = bits
    count = count + u32(1)
    (bits & u32(1)) == u32(1) ? { count = count + u32(0) }
    bits = bits >> u32(1)
  }
  count
}

classify: (v: u32) -> u32 {
  out: u32 = u32(0)
  v == u32(0) ? { out = u32(1) } | v < u32(10) ? { out = u32(2) } | { out = u32(3) }
  out
}

at_signed: (v: []u8, i: i32) -> u8 = v[i]

main: (): i32 {
  words: [8]u32
  data: [4]u8
  data[1] = u8(7)
  n: u32 = mark_bits(span(&words), u32(11))
  i32_bits_u32(n + classify(u32(0)) + classify(u32(5)) + classify(u32(50)) + u32(at_signed(view(&data), i32(1))) - u32(17))
}
`

func TestE2ENativeStatementShapes(t *testing.T) {
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
		comp := New().WithSource("shapes.oak", nativeStatementShapesProgram).WithTarget(tgt).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(sink)
		if _, err := comp.EmitC().Get(); err != nil {
			t.Fatalf("%s: native build: %v", tname, err)
		}
		for _, fn := range []string{"mark_bits", "classify", "at_signed"} {
			for _, m := range native {
				if strings.Contains(m, "native backend: "+fn+" left to the C backend") {
					t.Errorf("%s: %s", tname, m)
				}
			}
			found := false
			for _, m := range native {
				if strings.Contains(m, "asm unit "+fn+":") || strings.Contains(m, "asm unit "+fn+" ") {
					found = true
				}
			}
			if !found {
				t.Errorf("%s: %s: no native verdict:\n%s", tname, fn, strings.Join(native, "\n"))
			}
		}
	}
	if _, exit, abnormal := buildAndRunFrom(t, "native_statement_shapes", New().WithSource("shapes.oak", nativeStatementShapesProgram)); abnormal || exit != 0 {
		t.Fatalf("program: exit = (%d, abnormal=%v), want 0", exit, abnormal)
	}
}
