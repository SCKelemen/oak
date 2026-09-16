package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A writable top-level array is a span memory on both sides of the
// verifier (docs/spec/94-assembler.md §9): the machine binds its address
// to the span base, its elements are the span's elements under the
// checker's bounds, and its stores are compared as a span parameter's —
// through a callee's summary as well. The prover's write family stopped
// at "an index into out_buf (not a span parameter)".
const nativeGlobalArrayProgram = `
buf: [64]u8
pos: u32

write_byte: (b: u8): () {
  pos < u32(64) ? {
    buf[pos] = b
    pos = pos + u32(1)
  } | { }
}

write_two: (a: u8, b: u8): () {
  write_byte(a)
  write_byte(b)
}

sum_buf: (n: u32): u32 {
  s: u32 = u32(0)
  i: u32 = u32(0)
  while i < n {
    s = s + u32(buf[i])
    i = i + u32(1)
  }
  s
}

main: (): i32 {
  write_two(u8(3), u8(4))
  (pos == u32(2) && buf[0] == u8(3) && buf[1] == u8(4) && sum_buf(u32(2)) == u32(7)) ? 42 | 1
}
`

func TestE2ENativeGlobalArrayProven(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("global_array.oak", nativeGlobalArrayProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_global_array", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("global array: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, unit := range []string{"write_byte", "write_two", "sum_buf"} {
		if !strings.Contains(joined, "asm unit "+unit+": proven equal to its Oak body") {
			t.Errorf("%s reads or writes the top-level array buf and must be proven; diagnostics:\n%s", unit, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_global_array_c", New().WithSource("global_array.oak", nativeGlobalArrayProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
