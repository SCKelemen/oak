package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A large owned array filled in one loop and read in another is a span
// memory on both sides of the verifier (docs/spec/94-assembler.md §9):
// carried leaf by leaf, its 256 elements exhausted the coupling; as a
// memory, the first loop's stores and the second loop's reads through it
// couple as a span parameter's do.
const nativeLargeArrayProgram = `
fill_sum: (n: u32): u32 {
  buf: [256]u8
  i: u32 = u32(0)
  while i < n {
    buf[i] = u8_trunc_u32(i)
    i = i + u32(1)
  }
  s: u32 = u32(0)
  j: u32 = u32(0)
  while j < n {
    s = s + u32(buf[j])
    j = j + u32(1)
  }
  s
}

main: (): i32 {
  fill_sum(u32(4)) == u32(6) ? 42 | 1
}
`

func TestE2ENativeLargeArrayLoopsProven(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("large_array.oak", nativeLargeArrayProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_large_array", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("large array: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if !strings.Contains(joined, "asm unit fill_sum: proven equal to its Oak body") {
		t.Errorf("fill_sum's 256-byte array must be a memory on both sides and prove; diagnostics:\n%s", joined)
	}
}
