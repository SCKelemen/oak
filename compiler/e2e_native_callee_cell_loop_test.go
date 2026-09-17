package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A call inside a loop body to a function that writes a package cell: the
// loop carries the cell as it carries one the body stores itself
// (docs/spec/94-assembler.md §9). The prover's write family calls
// write_flush, which resets out_len, from its loops; seven bodies stopped
// at "a call writing package global out_len in a loop".
const nativeCalleeCellLoopProgram = `
count: u32
high: u32

bump: (k: u32): () {
  j: u32 = u32(0)
  while j < k {
    count = count + u32(1)
    j = j + u32(1)
  }
  count > high ? { high = count } | { }
}

run: (n: u32): () {
  i: u32 = u32(0)
  while i < n {
    bump(u32(2))
    i = i + u32(1)
  }
}

main: (): i32 {
  run(u32(3))
  (count == u32(6) && high == u32(6)) ? 42 | 1
}
`

func TestE2ENativeCalleeCellInLoopProven(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("callee_cell.oak", nativeCalleeCellLoopProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_callee_cell", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("callee cell in loop: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if !strings.Contains(joined, "asm unit run: proven equal to its Oak body") {
		t.Errorf("run calls bump, which writes count and high, from its loop and must be proven; diagnostics:\n%s", joined)
	}
}
