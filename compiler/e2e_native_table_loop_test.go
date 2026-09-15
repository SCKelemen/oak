package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A constant table read inside a loop body (the CRC-32C byte loop's
// shape): the verifier reads the table's address (`adrl`) in a summarized
// loop body as it does on a straight path (asm/loops.go), so the fold is
// proven rather than trusted, and the value agrees with the C backend.
const nativeTableLoopProgram = `TABLE: [4]u32 = [4]u32{10, 20, 30, 40}

fold: (v: []u8): u32 {
  acc: u32 = 0
  i: u32 = 0
  while i < len(v) {
    acc = acc + TABLE[u32(v[i] & u8(3))]
    i = i + u32(1)
  }
  acc
}

main: (): i32 {
  bytes: [5]u8 = [5]u8{0, 1, 2, 3, 7}
  // 10 + 20 + 30 + 40 + 40 = 140.
  i32_bits_u32(fold(view(&bytes)))
}
`

func TestE2ENativeTableInLoop(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("tloop.oak", nativeTableLoopProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	if _, err := comp.Check().Get(); err != nil {
		t.Fatal(err)
	}
	joined := strings.Join(infos, "\n")
	if !strings.Contains(joined, "asm unit fold: proven equal to its Oak body") {
		t.Errorf("the table fold must be proven with its address read in the loop body; diagnostics:\n%s", joined)
	}
	_, code, abnormal := buildAndRunFrom(t, "native_table_loop", comp)
	if abnormal || code != 140 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 140\n%s", code, abnormal, joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_table_loop_c", New().WithSource("tloop.oak", nativeTableLoopProgram)); abnormal || code != 140 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 140", code, abnormal)
	}
}
