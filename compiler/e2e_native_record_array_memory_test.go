package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A record argument's sixty-four-element array field read at a symbolic
// index is a memory read on both sides (asm/verify.go, elementUnderIndexTerm
// and recordArrayMemory): the prover's Bits family reads `a.at[i]` so, and
// its loop obligations over two such reads exceeded every diagram as
// folds over the leaves.
const nativeRecordArrayMemoryProgram = `Bits: type = struct { at: [64]u32 }

pick: (a: Bits, i: u32): u32 { a.at[i] }

pair: (a: Bits, i: u32): u32 { a.at[i] + a.at[i + u32(1)] }

count_set: (a: Bits, w: u32): u32 {
  n: u32 = 0
  i: u32 = 0
  while i < w {
    n = n + (a.at[i] & u32(1))
    i = i + u32(1)
  }
  n
}

main: (): i32 {
  b: Bits
  k: u32 = 0
  while k < u32(64) {
    b.at[k] = k
    k = k + u32(1)
  }
  i32_bits_u32(pick(b, u32(5)) + pair(b, u32(10)) + count_set(b, u32(64)) - u32(16))
}
`

func TestE2ENativeRecordArrayMemory(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("bits.oak", nativeRecordArrayMemoryProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "record_array_memory", comp)
	joined := strings.Join(infos, "\n")
	// 5 + (10 + 11) + 32 - 16 = 42
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, want := range []string{
		"asm unit pick: proven equal to its Oak body (linear normal form 1*a.at[i]",
		"asm unit pair: proven equal to its Oak body (linear normal form 1*a.at[i + 1] + 1*a.at[i]",
		"asm unit count_set: proven equal to its Oak body",
	} {
		if !strings.Contains(joined, want) {
			t.Errorf("want %q in the diagnostics:\n%s", want, joined)
		}
	}
}
