package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A record field handed to a callee by address (docs/spec/94-assembler.md
// §9 "Call summaries"): the machine passes `&state` plus the field's offset
// where the callee takes `[8]u32`, and the call summary binds the callee's
// leaves to the caller's leaves at those offsets — `state.cv[k]` — rather
// than to fresh symbols `state[k]` for the same words. The unit is proven;
// with the fresh symbols the verifier refuted it on a state where both
// backends agree (hash.blake3_chunk_cv, #507).
const nativeFieldAddressArgumentProgram = `
State: type = struct {
  cv: [8]u32
  block: [64]u8
  block_len: u32
  counter: u64
}

low_words: (cv: [8]u32, block: [16]u32, counter: u64): [16]u32 {
  v: [16]u32 = [16]u32{ cv[0], cv[1], cv[2], cv[3], cv[4], cv[5], cv[6], cv[7], block[0], block[1], block[2], block[3], u32_trunc_u64(counter), u32_trunc_u64(counter >> u64(32)), 0, 0 }
  v
}

words: (block: [64]u8): [16]u32 {
  m: [16]u32
  i: u32 = 0
  while i < u32(16) {
    m[i] = u32(block[i * u32(4)]) | (u32(block[i * u32(4) + u32(1)]) << u32(8))
    i = i + u32(1)
  }
  m
}

first_two: (state: State): u64 {
  out: [16]u32 = low_words(state.cv, words(state.block), state.counter)
  u64(out[0]) | (u64(out[1]) << u64(32))
}

main: (): i32 {
  s: State
  i: u32 = 0
  while i < u32(64) { s.block[i] = u8_trunc_u32(i + u32(6)); i = i + u32(1) }
  s.cv = [8]u32{ 0, 0, 0, 1, 2, 3, 4, 5 }
  s.counter = u64(15)
  i32_bits_u32(u32_trunc_u64(first_two(s)) & u32(63))
}
`

func TestNativeShapesFieldAddressArgument(t *testing.T) {
	var infos []string
	comp := nativeShapeCompilation("field_arg.oak", nativeFieldAddressArgumentProgram).WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	if _, err := comp.Check().Get(); err != nil {
		t.Fatalf("check: %v\n%s", err, strings.Join(infos, "\n"))
	}
	joined := strings.Join(infos, "\n")
	if strings.Contains(joined, "asm unit first_two disagrees") {
		t.Fatalf("the field address argument must bind to the caller's leaves, not refute the unit:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit first_two: proven equal") {
		t.Errorf("first_two must be proven through its callees; diagnostics:\n%s", joined)
	}
}
