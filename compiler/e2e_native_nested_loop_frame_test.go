package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A loop whose iteration stores nothing to a span keeps the span's entry
// memory (docs/spec/94-assembler.md §9, the field-sensitive marker). Inside
// another loop's body, that restore must leave the enclosing loop's marker
// in the log: the bit scan below reads the pool through both loops and
// stores once past them (the shape of the stdlib's id_pool_allocate),
// which panicked the lowering when the inner loop's restore dropped the
// outer loop's memory.
const nativeNestedLoopFrameProgram = `
find_free: (storage: [*]u8, limit: u32): u32 {
  needed: u32 = (limit + u32(7)) / u32(8)
  byte_index: u32 = 0
  id: u32 = limit
  while byte_index < needed && byte_index < len(storage) && id == limit {
    storage[byte_index] != u8(255) ? {
      bit: u32 = 0
      while bit < u32(8) && id == limit {
        candidate: u32 = byte_index * u32(8) + bit
        mask: u8 = u8(1) << u8_trunc_u32(bit)
        candidate < limit && (storage[byte_index] & mask) == u8(0) ? { id = candidate }
        bit = bit + u32(1)
      }
    }
    byte_index = byte_index + u32(1)
  }
  slot: u32 = id / u32(8)
  id < limit && slot < len(storage) ? { storage[slot] = storage[slot] | (u8(1) << u8_trunc_u32(id % u32(8))) }
  id
}

main: (): i32 {
  pool: [4]u8 = [4]u8{ 255, 3, 0, 0 }
  first: u32 = find_free(span(&pool), u32(32))
  second: u32 = find_free(span(&pool), u32(32))
  // 10, then 11 once bit 10 is taken: 1011.
  i32_bits_u32(first * u32(100) + second)
}
`

func TestE2ENativeNestedLoopKeepsTheOuterMemoryMarker(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("nested.oak", nativeNestedLoopFrameProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	joined := strings.Join(infos, "\n")
	lowered := false
	for _, f := range model.AsmFunctions {
		if f.Name == "find_free" {
			lowered = true
		}
	}
	if !lowered {
		t.Fatalf("find_free was not lowered natively:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit find_free:") {
		t.Errorf("find_free's verification left no verdict:\n%s", joined)
	}
}
