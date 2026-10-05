package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A byte-absorber whose loop calls a helper when its block fills (the
// SHA-256 update's shape, docs/spec/94-assembler.md §9 "Loop invariants",
// the probed frame stores): the store `a.block[a.filled] = src[i]` at a
// data-dependent index names its slots only when the summarizer runs the
// body once, and that probe used to be skipped for any body with a call.
// The block's slots are then not loop-carried on the machine side, the Oak
// chunks have no image, and the unit was witnessed on its budget. Probed
// with the call as a clobber, the block is carried and the unit proven.
const nativeAbsorberCallProgram = `
Acc: type = struct {
  filled: u32
  blocks: u32
  block: [64]u8
}

// A loop keeps mix a callee of its own (the small-helper expansion takes
// bodies without one).
mix: (block: [64]u8, seed: u32): u32 {
  acc: u32 = seed
  i: u32 = 0
  while i < u32(64) {
    acc = (acc * u32(31)) ^ u32(block[i])
    i = i + u32(1)
  }
  acc
}

absorb: (src: []u8): u32 {
  a: Acc
  a.filled = u32(0)
  a.blocks = u32(0)
  acc: u32 = 0
  i: u32 = 0
  while i < len(src) {
    a.block[a.filled] = src[i]
    a.filled = a.filled + u32(1)
    a.filled == u32(64) ? {
      acc = acc ^ mix(a.block, acc)
      a.blocks = a.blocks + u32(1)
      a.filled = u32(0)
    }
    i = i + u32(1)
  }
  acc + a.filled * u32(65537) + a.blocks
}

main: (): i32 {
  buf: [200]u8
  i: u32 = 0
  while i < u32(200) { buf[i] = u8_trunc_u32(i * u32(7) + u32(3)); i = i + u32(1) }
  full: u32 = absorb(view(&buf))
  assert(absorb(view(&buf)[u32(0):u32(64)]) == absorb(view(&buf)[u32(0):u32(64)]))
  assert(absorb(view(&buf)[u32(0):u32(7)]) == u32(7) * u32(65537))
  i32_bits_u32(full & u32(63))
}
`

func TestNativeShapesAbsorberCallProven(t *testing.T) {
	var infos []string
	comp := nativeShapeCompilation("absorb.oak", nativeAbsorberCallProgram).WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	if _, err := comp.Check().Get(); err != nil {
		t.Fatalf("check: %v\n%s", err, strings.Join(infos, "\n"))
	}
	joined := strings.Join(infos, "\n")
	if !strings.Contains(joined, "asm unit absorb: proven equal") {
		t.Errorf("absorb must be proven with its block carried through the call; diagnostics:\n%s", joined)
	}
}

func TestE2ENativeAbsorberCall(t *testing.T) {
	requireArm64Host(t)
	_, nCode, nAbnormal := buildAndRunFrom(t, "native_absorber_call", New().WithSource("absorb.oak", nativeAbsorberCallProgram).WithNativeBodies().WithNativeAsm())
	_, cCode, cAbnormal := buildAndRunFrom(t, "native_absorber_call_c", New().WithSource("absorb.oak", nativeAbsorberCallProgram))
	if nAbnormal || cAbnormal || nCode != cCode {
		t.Fatalf("native (%d, abnormal=%v) and C (%d, abnormal=%v) disagree", nCode, nAbnormal, cCode, cAbnormal)
	}
}
