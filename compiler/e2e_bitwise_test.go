package compiler

import "testing"

// Bitwise and shift operators (docs/spec/10-syntax.md §3b): the register
// bitfield vocabulary — set with |, mask with &, clear with & ^mask,
// extract with shift-and-mask. Unsigned-only, same-width, hex literals.
// This is the F7 shape: an HCR_EL2-style trap-control register.
func TestE2ERegisterBitfields(t *testing.T) {
	code, abnormal := buildAndRun(t, "bitfields", `
main: (): i32 {
  hcrVM: u64 = 0x1
  hcrFMO: u64 = 0x8
  hcrIMO: u64 = 0x10
  hcrTGE: u64 = u64(1) << 27

  hcr: u64 = hcrVM | hcrFMO | hcrIMO | hcrTGE

  assert(hcr == 0x8000019)
  assert(hcr & hcrFMO == hcrFMO)

  cleared: u64 = hcr & ^hcrFMO
  assert(cleared & hcrFMO == 0)
  assert(cleared & hcrVM == hcrVM)

  field: u64 = (hcr >> 3) & 0x3
  assert(field == 0x3)

  toggled: u64 = hcr ^ hcrVM ^ hcrVM
  assert(toggled == hcr)

  lane: u32 = 0b1010
  assert(lane | 0b0101 == 0xF)

  i: u32 = 0
  bits: u32 = 0
  while i < u32(4) {
    bits = bits | (u32(1) << i)
    i = i + 1
  }
  assert(bits == 0xF)

  assert(bits + u32(27) == u32(42))
  42
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42 (15 + 27)", code, abnormal)
	}
}

// A variable shift count that reaches the operand width traps — C makes it
// UB, Oak makes it a fail-stop (same doctrine as bounds checks).
func TestE2EOversizedShiftTraps(t *testing.T) {
	code, abnormal := buildAndRun(t, "shifttrap", `
width: u32 = 32

main: (): i32 {
  v: u32 = 1
  x: u32 = v << width
  assert(x == 0)
  0
}
`)
	if !abnormal && code == 0 {
		t.Fatalf("oversized variable shift must trap, got exit = (%d, abnormal=%v)", code, abnormal)
	}
}

// Inside a bare-expression ?-match arm, | stays the arm separator;
// parenthesized (a | b) is bitwise or. Outside arms, bare | is bitwise or.
func TestE2EBitwiseOrArmRule(t *testing.T) {
	code, abnormal := buildAndRun(t, "armrule", `
main: (): i32 {
  a: u32 = 0x28
  b: u32 = 0x2
  picked: u32 = a > b ? (a | b) | a
  bare: u32 = a | b
  assert(picked == 0x2A)
  assert(bare == 0x2A)
  42
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// The two pilot gaps that already existed upstream, locked executable:
// F6 — same-width cross-sign conversion is spelled i32_bits_u32 (total,
// two's-complement); F10 — conditional mutation is the single-arm
// statement ?-match, no else arm required.
func TestE2EBitsConversionAndConditionalMutation(t *testing.T) {
	code, abnormal := buildAndRun(t, "f6f10", `
main: (): i32 {
  all: u32 = 0xFFFFFFFF
  asSigned: i32 = i32_bits_u32(all)
  assert(asSigned == -1)

  best: u32 = 5
  v: u32 = 9
  v > best ? { best = v }
  v < best ? { best = 0 }
  assert(best == u32(9))
  42
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
