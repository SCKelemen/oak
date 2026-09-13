package compiler

import "testing"

// The heavy-tailed and swarm samplers over the choice tape
// (docs/spec/110-testing.md "Choice tapes"): fixed tapes give fixed
// counts and masks, the cap holds, an exhausted tape draws the floor, and
// a mask over a positive number of kinds is never zero and never exceeds
// them. Interpreted here; the compiled realization runs them through the
// test runner's WAL campaign (testrunner/io_sim_test.go), since a program
// importing testing links the host externs only under oak test.
const samplerProgram = `
import(std)
import(testing)
geometric_of: (tape: []u8, max: u32): u32 {
  choices: [1]TestChoices
  test_geometric(span(&choices), tape, max)
}
mask_of: (tape: []u8, kinds: u32): u32 {
  choices: [1]TestChoices
  test_swarm_mask(span(&choices), tape, kinds)
}
main: (): i32 {
  ok: Bool = true
  // 0b00000111: three set bits then a clear one.
  seven: [1]u8 = [u8(7)]
  ok = ok && geometric_of(view(&seven), u32(10)) == u32(3)
  // 0xff then 0x03: ten set bits, capped at eight or read in full.
  long: [2]u8 = [u8(255), u8(3)]
  ok = ok && geometric_of(view(&long), u32(8)) == u32(8)
  ok = ok && geometric_of(view(&long), u32(16)) == u32(10)
  // A clear first bit and an exhausted tape both draw zero.
  even: [1]u8 = [u8(2)]
  empty: [1]u8 = [u8(0)]
  empty_view: []u8 = view(&empty)
  ok = ok && geometric_of(view(&even), u32(10)) == u32(0)
  ok = ok && geometric_of(subslice(empty_view, u32(0), u32(0)), u32(10)) == u32(0)
  // test_delay: floor plus unit per count.
  choices: [1]TestChoices
  ok = ok && test_delay(span(&choices), view(&seven), u32(100), u32(10), u32(5)) == u32(130)
  // Swarm masks: every byte drawn is one Bool per kind (a byte's low bit),
  // so 1,0,1 over three kinds is 0b101; all-clear bytes fall back to one
  // kind chosen by the next tape word, here kind 0.
  picked: [3]u8 = [u8(1), u8(0), u8(1)]
  ok = ok && mask_of(view(&picked), u32(3)) == u32(5)
  none: [8]u8 = [u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0)]
  none_view: []u8 = view(&none)
  ok = ok && mask_of(none_view, u32(3)) == u32(1)
  ok = ok && mask_of(subslice(none_view, u32(0), u32(0)), u32(6)) == u32(1)
  ok = ok && mask_of(view(&none), u32(0)) == u32(0)
  // Bounds over every tape of three bytes with low bits varying.
  t: u32 = u32(0)
  while t < u32(8) {
    tape: [7]u8 = [u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0)]
    tape[u32(0)] = u8_trunc_u32(t & u32(1))
    tape[u32(1)] = u8_trunc_u32((t >> u32(1)) & u32(1))
    tape[u32(2)] = u8_trunc_u32((t >> u32(2)) & u32(1))
    m: u32 = mask_of(view(&tape), u32(3))
    ok = ok && m > u32(0) && m < u32(8)
    t = t + u32(1)
  }
  ok ? 42 | 1
}
`

func TestE2ETestingSamplersInterpreted(t *testing.T) {
	if got := interpretChecked(t, samplerProgram); got != 42 {
		t.Fatalf("interpreter: got %d, want 42", got)
	}
}
