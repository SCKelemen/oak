package compiler

import "testing"

// The hypervisor pilot's reported shapes (SCKelemen/os pilots/oak/findings.md,
// oak#48 and oak#50), locked executable at HEAD so the spellings are
// greppable and cannot regress: guarded stores inside ?-match arms into a
// const-parameter generic record global (the virq ack/EOI shape), scalar
// reassignment in arms, and field extraction with the explicit conversion
// family (u8_trunc_u64 of a shifted ESR, i32_bits_u32).
func TestE2EPilotGuardedStoresInArms(t *testing.T) {
	code, abnormal := buildAndRun(t, "pilotstores", `
Virq[N: u32]: type = struct {
  latched: [N]u8
  pending: u32
}

Ev: type = Ack: u32 | Eoi: u32 | Nop

irqs: Virq[4]

fn ack(e: Ev) -> u32 {
  handled: u32 = 0
  e ?
    | .Ack(id) => {
      irqs.latched[id] = u8(0)
      irqs.pending = irqs.pending - u32(1)
      handled = u32(1)
    }
    | .Eoi(id) => {
      id < u32(4) ? { irqs.latched[id] = u8(2) }
      handled = u32(1)
    }
    | .Nop => { }
  handled
}

main: (): i32 {
  irqs.latched[u32(1)] = u8(1)
  irqs.pending = u32(1)
  assert(ack(.Ack(1)) == u32(1))
  assert(irqs.latched[u32(1)] == u8(0))
  assert(irqs.pending == u32(0))
  assert(ack(.Eoi(3)) == u32(1))
  assert(irqs.latched[u32(3)] == u8(2))
  assert(ack(.Nop) == u32(0))

  x: u32 = 0
  x == u32(0) ? { x = u32(42) } | { x = u32(7) }
  assert(x == u32(42))
  42
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// Trap decoding is field extraction all the way down: the explicit
// conversion family ({target}_{op}_{source}) narrows and reinterprets
// under a greppable spelling while iN(uN) stays widening-only.
func TestE2EPilotFieldExtraction(t *testing.T) {
	code, abnormal := buildAndRun(t, "pilotextract", `
main: (): i32 {
  esr: u64 = 0x96000045
  ec: u8 = u8_trunc_u64(esr >> 26)
  iss: u32 = u32_trunc_u64(esr & 0x1FFFFFF)
  assert(ec == u8(0x25))
  assert(iss == u32(0x45))

  all: u32 = 0xFFFFFFFF
  asSigned: i32 = i32_bits_u32(all)
  assert(asSigned == -1)

  wide: u32 = 300
  clamped: u8 = u8_saturating_u32(wide)
  assert(clamped == u8(255))
  42
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// Stage-2 PTE arrays: generic functions over wide-element spans.
func TestE2EPilotSpanGenericOverU64(t *testing.T) {
	code, abnormal := buildAndRun(t, "pilotspan", `
sum2[T]: (s: [*]T): T {
  s[0] + s[1]
}

main: (): i32 {
  ptes: [2]u64
  ptes[0] = u64(0x40000000)
  ptes[1] = u64(0x2)
  sp: [*]u64 = span(&ptes)
  assert(sum2(sp) == u64(0x40000002))
  42
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
