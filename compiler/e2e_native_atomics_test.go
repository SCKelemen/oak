package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Atomics in the native subset (docs/spec/65-machine-memory.md section 7a;
// the OS pilot's N7): cells reached by storage path through a writable
// span — an element of `[*]Atomic[u32]`, an atomic field of a `[*]Cursor`
// element — under every builtin kind: ordered loads and stores, a fence,
// fetch-add, exchange, and compare-exchange. The function lowers natively
// and computes what the C backend computes.
const nativeAtomicsProgram = `
Cursor: type = struct { tail: Atomic[u32], head: Atomic[u32], pad: u32 }

publish: (c: [*]Cursor, seqs: [*]Atomic[u32], slot: u32, value: u32): u32 {
  slot < len(seqs) && len(c) > u32(0) ? {
    atomic_store_relaxed(seqs[slot], value)
    prev: u32 = atomic_fetch_add_acq_rel(c[0].tail, u32(1))
    atomic_store_release(c[0].head, prev + u32(1))
    atomic_fence_release()
    observed: u32 = atomic_compare_exchange_acq_rel_acquire(c[0].tail, prev + u32(1), prev + u32(2))
    swapped: u32 = atomic_exchange_acquire(seqs[slot], value + u32(7))
    atomic_load_acquire(c[0].head) + observed + swapped + atomic_load_relaxed(seqs[slot])
  } | { u32(0) }
}

narrow: (flags: [*]Atomic[u8], i: u32): u32 {
  i < len(flags) ? {
    atomic_store_seq_cst(flags[i], u8(3))
    was: u8 = atomic_fetch_add_relaxed(flags[i], u8(4))
    u32(was) + u32(atomic_load_seq_cst(flags[i]))
  } | { u32(0) }
}

main: (): i32 {
  cursors: [1]Cursor
  seqs: [4]Atomic[u32]
  flags: [2]Atomic[u8]
  // tail 0 -> 1 (prev 0), head 1, CAS 1 -> 2 observes 1, exchange returns 10, seqs[2] = 17: 1 + 1 + 10 + 17 = 29
  first: u32 = publish(span(&cursors), span(&seqs), u32(2), u32(10))
  // tail 2 -> 3 (prev 2), head 3, CAS 3 -> 4 observes 3, exchange returns 20, seqs[1] = 27: 3 + 3 + 20 + 27 = 53
  second: u32 = publish(span(&cursors), span(&seqs), u32(1), u32(20))
  // was 3, then 7: 10
  third: u32 = narrow(span(&flags), u32(1))
  i32_bits_u32(first + second + third)
}
`

func TestE2ENativeAtomics(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("atomics.oak", nativeAtomicsProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_atomics", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 29+53+10 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want %d\n%s", code, abnormal, 29+53+10, joined)
	}
	for _, fn := range []string{"publish", "narrow"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s must lower natively; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_atomics_c", New().WithSource("atomics.oak", nativeAtomicsProgram)); abnormal || code != 29+53+10 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want %d", code, abnormal, 29+53+10)
	}
	if got := interpretChecked(t, nativeAtomicsProgram); got != 29+53+10 {
		t.Fatalf("interpreter: %d", got)
	}
}
