package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Compound reads of an owned-array field of a span element (the OS pilot's
// N4: `virq.next_pending`, `timer.next`). One `doms[d].pending[i]` read
// lowered before; the same read repeated, inside a comparison, or inside
// nested `?` arms fell back to C because the generator's type query
// resolved the array field by lowering the element address — emitting
// code && pinning a scratch register for every query until the pool ran
// dry. The functions lower natively && agree with the C backend.
const nativeCompoundProgram = `
Dom: type = struct { pending: [8]u32, count: u32, mask: u32 }

// The pilot's shape: the same element-field read in a comparison, in both
// arms of a nested conditional, && once more in the result.
next_pending: (doms: [*]Dom, d: u32, i: u32): u32 {
  d < len(doms) && i < u32(8) ? {
    doms[d].pending[i] != u32(0) && doms[d].pending[i] > doms[d].count ? {
      doms[d].pending[i] - doms[d].count
    } | {
      doms[d].pending[i] == u32(0) ? { doms[d].mask } | { doms[d].pending[i] + doms[d].count }
    }
  } | { u32(0) }
}

// The same reads through a view.
peek: (doms: []Dom, d: u32): u32 {
  d < len(doms) ? {
    doms[d].pending[u32(1)] > doms[d].pending[u32(2)] ? {
      doms[d].pending[u32(1)] - doms[d].pending[u32(2)]
    } | { doms[d].pending[u32(2)] - doms[d].pending[u32(1)] }
  } | { u32(0) }
}

// A scan with the read in the loop condition && the body.
first_set: (doms: [*]Dom, d: u32): u32 {
  i: u32 = u32(0)
  d < len(doms) ? {
    while i < u32(8) && doms[d].pending[i] == u32(0) {
      i = i + u32(1)
    }
    i < u32(8) ? { doms[d].pending[i] } | { u32(0) }
  } | { u32(0) }
}

main: (): i32 {
  doms: [2]Dom
  doms[u32(1)].count = u32(5)
  doms[u32(1)].mask = u32(77)
  doms[u32(1)].pending[u32(3)] = u32(9)
  doms[u32(1)].pending[u32(1)] = u32(4)
  doms[u32(1)].pending[u32(2)] = u32(30)
  a: u32 = next_pending(span(&doms), u32(1), u32(3))  // 9 > 5: 4
  b: u32 = next_pending(span(&doms), u32(1), u32(1))  // 4 <= 5: 4 + 5 = 9
  c: u32 = next_pending(span(&doms), u32(1), u32(0))  // zero: mask 77
  p: u32 = peek(view(&doms), u32(1))                   // 30 - 4 = 26
  f: u32 = first_set(span(&doms), u32(1))              // first set is index 1: 4
  // 4 + 9 + 77 + 26 + 4 = 120
  i32_bits_u32(a + b + c + p + f)
}
`

func TestE2ENativeCompoundElementFieldReads(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("compound.oak", nativeCompoundProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_compound", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 120 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 120\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"next_pending", "peek", "first_set"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s must lower natively with repeated element-field reads; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_compound_c", New().WithSource("compound.oak", nativeCompoundProgram)); abnormal || code != 120 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 120", code, abnormal)
	}
}
