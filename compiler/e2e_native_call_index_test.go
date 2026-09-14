package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// An index or value that calls, into an owned-array field of a span
// element (the OS pilot's N8: `s[dom].pages[cell(i, j)] = v` in
// stage2.reset). The element address used to be computed first, spilled
// around the `bl`, and reloaded — without the region fact the checker
// held before the call, so the store was refused ("memory operands go
// through the declared sp frame or a bound span base"). Operands that
// call are now evaluated before the place. Native exit == C exit.
const nativeCallIndexProgram = `
entries: u32 = 8

Dom: type = struct { pages: [64]u64, entry_count: [8]u32, root: u64, flags: u32 }

pub cell: (t: u32, i: u32): u32 = t * entries + i
pub count_of: (t: u32): u32 = t * u32(3) + u32(1)

reset: (s: [*]Dom, dom: u32): u32 {
  dom < len(s) ? {
    i: u32 = u32(0)
    while i < u32(8) {
      j: u32 = u32(0)
      while j < entries {
        s[dom].pages[cell(i, j)] = u64(cell(i, j))
        j = j + u32(1)
      }
      s[dom].entry_count[u32(i)] = count_of(i)
      i = i + u32(1)
    }
    s[dom].root = u64(7)
    s[dom].flags
  } | { u32(1) }
}

sum: (s: [*]Dom, dom: u32): u64 {
  dom < len(s) ? {
    s[dom].pages[cell(u32(3), u32(2))] + u64(s[dom].entry_count[u32(5)]) + s[dom].root
  } | { u64(0) }
}

main: (): i32 {
  doms: [2]Dom
  doms[u32(1)].flags = u32(9)
  a: u32 = reset(span(&doms), u32(1))
  b: u64 = sum(span(&doms), u32(1))
  // a = 9; b = 26 + 16 + 7 = 49; 58
  i32_bits_u32(a + u32_trunc_u64(b))
}
`

func TestE2ENativeCallIndex(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("call_index.oak", nativeCallIndexProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_call_index", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 58 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 58\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"reset", "sum"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s must lower natively with a calling index; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_call_index_c", New().WithSource("call_index.oak", nativeCallIndexProgram)); abnormal || code != 58 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 58", code, abnormal)
	}
}
