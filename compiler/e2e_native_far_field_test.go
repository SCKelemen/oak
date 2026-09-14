package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A field of a span element past one immediate's reach (the OS pilot's N8,
// shape 2): `entry_count` sits at 393 264 bytes, behind a 393 216-byte
// page array and a 48-byte stack, so its address takes `add … lsl #12`
// then `add … #48` in place. The checker keeps the element's region
// through the in-place add, so the guarded store is admitted. The
// function lowers natively and agrees with the C backend.
const nativeFarFieldProgram = `
entries: u32 = 8

Dom: type = struct { pages: [49152]u64, free_stack: [24]u16, entry_count: [24]u16, pool_base: u64 }

pub cell: (t: u32, i: u32): u32 = t * entries + i

z: (s: [*]Dom, dom: u32): u32 {
  dom < len(s) ? {
    i: u32 = u32(0)
    while i < u32(24) {
      j: u32 = u32(0)
      while j < entries {
        s[dom].pages[cell(i, j)] = u64(cell(i, j))
        j = j + u32(1)
      }
      s[dom].free_stack[u32(i)] = u16_trunc_u32(i)
      s[dom].entry_count[u32(i)] = u16_trunc_u32(i * u32(2))
      i = i + u32(1)
    }
    s[dom].pool_base = s[dom].pages[cell(u32(2), u32(3))]
    u32(s[dom].entry_count[u32(3)]) + u32(s[dom].free_stack[u32(5)]) + u32_trunc_u64(s[dom].pool_base)
  } | { u32(1) }
}

main: (): i32 {
  doms: [1]Dom
  // 6 + 5 + 19 = 30
  i32_bits_u32(z(span(&doms), u32(0)))
}
`

func TestE2ENativeFarField(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("far_field.oak", nativeFarFieldProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_far_field", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 30 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 30\n%s", code, abnormal, joined)
	}
	if !strings.Contains(joined, "asm unit z:") {
		t.Errorf("z must lower natively with its far field; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_far_field_c", New().WithSource("far_field.oak", nativeFarFieldProgram)); abnormal || code != 30 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 30", code, abnormal)
	}
}
