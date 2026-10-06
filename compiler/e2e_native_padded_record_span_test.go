package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// An array field of records with padding, through a span of records: the
// desktop WM's `Surface` (OS OAK-REQUEST #10). Passing an element by value
// copies it as two words, and the second covers `alive`, three padding
// bytes, and `hue`. The padding reads as a fresh value per load, so the
// proof holds whatever those bytes are; before, the load was refused as
// "no field" and every accessor was trusted.
const nativePaddedRecordSpanProgram = `
Surface: type = struct { id: u32, tags: u32, alive: u8, hue: u32 }
Desk: type = struct { surfaces: [4]Surface, visible_tags: u32 }

visible: (sf: Surface, mask: u32): u8 {
  r: u8 = u8(0)
  live: Bool = sf.alive == u8(1) && (sf.tags & mask) != u32(0)
  r = live ? u8(1) | r
  r
}

visible_count: (s: [*]Desk, d: u32): u32 {
  n: u32 = u32(0)
  i: u32 = u32(0)
  while i < u32(4) {
    add: Bool = visible(s[d].surfaces[i], s[d].visible_tags) == u8(1)
    n = add ? n + u32(1) | n
    i = i + u32(1)
  }
  n
}

hue_if_alive: (s: [*]Desk, d: u32, i: u32): u32 {
  d < len(s) && i < u32(4) ? {
    sf: Surface = s[d].surfaces[i]
    sf.alive == u8(1) ? sf.hue | u32(0)
  } | { u32(0) }
}

main: (): i32 {
  desks: [1]Desk
  i: u32 = 0
  while i < u32(4) {
    desks[u32(0)].surfaces[i].id = i
    desks[u32(0)].surfaces[i].tags = i == u32(2) ? u32(4) | u32(1)
    desks[u32(0)].surfaces[i].alive = i == u32(3) ? u8(0) | u8(1)
    desks[u32(0)].surfaces[i].hue = u32(100) + i
    i = i + u32(1)
  }
  desks[u32(0)].visible_tags = u32(1)
  s: [*]Desk = span(&desks)
  // Surfaces 0 and 1 are alive with tag 1; 2 has tag 4, 3 is dead: 2.
  // Surface 1's hue is 101; surface 3 is dead: 0. 2 + 101 = 103.
  i32_bits_u32(visible_count(s, u32(0)) + hue_if_alive(s, u32(0), u32(1)) + hue_if_alive(s, u32(0), u32(3)))
}
`

func TestE2ENativePaddedRecordSpan(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("padded_span.oak", nativePaddedRecordSpanProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_padded_record_span", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 103 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 103\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"visible_count", "hue_if_alive"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven equal to its Oak body") {
			t.Errorf("%s reads a padded record element and must be proven; diagnostics:\n%s", fn, joined)
		}
	}
	if strings.Contains(joined, "disagrees") {
		t.Errorf("a false mismatch over a padded record span:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_padded_record_span_c", New().WithSource("padded_span.oak", nativePaddedRecordSpanProgram)); abnormal || code != 103 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 103", code, abnormal)
	}
}
