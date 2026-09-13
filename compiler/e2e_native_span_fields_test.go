package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Owned-array fields of a span element in compound reads through the
// native backend — the OS pilot's N4 (docs/notes/os-language-requests-2026-09.md):
// `s[dom].f[i]` read repeatedly in one function, inside a call's arguments,
// a comparison, and nested `?` arms. Type resolution of such a read once
// went through the array's placement, which for a span element emits the
// element address and holds a register; each read leaked one, and the
// function fell back to the C backend once the scratch registers ran out.
// The shape is virq's next_pending. The C backend's realization of the
// same program is the oracle.
const nativeSpanFieldsProgram = `
Ctl[N: u32]: type = struct {
  enabled: [N]u8
  latched: [N]u8
  active: [N]u8
  level: [N]u8
  priority: [N]u8
}

reset: (s: [*]Ctl[16], dom: u32): () {
  i: u32 = u32(0)
  while i < u32(16) {
    s[dom].enabled[i] = u8(0)
    s[dom].latched[i] = u8(0)
    s[dom].active[i] = u8(0)
    s[dom].level[i] = u8(0)
    s[dom].priority[i] = u8(128)
    i = i + u32(1)
  }
}

deliverable: (en: u8, lat: u8, act: u8, lev: u8, pri: u8, mask: u8): Bool {
  en == u8(1) && (lat == u8(1) || lev == u8(1)) && act == u8(0) && pri < mask
}

// Highest-priority deliverable id, ties to the lowest id; 16 = none.
next_pending: (s: [*]Ctl[16], dom: u32, mask: u8): u32 {
  best: u32 = u32(16)
  best_pri: u8 = u8(255)
  i: u32 = u32(0)
  while i < u32(16) {
    pri: u8 = s[dom].priority[i]
    d: Bool = deliverable(s[dom].enabled[i], s[dom].latched[i], s[dom].active[i], s[dom].level[i], pri, mask)
    take: Bool = d && (best == u32(16) || pri < best_pri)
    take ? {
      best = i
      best_pri = pri
    }
    i = i + u32(1)
  }
  best
}

// The same reads inside comparisons and nested arms, plus len of the field.
count_armed: (s: [*]Ctl[16], dom: u32): u32 {
  n: u32 = u32(0)
  i: u32 = u32(0)
  while i < u32(len(s[dom].enabled)) {
    s[dom].enabled[i] == u8(1) ? {
      s[dom].latched[i] == u8(1) || s[dom].level[i] == u8(1) ? {
        s[dom].active[i] == u8(0) ? { n = n + u32(1) }
      }
    }
    i = i + u32(1)
  }
  n
}

ack: (s: [*]Ctl[16], dom: u32, mask: u8): u32 {
  id: u32 = next_pending(s, dom, mask)
  g: Bool = id < u32(16)
  g ? {
    s[dom].latched[id] = u8(0)
    s[dom].active[id] = u8(1)
  }
  id
}

// Setup through the span parameter, as the ports drive their state.
arm: (s: [*]Ctl[16], dom: u32, id: u32, pri: u8, edge: u8, lvl: u8): () {
  s[dom].enabled[id] = u8(1)
  s[dom].latched[id] = edge
  s[dom].level[id] = lvl
  s[dom].priority[id] = pri
}

active_sum: (s: [*]Ctl[16], dom: u32): i32 {
  i32(s[dom].active[3]) + i32(s[dom].active[9]) + i32(s[dom].active[12]) + i32(s[dom].active[5])
}

main: (): i32 {
  pool: [2]Ctl[16]
  s: [*]Ctl[16] = span(&pool)
  reset(s, u32(0))
  reset(s, u32(1))
  arm(s, u32(1), u32(3), u8(40), u8(1), u8(0))
  arm(s, u32(1), u32(9), u8(20), u8(0), u8(1))
  arm(s, u32(1), u32(12), u8(20), u8(1), u8(0))
  arm(s, u32(1), u32(5), u8(10), u8(1), u8(0))
  assert(ack(s, u32(1), u8(255)) == u32(5))
  assert(next_pending(s, u32(0), u8(255)) == u32(16))
  assert(next_pending(s, u32(1), u8(255)) == u32(9))
  assert(next_pending(s, u32(1), u8(20)) == u32(16))
  assert(next_pending(s, u32(1), u8(21)) == u32(9))
  assert(count_armed(s, u32(1)) == u32(3))
  assert(ack(s, u32(1), u8(255)) == u32(9))
  assert(next_pending(s, u32(1), u8(255)) == u32(12))
  assert(count_armed(s, u32(1)) == u32(2))
  assert(ack(s, u32(1), u8(255)) == u32(12))
  assert(ack(s, u32(1), u8(255)) == u32(3))
  assert(ack(s, u32(1), u8(255)) == u32(16))
  assert(count_armed(s, u32(1)) == u32(0))
  active_sum(s, u32(1)) + 38
}
`

func TestE2ENativeSpanArrayFields(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("spanfields.oak", nativeSpanFieldsProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_span_fields", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native span array fields: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"reset", "deliverable", "next_pending", "count_armed", "ack", "arm", "active_sum"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	if strings.Contains(joined, "not a span parameter") {
		t.Errorf("a read of an array field of a span element fell back:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_span_fields_c", New().WithSource("spanfields.oak", nativeSpanFieldsProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
