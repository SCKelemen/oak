package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// An index the lowering loads twice from the same frame slot — a record
// field guarded once and then used to index (the standard library's
// builders) — keeps its guard through the slot
// (Oak.Assembler.guard_through_slot, docs/spec/94-assembler.md §9.ah): the
// store's index needs no second compare, and the verifier still proves the
// body.
const nativeSlotIndexProgram = `
Builder: type = struct {
  length: u32
  failed: Bool
}

append_at: (state: Builder, storage: [*]u8, value: u8): Builder {
  next: Builder = state
  state.failed ? { next } | {
    assert(state.length <= len(storage))
    state.length < len(storage) ? {
      storage[state.length] = value
      next.length = state.length + u32(1)
    } | { next.failed = true }
    next
  }
}

main: (): i32 {
  buf: [4]u8
  start: Builder = Builder { length: u32(1), failed: false }
  done: Builder = append_at(start, span(&buf), u8(7))
  i32_bits_u32(done.length + u32(40))
}
`

func TestE2ENativeSlotIndexElision(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("slot_index.oak", nativeSlotIndexProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	if _, err := comp.Check().Get(); err != nil {
		t.Fatal(err)
	}
	joined := strings.Join(infos, "\n")
	if !strings.Contains(joined, "append_at: 1 element guard(s) elided") {
		t.Fatalf("the store's index must be elided through its slot:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit append_at: proven equal") {
		t.Fatalf("append_at must stay proven with the guard elided:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_slot_index", comp); abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
}
