package asm

import (
	"strings"
	"testing"
)

// Frame memory (docs/spec/94-assembler.md §8): stores record terms at
// entry-relative slots, loads read them back, and callee-saved registers
// are the caller's opaque values — so spills and save/restore bodies are
// proven rather than trusted.
func TestVerifyFrameMemory(t *testing.T) {
	// A spill and reload around an addition.
	spill := verifyCase(t, "inc: (a: u64) -> u64", "a + u64(1)",
		"  bind x0 = a\n  clobber x9\n  frame 16\n  str x0, [sp, #-16]!\n  ldr x9, [sp], #16\n  add x0, x9, #1\n  ret")
	if spill.Kind != VerdictProven {
		t.Fatalf("a spill/reload must be proven, got %s: %s", spill.Kind, spill.Message)
	}
	// Two values spilled with stp, reloaded with ldp, combined.
	pair := verifyCase(t, "combine: (a, b: u64) -> u64", "(a << 8) | b",
		"  bind x0 = a\n  bind x1 = b\n  clobber x9, x10\n  frame 16\n  stp x0, x1, [sp, #-16]!\n  ldp x9, x10, [sp], #16\n  lsl x9, x9, #8\n  orr x0, x9, x10\n  ret")
	if pair.Kind != VerdictProven {
		t.Fatalf("stp/ldp round trip must be proven, got %s: %s", pair.Kind, pair.Message)
	}
	// Callee-saved registers: saved, used as scratch, restored; the result
	// does not depend on the caller's values, which the round trip keeps.
	saved := verifyCase(t, "sum3: (a, b, c: u64) -> u64", "a + b + c",
		"  bind x0 = a\n  bind x1 = b\n  bind x2 = c\n  clobber x19, x20\n  frame 16\n  stp x19, x20, [sp, #-16]!\n  mov x19, x0\n  add x19, x19, x1\n  mov x20, x2\n  add x0, x19, x20\n  ldp x19, x20, [sp], #16\n  ret")
	if saved.Kind != VerdictProven {
		t.Fatalf("a callee-saved save/use/restore body must be proven, got %s: %s", saved.Kind, saved.Message)
	}
	// sub/add sp with explicit offsets, 32-bit slots.
	explicit := verifyCase(t, "swap_add: (a, b: u32) -> u32", "b + a",
		"  bind w0 = a\n  bind w1 = b\n  clobber w9, w10\n  frame 16\n  sub sp, sp, #16\n  str w0, [sp, #4]\n  str w1, [sp, #8]\n  ldr w9, [sp, #8]\n  ldr w10, [sp, #4]\n  add w0, w9, w10\n  add sp, sp, #16\n  ret")
	if explicit.Kind != VerdictProven {
		t.Fatalf("explicit frame slots must be proven, got %s: %s", explicit.Kind, explicit.Message)
	}
	// Reloading a slot never stored is outside the subset: trusted, never a
	// fresh value that could match by accident.
	unstored := verifyCase(t, "inc: (a: u64) -> u64", "a + u64(1)",
		"  bind x0 = a\n  clobber x9\n  frame 32\n  str x0, [sp, #-32]!\n  ldr x9, [sp, #8]\n  add sp, sp, #32\n  add x0, x9, #1\n  ret")
	if unstored.Kind != VerdictTrusted || !strings.Contains(unstored.Message, "never stored") {
		t.Fatalf("a load of an unstored slot must be trusted, got %s: %s", unstored.Kind, unstored.Message)
	}
	// Frame slots tile: a narrower reload reads the slot's low bytes
	// (little-endian), so the low half is proven and the high half refuted.
	widths := verifyCase(t, "low: (a: u64) -> u32", "u32_trunc_u64(a)",
		"  bind x0 = a\n  clobber w9\n  frame 16\n  str x0, [sp, #-16]!\n  ldr w9, [sp], #16\n  mov w0, w9\n  ret")
	if widths.Kind != VerdictProven {
		t.Fatalf("a narrower reload of the low half must be proven, got %s: %s", widths.Kind, widths.Message)
	}
	highHalf := verifyCase(t, "low: (a: u64) -> u32", "u32_trunc_u64(a)",
		"  bind x0 = a\n  clobber w9\n  frame 16\n  str x0, [sp, #-16]!\n  ldr w9, [sp, #4]\n  add sp, sp, #16\n  mov w0, w9\n  ret")
	if highHalf.Kind != VerdictMismatch {
		t.Fatalf("reloading the high half for the low half must be a mismatch, got %s: %s", highHalf.Kind, highHalf.Message)
	}
	// The wrong slot is a genuine difference: refuted.
	wrongSlot := verifyCase(t, "second: (a, b: u64) -> u64", "b",
		"  bind x0 = a\n  bind x1 = b\n  frame 16\n  stp x0, x1, [sp, #-16]!\n  ldr x0, [sp]\n  add sp, sp, #16\n  ret")
	if wrongSlot.Kind != VerdictMismatch {
		t.Fatalf("reloading the first slot for the second value must be a mismatch, got %s: %s", wrongSlot.Kind, wrongSlot.Message)
	}
}
