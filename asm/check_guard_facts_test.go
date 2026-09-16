package asm

import (
	"strings"
	"testing"
)

// The index guards the checker carries past a copy, a slack compare, and a
// call — the admissions that let the native lowering elide the guards the
// typechecker proved (docs/spec/94-assembler.md §9, "Proof-guided
// elision"); each cites its law.
func TestCheckerGuardFacts(t *testing.T) {
	decl := "read: (v: []u8, i: u32) -> u32"
	symbols := map[string]bool{"helper": true}
	epilogue := "\ntrap:\n  brk #1"
	// A body that calls: the span parked in x19/w20, the index in w21.
	callPrologue := "  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10, x19, x20, x21, x29, x30\n  frame 48\n  sub sp, sp, #48\n  stp x29, x30, [sp]\n  stp x19, x20, [sp, #16]\n  str x21, [sp, #32]\n  mov x19, x0\n  mov w20, w1\n  mov w21, w2\n"
	callEpilogue := "\n  ldr x21, [sp, #32]\n  ldp x19, x20, [sp, #16]\n  ldp x29, x30, [sp]\n  add sp, sp, #48\n  ret" + epilogue
	accepts := []struct{ name, body string }{
		{"add #0 carries the guard (Oak.SpanAlias.idxMeans_preserved)",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9\n  cmp w2, w1\n  b.hs trap\n  add w9, w2, #0\n  ldrb w0, [x0, w9, uxtw]\n  ret" + epilogue},
		{"exclusive slack guard admits the reads before the slack (Oak.Assembler.slack_guard_strict)",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10\n  cmp w1, #4\n  b.lo trap\n  mov w9, w1\n  sub w9, w9, #4\n  cmp w2, w9\n  b.hs trap\n  add w10, w2, #3\n  ldrb w0, [x0, w10, uxtw]\n  ret" + epilogue},
		{"guard on callee-saved registers survives a call",
			callPrologue + "  cmp w21, w20\n  b.hs trap\n  bl helper\n  ldrb w0, [x19, w21, uxtw]" + callEpilogue},
		{"guard against the caller-saved length rebinds to its callee-saved copy",
			callPrologue + "  cmp w21, w1\n  b.hs trap\n  bl helper\n  ldrb w0, [x19, w21, uxtw]" + callEpilogue},
		{"a condition materialized then tested: cset lo, cbz (Oak.Assembler.cset_cbz)",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9\n  cmp w2, w1\n  cset w9, lo\n  cbz w9, skip\n  ldrb w0, [x0, w2, uxtw]\n  ret\nskip:\n  mov w0, wzr\n  ret"},
		{"the negated condition: cset hs, cbnz (Oak.Assembler.cset_cbnz)",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9\n  cmp w2, w1\n  cset w9, hs\n  cbnz w9, skip\n  ldrb w0, [x0, w2, uxtw]\n  ret\nskip:\n  mov w0, wzr\n  ret"},
		{"a nonzero span length admits element zero (Oak.Forwarding.unsigned_lt_one_is_zero)",
			"  bind x0, w1 = v\n  bind w2 = i\n  cbz w1, trap\n  ldrb w0, [x0]\n  ret" + epilogue},
		{"the inclusive slack guard through a boolean: cset ls, cbz",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10\n  cmp w1, #4\n  b.lo trap\n  mov w9, w1\n  sub w9, w9, #4\n  cmp w2, w9\n  cset w10, ls\n  cbz w10, trap\n  add w9, w2, #3\n  ldrb w0, [x0, w9, uxtw]\n  ret" + epilogue},
		{"a masked index is bounded by its mask (Oak.Assembler.masked_index_bound)",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10, x11\n  frame 16\n  sub sp, sp, #16\n  mov x9, #0\n  stp x9, x9, [sp]\n  add x9, sp, #0\n  and w10, w2, #3\n  add x11, x9, w10, uxtw #2\n  ldr w0, [x11]\n  add sp, sp, #16\n  ret"},
		{"a mask held in a constant register",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10, x11, x12\n  frame 16\n  sub sp, sp, #16\n  mov x9, #0\n  stp x9, x9, [sp]\n  add x9, sp, #0\n  movz w12, #3\n  and w10, w2, w12\n  add x11, x9, w10, uxtw #2\n  ldr w0, [x11]\n  add sp, sp, #16\n  ret"},
		{"a loaded byte indexes a 256-entry array (Oak.Assembler.narrow_value_bound)",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10, x11\n  frame 1024\n  sub sp, sp, #1024\n  cmp w1, #1\n  b.lo trap\n  ldrb w9, [x0]\n  add x10, sp, #0\n  add x11, x10, w9, uxtw #2\n  ldr w0, [x11]\n  add sp, sp, #1024\n  ret" + epilogue},
		{"a zero-extended byte indexes a 256-entry array",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10, x11\n  frame 1024\n  sub sp, sp, #1024\n  uxtb w9, w2\n  add x10, sp, #0\n  add x11, x10, w9, uxtw #2\n  ldr w0, [x11]\n  add sp, sp, #1024\n  ret"},
		{"an exact length is a minimum: cmp #K, b.ne (Oak.Extents.exact_length_min)",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9\n  cmp w1, #2\n  b.ne trap\n  ldrb w0, [x0, #1]\n  ret" + epilogue},
		{"the zero register as a constant index",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9\n  cmp w1, #1\n  b.lo trap\n  mov w9, wzr\n  ldrb w0, [x0, w9, uxtw]\n  ret" + epilogue},
		{"a constant index in a register under the proven minimum (Oak.Assembler.constant_index_bound)",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9\n  cmp w1, #4\n  b.lo trap\n  movz w9, #3\n  ldrb w0, [x0, w9, uxtw]\n  ret" + epilogue},
		{"a guarded index spilled to a slot is guarded when it is loaded back (Oak.Assembler.guard_through_slot)",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10\n  frame 16\n  sub sp, sp, #16\n  cmp w2, w1\n  b.hs trap\n  str w2, [sp, #8]\n  ldr w9, [sp, #8]\n  ldrb w0, [x0, w9, uxtw]\n  add sp, sp, #16\n  ret" + epilogue},
		// Block versioning by fact context (docs/spec/94-assembler.md): the
		// guard holds on the path that reaches the access, and the other
		// path into the join cannot reach it, so the meet's loss of the
		// fact is not a refusal.
		{"a guard lost at a join is admitted per arriving context",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9\n  cmp w2, w1\n  cset w9, lo\n  cbz w9, skip\n  b body\nbody:\n  ldrb w0, [x0, w2, uxtw]\n  ret\nskip:\n  mov w0, wzr\n  ret"},
		{"proven minimum survives a call with the span",
			callPrologue + "  cmp w20, #2\n  b.lo trap\n  bl helper\n  ldrb w0, [x19, #1]" + callEpilogue},
	}
	for _, tc := range accepts {
		t.Run(tc.name, func(t *testing.T) {
			unit, errs := ParseUnit("guard.oakasm", decl+" = {\n"+tc.body+"\n}\n")
			if len(errs) != 0 {
				t.Fatal(errs)
			}
			sig, _ := parseSignature(decl)
			if findings := Check(unit.Functions[0], sig, symbols); len(findings) != 0 {
				t.Fatalf("must pass: %v", findings)
			}
		})
	}
	rejects := []struct{ name, body, want string }{
		{"add #1 does not carry a plain guard",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9\n  cmp w2, w1\n  b.hs trap\n  add w9, w2, #1\n  ldrb w0, [x0, w9, uxtw]\n  ret" + epilogue,
			"without a dominating index guard"},
		{"exclusive slack guard does not reach the element at the slack",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10\n  cmp w1, #4\n  b.lo trap\n  mov w9, w1\n  sub w9, w9, #4\n  cmp w2, w9\n  b.hs trap\n  add w10, w2, #4\n  ldrb w0, [x0, w10, uxtw]\n  ret" + epilogue,
			"without a dominating index guard"},
		{"slack guard without the minimum proven (the subtraction may wrap)",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10\n  mov w9, w1\n  sub w9, w9, #4\n  cmp w2, w9\n  b.hs trap\n  add w10, w2, #3\n  ldrb w0, [x0, w10, uxtw]\n  ret" + epilogue,
			"len >= 4 proven first"},
		{"inclusive slack guard without the minimum proven, scalar read",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9\n  mov w9, w1\n  sub w9, w9, #4\n  cmp w2, w9\n  b.hi trap\n  ldrb w0, [x0, w2, uxtw]\n  ret" + epilogue,
			"len >= 4 proven first"},
		{"a boolean tested after a label proves nothing",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9\n  cmp w2, w1\n  cset w9, lo\n  b join\njoin:\n  cbz w9, skip\n  ldrb w0, [x0, w2, uxtw]\n  ret\nskip:\n  mov w0, wzr\n  ret",
			"without a dominating index guard"},
		{"a boolean rewritten before the test proves nothing",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9\n  cmp w2, w1\n  cset w9, lo\n  mov w9, #1\n  cbz w9, skip\n  ldrb w0, [x0, w2, uxtw]\n  ret\nskip:\n  mov w0, wzr\n  ret",
			"without a dominating index guard"},
		{"the index rewritten between the compare and the test proves nothing",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9\n  cmp w2, w1\n  cset w9, lo\n  mov w2, #7\n  cbz w9, skip\n  ldrb w0, [x0, w2, uxtw]\n  ret\nskip:\n  mov w0, wzr\n  ret",
			"proven minimum length"},
		{"cbz on a register no compare defined proves nothing",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9\n  mov w9, #1\n  cbz w9, skip\n  ldrb w0, [x0, w2, uxtw]\n  ret\nskip:\n  mov w0, wzr\n  ret",
			"without a dominating index guard"},
		{"cbnz on a span length gives no nonempty fall-through fact",
			"  bind x0, w1 = v\n  bind w2 = i\n  cbnz w1, trap\n  ldrb w0, [x0]\n  ret" + epilogue,
			"without a dominating bounds guard"},
		{"the taken cbz edge keeps the zero-length state",
			"  bind x0, w1 = v\n  bind w2 = i\n  cbz w1, zero\n  mov w0, wzr\n  ret\nzero:\n  ldrb w0, [x0]\n  ret",
			"without a dominating bounds guard"},
		{"a mask wider than the array proves too little",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10, x11\n  frame 16\n  sub sp, sp, #16\n  mov x9, #0\n  stp x9, x9, [sp]\n  add x9, sp, #0\n  and w10, w2, #7\n  add x11, x9, w10, uxtw #2\n  ldr w0, [x11]\n  add sp, sp, #16\n  ret",
			""},
		{"a loaded halfword proves too little for a 256-entry array",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10, x11\n  frame 1024\n  sub sp, sp, #1024\n  cmp w1, #1\n  b.lo trap\n  ldrh w9, [x0]\n  add x10, sp, #0\n  add x11, x10, w9, uxtw #2\n  ldr w0, [x11]\n  add sp, sp, #1024\n  ret" + epilogue,
			""},
		{"a constant index at the proven minimum is out of range",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9\n  cmp w1, #4\n  b.lo trap\n  movz w9, #4\n  ldrb w0, [x0, w9, uxtw]\n  ret" + epilogue,
			""},
		{"a slot written with an unguarded value carries nothing",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10\n  frame 16\n  sub sp, sp, #16\n  cmp w2, w1\n  b.hs trap\n  str w2, [sp, #8]\n  mov w10, #7\n  str w10, [sp, #8]\n  ldr w9, [sp, #8]\n  ldrb w0, [x0, w9, uxtw]\n  add sp, sp, #16\n  ret" + epilogue,
			"proven minimum length"},
		{"a slot fact dies with the length register it names",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10\n  frame 16\n  sub sp, sp, #16\n  cmp w2, w1\n  b.hs trap\n  str w2, [sp, #8]\n  mov w1, #0\n  ldr w9, [sp, #8]\n  ldrb w0, [x0, w9, uxtw]\n  add sp, sp, #16\n  ret" + epilogue,
			"without a dominating index guard"},
		{"a join whose other path reaches the access unguarded is refused",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9\n  cmp w2, w1\n  cset w9, lo\n  cbz w9, body\n  b body\nbody:\n  ldrb w0, [x0, w2, uxtw]\n  ret",
			"without a dominating index guard"},
		{"guard on a caller-saved index dies at a call",
			callPrologue + "  mov w9, w21\n  cmp w9, w20\n  b.hs trap\n  bl helper\n  ldrb w0, [x19, w9, uxtw]" + callEpilogue,
			"without a dominating index guard"},
		{"guard against a length with no callee-saved copy dies at a call",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x19, x21, x29, x30\n  frame 48\n  sub sp, sp, #48\n  stp x29, x30, [sp]\n  stp x19, x21, [sp, #16]\n  mov x19, x0\n  mov w21, w2\n  cmp w21, w1\n  b.hs trap\n  bl helper\n  ldrb w0, [x19, w21, uxtw]\n  ldp x19, x21, [sp, #16]\n  ldp x29, x30, [sp]\n  add sp, sp, #48\n  ret" + epilogue,
			""},
	}
	for _, tc := range rejects {
		t.Run(tc.name, func(t *testing.T) {
			unit, errs := ParseUnit("guard.oakasm", decl+" = {\n"+tc.body+"\n}\n")
			if len(errs) != 0 {
				t.Fatal(errs)
			}
			sig, _ := parseSignature(decl)
			joined := strings.Join(Check(unit.Functions[0], sig, symbols), "\n")
			if joined == "" || !strings.Contains(joined, tc.want) {
				t.Fatalf("expected a finding mentioning %q, got:\n%s", tc.want, joined)
			}
		})
	}
}

// The divided bound (docs/spec/94-assembler.md §7): a length divided by a
// constant that is not a power of two, and an index multiplied back by it
// — the binary search over a three-word table that the typechecker
// discharges by Oak.Extents.div_bound_scaled. Each case cites its law.
func TestCheckerDividedBound(t *testing.T) {
	decl := "search: (t: []u32, k: u32) -> u32"
	symbols := map[string]bool{}
	epilogue := "\ntrap:\n  brk #1"
	// entries = len(t) / 3 in w10, the index guarded below it in w2.
	divided := "  bind x0, w1 = t\n  bind w2 = k\n  clobber x9, x10, x11, x12\n  movz w9, #3\n  udiv w10, w1, w9\n  cmp w2, w10\n  b.hs trap\n"
	accepts := []struct{ name, body string }{
		{"the scaled index itself (Oak.Assembler.scaled_index_slack)",
			divided + "  mul w11, w2, w9\n  ldr w0, [x0, w11, uxtw #2]\n  ret" + epilogue},
		{"the second word of the entry (Oak.Assembler.scaled_index_element)",
			divided + "  mul w11, w2, w9\n  add w11, w11, #1\n  ldr w0, [x0, w11, uxtw #2]\n  ret" + epilogue},
		{"the third word of the entry",
			divided + "  mul w11, w2, w9\n  add w11, w11, #2\n  ldr w0, [x0, w11, uxtw #2]\n  ret" + epilogue},
		{"the constant on the left of the multiply",
			divided + "  mul w11, w9, w2\n  ldr w0, [x0, w11, uxtw #2]\n  ret" + epilogue},
		{"a scale below the divisor leaves room to spare",
			divided + "  movz w12, #2\n  mul w11, w2, w12\n  add w11, w11, #1\n  ldr w0, [x0, w11, uxtw #2]\n  ret" + epilogue},
		{"the midpoint of the search is below the same divided bound (Oak.Assembler.midpoint_below)",
			"  bind x0, w1 = t\n  bind w2 = k\n  clobber x9, x10, x11, x12\n  movz w9, #3\n  udiv w10, w1, w9\n  mov w12, wzr\n  cmp w12, w10\n  b.hs trap\n  sub w11, w10, w12\n  lsr w11, w11, #1\n  add w11, w12, w11\n  mul w11, w11, w9\n  ldr w0, [x0, w11, uxtw #2]\n  ret" + epilogue},
	}
	for _, tc := range accepts {
		t.Run(tc.name, func(t *testing.T) {
			unit, errs := ParseUnit("divided.oakasm", decl+" = {\n"+tc.body+"\n}\n")
			if len(errs) != 0 {
				t.Fatal(errs)
			}
			sig, _ := parseSignature(decl)
			if findings := Check(unit.Functions[0], sig, symbols); len(findings) != 0 {
				t.Fatalf("must pass: %v", findings)
			}
		})
	}
	rejects := []struct{ name, body, want string }{
		{"a word past the entry is outside the slack the divisor leaves",
			divided + "  mul w11, w2, w9\n  add w11, w11, #3\n  ldr w0, [x0, w11, uxtw #2]\n  ret" + epilogue,
			"without a dominating index guard"},
		{"a scale above the divisor proves nothing",
			divided + "  movz w12, #4\n  mul w11, w2, w12\n  ldr w0, [x0, w11, uxtw #2]\n  ret" + epilogue,
			"without a dominating index guard"},
		{"an unguarded index scaled by the divisor proves nothing",
			"  bind x0, w1 = t\n  bind w2 = k\n  clobber x9, x10, x11\n  movz w9, #3\n  udiv w10, w1, w9\n  mul w11, w2, w9\n  ldr w0, [x0, w11, uxtw #2]\n  ret" + epilogue,
			"without a dominating index guard"},
		{"a quotient by a register no constant defined bounds nothing",
			"  bind x0, w1 = t\n  bind w2 = k\n  clobber x9, x10, x11\n  mov w9, w2\n  udiv w10, w1, w9\n  cmp w2, w10\n  b.hs trap\n  movz w12, #3\n  mul w11, w2, w12\n  ldr w0, [x0, w11, uxtw #2]\n  ret" + epilogue,
			"without a dominating index guard"},
		{"the divisor rewritten between the quotient and the multiply proves nothing",
			divided + "  movz w9, #1\n  mul w11, w2, w9\n  add w11, w11, #2\n  ldr w0, [x0, w11, uxtw #2]\n  ret" + epilogue,
			"without a dominating index guard"},
	}
	for _, tc := range rejects {
		t.Run(tc.name, func(t *testing.T) {
			unit, errs := ParseUnit("divided.oakasm", decl+" = {\n"+tc.body+"\n}\n")
			if len(errs) != 0 {
				t.Fatal(errs)
			}
			sig, _ := parseSignature(decl)
			findings := Check(unit.Functions[0], sig, symbols)
			if len(findings) == 0 {
				t.Fatalf("must be refused")
			}
			if tc.want != "" && !strings.Contains(strings.Join(findings, "\n"), tc.want) {
				t.Fatalf("want %q, got %v", tc.want, findings)
			}
		})
	}
}

// The same divided bound over a constant table (docs/spec/94-assembler.md
// §7): a global array whose element count is a literal, `entries = N / 3`
// folded to a constant, and the search index scaled back by three. This is
// the shape the stdlib's binary searches take — no register holds a
// length, so the bound is an immediate throughout
// (Oak.Extents.scaled_under_bound).
func TestCheckerDividedConstantBound(t *testing.T) {
	decl := "lookup: (scalar: u32) -> u32"
	symbols := map[string]bool{}
	epilogue := "\ntrap:\n  brk #1"
	// 12 four-byte words: four entries of three. entries = 12 / 3 = 4.
	table := map[string]Table{"grapheme_table": {Size: 48, Elem: 4}}
	prologue := "  bind w0 = scalar\n  clobber x9, x10, x11, x12, x13\n  adrl x9, grapheme_table\n  add x13, x9, #0\n  movz w10, #12\n  movz w11, #3\n  udiv w12, w10, w11\n"
	accepts := []struct{ name, body string }{
		{"the first word of the entry",
			prologue + "  cmp w0, w12\n  b.hs trap\n  mul w9, w0, w11\n  add x10, x13, #0\n  ldr w0, [x10, w9, uxtw #2]\n  ret" + epilogue},
		{"the third word of the entry",
			prologue + "  cmp w0, w12\n  b.hs trap\n  mul w9, w0, w11\n  add w9, w9, #2\n  add x10, x13, #0\n  ldr w0, [x10, w9, uxtw #2]\n  ret" + epilogue},
	}
	for _, tc := range accepts {
		t.Run(tc.name, func(t *testing.T) {
			unit, errs := ParseUnit("table.oakasm", decl+" = {\n"+tc.body+"\n}\n")
			if len(errs) != 0 {
				t.Fatal(errs)
			}
			unit.Functions[0].Tables = table
			sig, _ := parseSignature(decl)
			if findings := Check(unit.Functions[0], sig, symbols); len(findings) != 0 {
				t.Fatalf("must pass: %v", findings)
			}
		})
	}
	rejects := []struct{ name, body, want string }{
		{"a fourth word runs past the last entry",
			prologue + "  cmp w0, w12\n  b.hs trap\n  mul w9, w0, w11\n  add w9, w9, #3\n  add x10, x13, #0\n  ldr w0, [x10, w9, uxtw #2]\n  ret" + epilogue,
			"past the"},
		{"the quotient of a length the checker does not know is no bound",
			"  bind w0 = scalar\n  clobber x9, x10, x11, x12, x13\n  adrl x9, grapheme_table\n  add x13, x9, #0\n  movz w11, #3\n  udiv w12, w0, w11\n  cmp w0, w12\n  b.hs trap\n  mul w9, w0, w11\n  add x10, x13, #0\n  ldr w0, [x10, w9, uxtw #2]\n  ret" + epilogue,
			"without a dominating constant index guard"},
		{"an index guarded below a wider count runs past the table",
			"  bind w0 = scalar\n  clobber x9, x10, x11, x12, x13\n  adrl x9, grapheme_table\n  add x13, x9, #0\n  movz w10, #21\n  movz w11, #3\n  udiv w12, w10, w11\n  cmp w0, w12\n  b.hs trap\n  mul w9, w0, w11\n  add x10, x13, #0\n  ldr w0, [x10, w9, uxtw #2]\n  ret" + epilogue,
			"past the"},
	}
	for _, tc := range rejects {
		t.Run(tc.name, func(t *testing.T) {
			unit, errs := ParseUnit("table.oakasm", decl+" = {\n"+tc.body+"\n}\n")
			if len(errs) != 0 {
				t.Fatal(errs)
			}
			unit.Functions[0].Tables = table
			sig, _ := parseSignature(decl)
			findings := Check(unit.Functions[0], sig, symbols)
			if len(findings) == 0 {
				t.Fatalf("must be refused")
			}
			if tc.want != "" && !strings.Contains(strings.Join(findings, "\n"), tc.want) {
				t.Fatalf("want %q, got %v", tc.want, findings)
			}
		})
	}
}
