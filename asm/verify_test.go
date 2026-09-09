package asm

import (
	"strings"
	"testing"
)

func verifyCase(t *testing.T, decl, oakBody, asmBody string) Verdict {
	t.Helper()
	unit, errs := ParseUnit("v.oakasm", decl+" = {\n"+asmBody+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	sig, err := parseSignature(decl)
	if err != nil {
		t.Fatal(err)
	}
	if findings := Check(unit.Functions[0], sig, nil); len(findings) != 0 {
		t.Fatalf("checker: %v", findings)
	}
	spec, err := parseSignatureWithBody(decl + " = " + oakBody)
	if err != nil {
		t.Fatal(err)
	}
	return Verify(unit.Functions[0], sig, spec.Body)
}

// Verdicts are labeled proof / evidence / trusted / mismatch
// (docs/spec/94-assembler.md §8).
func TestVerifyVerdicts(t *testing.T) {
	decl := "add_asm: (left, right: u32) -> u32"
	proven := verifyCase(t, decl, "left + right", "  bind w0 = left\n  bind w1 = right\n  add w0, w0, w1\n  ret")
	if proven.Kind != VerdictProven {
		t.Fatalf("add must be proven, got %s: %s", proven.Kind, proven.Message)
	}
	// Commuted operands and a subtraction spelled as add-of-negation are the
	// same linear form.
	commuted := verifyCase(t, decl, "right + left", "  bind w0 = left\n  bind w1 = right\n  add w0, w1, w0\n  ret")
	if commuted.Kind != VerdictProven {
		t.Fatalf("commuted add must be proven, got %s", commuted.Kind)
	}
	shifted := verifyCase(t, "scale: (a: u64) -> u64", "(a + u64(2)) << 3", "  bind x0 = a\n  clobber x9\n  add x9, x0, #2\n  lsl x0, x9, #3\n  ret")
	if shifted.Kind != VerdictProven {
		t.Fatalf("add-then-shift is linear and must be proven, got %s: %s", shifted.Kind, shifted.Message)
	}

	wrong := verifyCase(t, decl, "left + right", "  bind w0 = left\n  bind w1 = right\n  sub w0, w0, w1\n  ret")
	if wrong.Kind != VerdictMismatch || !strings.Contains(wrong.Message, "disagrees") {
		t.Fatalf("sub for add must be a mismatch, got %s: %s", wrong.Kind, wrong.Message)
	}

	// Beyond the linear form the bit-blaster decides: shift-and-mask,
	// flag composition with or/xor, and a subtraction are proven; a wrong
	// mask is a mismatch with a concrete counterexample.
	masked := verifyCase(t, "low_nibble: (v: u32) -> u32", "(v >> 4) & u32(15)", "  bind w0 = v\n  clobber w9\n  lsr w9, w0, #4\n  and w0, w9, #15\n  ret")
	if masked.Kind != VerdictProven || !strings.Contains(masked.Message, "bit level") {
		t.Fatalf("shift-and-mask must be proven at the bit level, got %s: %s", masked.Kind, masked.Message)
	}
	flags := verifyCase(t, "compose: (a, b: u64) -> u64", "(a | (b << 8)) ^ u64(255)", "  bind x0 = a\n  bind x1 = b\n  clobber x9\n  lsl x9, x1, #8\n  orr x0, x0, x9\n  eor x0, x0, #255\n  ret")
	if flags.Kind != VerdictProven {
		t.Fatalf("or/xor composition must be proven, got %s: %s", flags.Kind, flags.Message)
	}
	wrongMask := verifyCase(t, "low_nibble: (v: u32) -> u32", "(v >> 4) & u32(31)", "  bind w0 = v\n  clobber w9\n  lsr w9, w0, #4\n  and w0, w9, #15\n  ret")
	if wrongMask.Kind != VerdictMismatch || !strings.Contains(wrongMask.Message, "v=") {
		t.Fatalf("a wrong mask must be a mismatch with a counterexample, got %s: %s", wrongMask.Kind, wrongMask.Message)
	}
	// A register shift count: the barrel shifter blasts it and the machine's
	// modulo-width count agrees with Oak only when the Oak side is also a
	// constant shift — so the Oak lowering refuses, and the verdict is
	// trusted rather than a false proof.
	variableShift := verifyCase(t, "shift_by: (v, n: u32) -> u32", "v << n", "  bind w0 = v\n  bind w1 = n\n  lsl w0, w0, w1\n  ret")
	if variableShift.Kind != VerdictTrusted {
		t.Fatalf("a variable shift count must be trusted (Oak traps, the machine wraps), got %s: %s", variableShift.Kind, variableShift.Message)
	}

	memory := verifyCase(t, "spill: (a: u64) -> u64", "a", "  bind x0 = a\n  frame 16\n  str x0, [sp, #-16]!\n  ldr x0, [sp], #16\n  ret")
	if memory.Kind != VerdictTrusted || !strings.Contains(memory.Message, "trusted") {
		t.Fatalf("a memory body must be trusted, got %s: %s", memory.Kind, memory.Message)
	}

	// The 32-bit width law: a w-register add wraps at 32 bits, so the
	// specification 0xFFFFFFFF + 1 == 0 holds and is proven, not mismatched.
	wrap := verifyCase(t, "inc: (a: u32) -> u32", "a + u32(1)", "  bind w0 = a\n  add w0, w0, #1\n  ret")
	if wrap.Kind != VerdictProven {
		t.Fatalf("32-bit wrapping add must be proven, got %s: %s", wrap.Kind, wrap.Message)
	}
}

// Conditional bodies (docs/spec/94-assembler.md §8, second increment): cmp
// sets NZCV as the flags of left - right, csel/cset read them as the
// comparison those flags encode, and the Oak side's `cond ? a | b` lowers
// to the same select — decided at the bit level through the subtraction
// chain.
func TestVerifyConditionalSelects(t *testing.T) {
	maxDecl := "max32: (a, b: u32) -> u32"
	maxBody := "a < b ? b | a"
	proven := verifyCase(t, maxDecl, maxBody, "  bind w0 = a\n  bind w1 = b\n  cmp w0, w1\n  csel w0, w1, w0, lo\n  ret")
	if proven.Kind != VerdictProven || !strings.Contains(proven.Message, "bit level") {
		t.Fatalf("unsigned max via csel lo must be proven, got %s: %s", proven.Kind, proven.Message)
	}
	// The reversed comparison with swapped select operands is the same function.
	swapped := verifyCase(t, maxDecl, maxBody, "  bind w0 = a\n  bind w1 = b\n  cmp w1, w0\n  csel w0, w0, w1, ls\n  ret")
	if swapped.Kind != VerdictProven {
		t.Fatalf("max via cmp b,a / csel ls must be proven, got %s: %s", swapped.Kind, swapped.Message)
	}
	// The wrong condition is a mismatch with a concrete counterexample.
	wrongCond := verifyCase(t, maxDecl, maxBody, "  bind w0 = a\n  bind w1 = b\n  cmp w0, w1\n  csel w0, w1, w0, hi\n  ret")
	if wrongCond.Kind != VerdictMismatch || !strings.Contains(wrongCond.Message, "a=") {
		t.Fatalf("csel hi for a < b must be a mismatch with a counterexample, got %s: %s", wrongCond.Kind, wrongCond.Message)
	}
	// Signedness is read off the parameter types: i32 compares signed, so
	// `lt` proves and `lo` is refuted (at a = -1, b = 0 they disagree).
	signedDecl := "max_i32: (a, b: i32) -> i32"
	signedOK := verifyCase(t, signedDecl, maxBody, "  bind w0 = a\n  bind w1 = b\n  cmp w0, w1\n  csel w0, w1, w0, lt\n  ret")
	if signedOK.Kind != VerdictProven {
		t.Fatalf("signed max via csel lt must be proven, got %s: %s", signedOK.Kind, signedOK.Message)
	}
	signedWrong := verifyCase(t, signedDecl, maxBody, "  bind w0 = a\n  bind w1 = b\n  cmp w0, w1\n  csel w0, w1, w0, lo\n  ret")
	if signedWrong.Kind != VerdictMismatch {
		t.Fatalf("unsigned lo for a signed comparison must be a mismatch, got %s: %s", signedWrong.Kind, signedWrong.Message)
	}
	// cset materializes the comparison; the 64-bit width goes through x
	// registers; an immediate compare works too.
	isZero := verifyCase(t, "is_zero: (v: u64) -> u64", "v == u64(0) ? u64(1) | u64(0)", "  bind x0 = v\n  cmp x0, #0\n  cset x0, eq\n  ret")
	if isZero.Kind != VerdictProven {
		t.Fatalf("cset eq must be proven, got %s: %s", isZero.Kind, isZero.Message)
	}
	// A select feeding arithmetic: saturating decrement.
	satDec := verifyCase(t, "sat_dec: (v: u32) -> u32", "v == u32(0) ? v | v - u32(1)", "  bind w0 = v\n  clobber w9\n  sub w9, w0, #1\n  cmp w0, #0\n  csel w0, w0, w9, eq\n  ret")
	if satDec.Kind != VerdictProven {
		t.Fatalf("saturating decrement must be proven, got %s: %s", satDec.Kind, satDec.Message)
	}
	// subs produces flags the select may read; adds does not describe a
	// comparison, so a select after it is trusted, not falsely proven.
	viaSubs := verifyCase(t, maxDecl, maxBody, "  bind w0 = a\n  bind w1 = b\n  clobber w9\n  subs w9, w0, w1\n  csel w0, w1, w0, lo\n  ret")
	if viaSubs.Kind != VerdictProven {
		t.Fatalf("flags from subs must verify, got %s: %s", viaSubs.Kind, viaSubs.Message)
	}
	viaAdds := verifyCase(t, maxDecl, maxBody, "  bind w0 = a\n  bind w1 = b\n  clobber w9\n  adds w9, w0, w1\n  csel w0, w1, w0, lo\n  ret")
	if viaAdds.Kind != VerdictTrusted {
		t.Fatalf("flags from adds are outside the subset and must be trusted, got %s: %s", viaAdds.Kind, viaAdds.Message)
	}
	// Single-flag conditions (mi/pl/vs/vc) are outside the verified subset.
	single := verifyCase(t, maxDecl, maxBody, "  bind w0 = a\n  bind w1 = b\n  cmp w0, w1\n  csel w0, w1, w0, mi\n  ret")
	if single.Kind != VerdictTrusted {
		t.Fatalf("condition mi must be trusted, got %s: %s", single.Kind, single.Message)
	}
}

// Acyclic branches (§8, third increment): a conditional branch forks the
// symbolic state under its condition; the paths' results meet as a select.
func TestVerifyAcyclicBranches(t *testing.T) {
	maxDecl := "max32: (a, b: u32) -> u32"
	maxBody := "a < b ? b | a"
	branchy := verifyCase(t, maxDecl, maxBody, "  bind w0 = a\n  bind w1 = b\n  cmp w0, w1\n  b.lo take\n  ret\ntake:\n  mov w0, w1\n  ret")
	if branchy.Kind != VerdictProven {
		t.Fatalf("max via b.lo must be proven, got %s: %s", branchy.Kind, branchy.Message)
	}
	wrongBranch := verifyCase(t, maxDecl, maxBody, "  bind w0 = a\n  bind w1 = b\n  cmp w0, w1\n  b.hs take\n  ret\ntake:\n  mov w0, w1\n  ret")
	if wrongBranch.Kind != VerdictMismatch {
		t.Fatalf("b.hs for a < b must be a mismatch, got %s: %s", wrongBranch.Kind, wrongBranch.Message)
	}
	// Two branches, three paths: a clamp.
	clamp := verifyCase(t, "clamp: (v, lo, hi: u32) -> u32", "v < lo ? lo | (v > hi ? hi | v)",
		"  bind w0 = v\n  bind w1 = lo\n  bind w2 = hi\n  cmp w0, w1\n  b.lo low\n  cmp w0, w2\n  b.hi high\n  ret\nlow:\n  mov w0, w1\n  ret\nhigh:\n  mov w0, w2\n  ret")
	if clamp.Kind != VerdictProven {
		t.Fatalf("clamp must be proven, got %s: %s", clamp.Kind, clamp.Message)
	}
	// Paths rejoining through an unconditional branch into a shared tail.
	rejoin := verifyCase(t, maxDecl, "(a < b ? b | a) + u32(1)",
		"  bind w0 = a\n  bind w1 = b\n  clobber w9\n  cmp w0, w1\n  b.lo take\n  mov w9, w0\n  b done\ntake:\n  mov w9, w1\ndone:\n  add w0, w9, #1\n  ret")
	if rejoin.Kind != VerdictProven {
		t.Fatalf("rejoining paths must be proven, got %s: %s", rejoin.Kind, rejoin.Message)
	}
	// A backward branch is a loop: outside the subset, trusted.
	loop := verifyCase(t, "cd: (n: u32) -> u32", "u32(0)", "  bind w0 = n\nagain:\n  cmp w0, #0\n  b.eq done\n  sub w0, w0, #1\n  b again\ndone:\n  ret")
	if loop.Kind != VerdictTrusted || !strings.Contains(loop.Message, "loop") {
		t.Fatalf("a loop must be trusted, got %s: %s", loop.Kind, loop.Message)
	}
	// Bool results and compound conditions: `&&` over two comparisons is the
	// branch chain, and a Bool-typed body is its 0/1 representation.
	inRange := verifyCase(t, "in_range: (v, lo, hi: u32) -> Bool", "lo <= v && v < hi",
		"  bind w0 = v\n  bind w1 = lo\n  bind w2 = hi\n  cmp w0, w1\n  b.lo no\n  cmp w0, w2\n  b.hs no\n  mov w0, #1\n  ret\nno:\n  mov w0, #0\n  ret")
	if inRange.Kind != VerdictProven {
		t.Fatalf("a range test must be proven, got %s: %s", inRange.Kind, inRange.Message)
	}
	inRangeWrong := verifyCase(t, "in_range: (v, lo, hi: u32) -> Bool", "lo <= v && v < hi",
		"  bind w0 = v\n  bind w1 = lo\n  bind w2 = hi\n  cmp w0, w1\n  b.lo no\n  cmp w0, w2\n  b.hi no\n  mov w0, #1\n  ret\nno:\n  mov w0, #0\n  ret")
	if inRangeWrong.Kind != VerdictMismatch {
		t.Fatalf("an inclusive upper bound for an exclusive one must be a mismatch, got %s: %s", inRangeWrong.Kind, inRangeWrong.Message)
	}
	either := verifyCase(t, "either: (a, b: u32) -> Bool", "a == u32(0) || b == u32(0)",
		"  bind w0 = a\n  bind w1 = b\n  cmp w0, #0\n  b.eq yes\n  cmp w1, #0\n  b.eq yes\n  mov w0, #0\n  ret\nyes:\n  mov w0, #1\n  ret")
	if either.Kind != VerdictProven {
		t.Fatalf("a disjunction must be proven, got %s: %s", either.Kind, either.Message)
	}
}
