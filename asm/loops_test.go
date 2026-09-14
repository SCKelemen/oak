package asm

import (
	"fmt"
	"strings"
	"testing"
)

// Data-dependent loops (§8, sixth increment): the sum over a view, whose
// trip count is len(v), is proven by coupling the Oak locals to the asm
// registers at the loop header and checking one iteration preserves the
// coupling; disagreements surface as concrete counterexamples.
func TestVerifyDataDependentLoops(t *testing.T) {
	decl := "sum: (v: []u32) -> u32"
	oakSum := "{\n  acc: u32 = u32(0)\n  i: u32 = u32(0)\n  while i < len(v) {\n    acc = acc + v[i]\n    i = i + u32(1)\n  }\n  acc\n}"
	walk := "  bind x0, w1 = v\n  clobber w9, w10, w11\n  mov w9, #0\n  mov w10, #0\nloop:\n  cmp w9, w1\n  b.hs done\n  ldr w11, [x0, w9, uxtw #2]\n  add w10, w10, w11\n  add w9, w9, #1\n  b loop\ndone:\n  mov w0, w10\n  ret"
	proven := verifyCase(t, decl, oakSum, walk)
	if proven.Kind != VerdictProven || !strings.Contains(proven.Message, "coupled inductively") {
		t.Fatalf("the sum loop must be proven by coupling, got %s: %s", proven.Kind, proven.Message)
	}
	// The commuted accumulate is the same loop.
	commuted := verifyCase(t, decl, strings.Replace(oakSum, "acc + v[i]", "v[i] + acc", 1), walk)
	if commuted.Kind != VerdictProven {
		t.Fatalf("the commuted body must be proven, got %s: %s", commuted.Kind, commuted.Message)
	}
	// Stride 2 in the asm: a concrete input refutes it.
	stride := verifyCase(t, decl, oakSum, strings.Replace(walk, "add w9, w9, #1", "add w9, w9, #2", 1))
	if stride.Kind != VerdictMismatch || !strings.Contains(stride.Message, "len(v)=") {
		t.Fatalf("a stride-2 walk must be a mismatch with a concrete length, got %s: %s", stride.Kind, stride.Message)
	}
	// Accumulating the index instead of the element: refuted on a concrete
	// input (an inclusive exit `b.hi` never gets this far — the seam
	// checker refuses the unguarded load).
	wrongOperand := verifyCase(t, decl, oakSum, strings.Replace(walk, "add w10, w10, w11", "add w10, w10, w9", 1))
	if wrongOperand.Kind != VerdictMismatch {
		t.Fatalf("summing indices must be a mismatch, got %s: %s", wrongOperand.Kind, wrongOperand.Message)
	}
	// Different results after equal loops: refuted.
	wrongResult := verifyCase(t, decl, oakSum, strings.Replace(walk, "mov w0, w10", "mov w0, w9", 1))
	if wrongResult.Kind != VerdictMismatch {
		t.Fatalf("returning the counter must be a mismatch, got %s: %s", wrongResult.Kind, wrongResult.Message)
	}
	// A loop on one side only is outside the method: trusted.
	oneSide := verifyCase(t, decl, "len(v) == u32(0) ? u32(0) | v[0]", walk)
	if oneSide.Kind != VerdictTrusted || !strings.Contains(oneSide.Message, "data-dependent loop") {
		t.Fatalf("a loop on one side only must be trusted, got %s: %s", oneSide.Kind, oneSide.Message)
	}
	// A scalar trip count: n iterations of an accumulate, with a 64-bit
	// accumulator coupled at 64 bits.
	times := verifyCase(t, "times: (a: u64, n: u32) -> u64",
		"{\n  acc: u64 = u64(0)\n  i: u32 = u32(0)\n  while i < n {\n    acc = acc + a\n    i = i + u32(1)\n  }\n  acc\n}",
		"  bind x0 = a\n  bind w1 = n\n  clobber w9, x10\n  mov w9, #0\n  mov x10, #0\nloop:\n  cmp w9, w1\n  b.hs done\n  add x10, x10, x0\n  add w9, w9, #1\n  b loop\ndone:\n  mov x0, x10\n  ret")
	if times.Kind != VerdictProven {
		t.Fatalf("the scalar-count accumulate must be proven, got %s: %s", times.Kind, times.Message)
	}
	// Counting down in the asm against counting up in Oak: the coupling is
	// affine (w1 = n - i) and needs the invariant i <= n read off the Oak
	// guard, under which `w1 != 0` is `i < n`.
	down := verifyCase(t, "times: (a: u64, n: u32) -> u64",
		"{\n  acc: u64 = u64(0)\n  i: u32 = u32(0)\n  while i < n {\n    acc = acc + a\n    i = i + u32(1)\n  }\n  acc\n}",
		"  bind x0 = a\n  bind w1 = n\n  clobber x10\n  mov x10, #0\nloop:\n  cmp w1, #0\n  b.eq done\n  add x10, x10, x0\n  sub w1, w1, #1\n  b loop\ndone:\n  mov x0, x10\n  ret")
	if down.Kind != VerdictProven || !strings.Contains(down.Message, "r1 = ") || !strings.Contains(down.Message, "invariant") {
		t.Fatalf("a count-down loop must be proven by an affine coupling under an invariant, got %s: %s", down.Kind, down.Message)
	}
	// An offset accumulator: the asm keeps acc + a and subtracts a at the
	// exit; the coupling is r10 = acc + a with a loop-invariant offset.
	offset := verifyCase(t, "times: (a: u64, n: u32) -> u64",
		"{\n  acc: u64 = u64(0)\n  i: u32 = u32(0)\n  while i < n {\n    acc = acc + a\n    i = i + u32(1)\n  }\n  acc\n}",
		"  bind x0 = a\n  bind w1 = n\n  clobber w9, x10\n  mov w9, #0\n  mov x10, x0\nloop:\n  cmp w9, w1\n  b.hs done\n  add x10, x10, x0\n  add w9, w9, #1\n  b loop\ndone:\n  sub x0, x10, x0\n  ret")
	if offset.Kind != VerdictProven || !strings.Contains(offset.Message, "r10 = acc + a") {
		t.Fatalf("an offset accumulator must be proven by r10 = acc + a, got %s: %s", offset.Kind, offset.Message)
	}
	// A 1-based inclusive counter (`cmp w9, w1; b.hi`) is NOT the count-up
	// loop: at n = 0xFFFFFFFF the asm counter wraps and never exits. The
	// verifier must not prove it — witness-checked is the honest verdict.
	inclusive := verifyCase(t, "times: (a: u64, n: u32) -> u64",
		"{\n  acc: u64 = u64(0)\n  i: u32 = u32(0)\n  while i < n {\n    acc = acc + a\n    i = i + u32(1)\n  }\n  acc\n}",
		"  bind x0 = a\n  bind w1 = n\n  clobber w9, x10\n  mov w9, #1\n  mov x10, #0\nloop:\n  cmp w9, w1\n  b.hi done\n  add x10, x10, x0\n  add w9, w9, #1\n  b loop\ndone:\n  mov x0, x10\n  ret")
	if inclusive.Kind != VerdictWitnessed {
		t.Fatalf("the wrapping inclusive counter must not be proven, got %s: %s", inclusive.Kind, inclusive.Message)
	}
}

// Forks inside a data-dependent loop body: the asm body's paths merge into
// selects at the back edge, and Oak's statement-level conditional merges
// its arms the same way — both couple to the value-position spelling.
func TestVerifyLoopBodyForks(t *testing.T) {
	decl := "count_gt: (v: []u32, t: u32) -> u32"
	valueForm := "{\n  n: u32 = u32(0)\n  i: u32 = u32(0)\n  while i < len(v) {\n    n = n + (v[i] > t ? u32(1) | u32(0))\n    i = i + u32(1)\n  }\n  n\n}"
	statementForm := "{\n  n: u32 = u32(0)\n  i: u32 = u32(0)\n  while i < len(v) {\n    v[i] > t ? { n = n + u32(1) } | { }\n    i = i + u32(1)\n  }\n  n\n}"
	branchy := "  bind x0, w1 = v\n  bind w2 = t\n  clobber w9, w10, w11\n  mov w9, #0\n  mov w10, #0\nloop:\n  cmp w9, w1\n  b.hs done\n  ldr w11, [x0, w9, uxtw #2]\n  cmp w11, w2\n  b.ls skip\n  add w10, w10, #1\nskip:\n  add w9, w9, #1\n  b loop\ndone:\n  mov w0, w10\n  ret"
	for name, body := range map[string]string{"value form": valueForm, "statement form": statementForm} {
		verdict := verifyCase(t, decl, body, branchy)
		if verdict.Kind != VerdictProven {
			t.Fatalf("%s: a branchy count loop must be proven, got %s: %s", name, verdict.Kind, verdict.Message)
		}
	}
	// The conditional select spelling of the same asm is the same function.
	selecting := "  bind x0, w1 = v\n  bind w2 = t\n  clobber w9, w10, w11, w12\n  mov w9, #0\n  mov w10, #0\nloop:\n  cmp w9, w1\n  b.hs done\n  ldr w11, [x0, w9, uxtw #2]\n  cmp w11, w2\n  cset w12, hi\n  add w10, w10, w12\n  add w9, w9, #1\n  b loop\ndone:\n  mov w0, w10\n  ret"
	if verdict := verifyCase(t, decl, statementForm, selecting); verdict.Kind != VerdictProven {
		t.Fatalf("cset spelling must be proven, got %s: %s", verdict.Kind, verdict.Message)
	}
	// The wrong branch sense counts v[i] <= t instead: refuted on a concrete input.
	wrong := verifyCase(t, decl, valueForm, strings.Replace(branchy, "b.ls skip", "b.hi skip", 1))
	if wrong.Kind != VerdictMismatch {
		t.Fatalf("the wrong branch sense must be a mismatch, got %s: %s", wrong.Kind, wrong.Message)
	}
	// A running maximum by conditional move.
	maxDecl := "max_of: (v: []u32) -> u32"
	oakMax := "{\n  best: u32 = u32(0)\n  i: u32 = u32(0)\n  while i < len(v) {\n    v[i] > best ? { best = v[i] } | { }\n    i = i + u32(1)\n  }\n  best\n}"
	asmMax := "  bind x0, w1 = v\n  clobber w9, w10, w11\n  mov w9, #0\n  mov w10, #0\nloop:\n  cmp w9, w1\n  b.hs done\n  ldr w11, [x0, w9, uxtw #2]\n  cmp w11, w10\n  b.ls keep\n  mov w10, w11\nkeep:\n  add w9, w9, #1\n  b loop\ndone:\n  mov w0, w10\n  ret"
	if verdict := verifyCase(t, maxDecl, oakMax, asmMax); verdict.Kind != VerdictProven {
		t.Fatalf("running maximum must be proven, got %s: %s", verdict.Kind, verdict.Message)
	}
}

// Nested data-dependent loops: the events form a tree on both sides, the
// inner loop is summarized while executing the outer body, and the outer
// preservation check runs under the inner loop's exit premise.
func TestVerifyNestedLoops(t *testing.T) {
	decl := "grid: (n, m: u32) -> u32"
	oakGrid := "{\n  acc: u32 = u32(0)\n  i: u32 = u32(0)\n  while i < n {\n    j: u32 = u32(0)\n    while j < m {\n      acc = acc + u32(1)\n      j = j + u32(1)\n    }\n    i = i + u32(1)\n  }\n  acc\n}"
	asmGrid := "  bind w0 = n\n  bind w1 = m\n  clobber w9, w10, w11\n  mov w9, #0\n  mov w11, #0\nouter:\n  cmp w9, w0\n  b.hs done\n  mov w10, #0\ninner:\n  cmp w10, w1\n  b.hs next\n  add w11, w11, #1\n  add w10, w10, #1\n  b inner\nnext:\n  add w9, w9, #1\n  b outer\ndone:\n  mov w0, w11\n  ret"
	proven := verifyCase(t, decl, oakGrid, asmGrid)
	if proven.Kind != VerdictProven || !strings.Contains(proven.Message, "2 nested data-dependent loops") {
		t.Fatalf("the nested counter must be proven, got %s: %s", proven.Kind, proven.Message)
	}
	// The inner body advancing by two is refuted on a concrete input.
	stride := verifyCase(t, decl, oakGrid, strings.Replace(asmGrid, "add w10, w10, #1", "add w10, w10, #2", 1))
	if stride.Kind != VerdictMismatch {
		t.Fatalf("an inner stride of two must be a mismatch, got %s: %s", stride.Kind, stride.Message)
	}
	// Row sums over a view: the inner loop reads memory by a two-level index.
	rows := "rows: (v: []u32, w: u32) -> u32"
	oakRows := "{\n  acc: u32 = u32(0)\n  i: u32 = u32(0)\n  while i < len(v) {\n    j: u32 = u32(0)\n    while j < w {\n      acc = acc + v[i]\n      j = j + u32(1)\n    }\n    i = i + u32(1)\n  }\n  acc\n}"
	asmRows := "  bind x0, w1 = v\n  bind w2 = w\n  clobber w9, w10, w11, w12\n  mov w9, #0\n  mov w11, #0\nouter:\n  cmp w9, w1\n  b.hs done\n  ldr w12, [x0, w9, uxtw #2]\n  mov w10, #0\ninner:\n  cmp w10, w2\n  b.hs next\n  add w11, w11, w12\n  add w10, w10, #1\n  b inner\nnext:\n  add w9, w9, #1\n  b outer\ndone:\n  mov w0, w11\n  ret"
	rowsVerdict := verifyCase(t, rows, oakRows, asmRows)
	if rowsVerdict.Kind != VerdictProven {
		t.Fatalf("row sums must be proven, got %s: %s", rowsVerdict.Kind, rowsVerdict.Message)
	}
	// A single Oak loop against nested asm loops: the shapes differ — trusted.
	flat := verifyCase(t, decl, "{\n  acc: u32 = u32(0)\n  i: u32 = u32(0)\n  while i < n {\n    acc = acc + m\n    i = i + u32(1)\n  }\n  acc\n}", asmGrid)
	if flat.Kind != VerdictTrusted || !strings.Contains(flat.Message, "data-dependent loops") {
		t.Fatalf("differing loop counts must be trusted, got %s: %s", flat.Kind, flat.Message)
	}
}

// A loop guarded by a conjunction (`len(v) >= 4 && i <= len(v) - 4`, the
// vector kernels' idiom) lowers to two exit tests at the header with a
// `sub` between them; the loop's continue condition is that neither exit
// is taken (docs/spec/94-assembler.md §8, the vector increment).
func TestVerifyConjunctiveExitLoop(t *testing.T) {
	decl := "strided: (v: []u32) -> u32"
	oak := "{\n  acc: u32 = u32(0)\n  i: u32 = u32(0)\n  while len(v) >= u32(4) && i <= len(v) - u32(4) {\n    acc = acc + v[i]\n    i = i + u32(4)\n  }\n  acc\n}"
	walk := `  bind x0, w1 = v
  clobber w9, w10, w11, w12
  mov w9, #0
  mov w10, #0
loop:
  cmp w1, #4
  b.lo done
  sub w12, w1, #4
  cmp w9, w12
  b.hi done
  ldr w11, [x0, w9, uxtw #2]
  add w10, w10, w11
  add w9, w9, #4
  b loop
done:
  mov w0, w10
  ret`
	verdict := verifyCase(t, decl, oak, walk)
	if verdict.Kind == VerdictTrusted || verdict.Kind == VerdictMismatch {
		t.Fatalf("the conjunctively guarded loop must be verified, got %s: %s", verdict.Kind, verdict.Message)
	}
	// Striding by eight in the asm against four in Oak: a concrete input refutes it.
	stride := verifyCase(t, decl, oak, strings.Replace(walk, "add w9, w9, #4", "add w9, w9, #8", 1))
	if stride.Kind != VerdictMismatch {
		t.Fatalf("the wrong stride must be a mismatch, got %s: %s", stride.Kind, stride.Message)
	}
}

// A vector accumulator across a data-dependent loop: the Oak lanes
// `acc[0..7]` and `acc[8..15]` are coupled as packs to the halves of the
// register that carries them, so the loop is proven, not witnessed
// (docs/spec/94-assembler.md §8, the loop increment).
func TestVerifyVectorLoopCoupling(t *testing.T) {
	decl := "anyset: (v: []u8) -> u32"
	oak := "{\n  acc: simd.U8x16 = simd.splat_u8x16(u8(0))\n  i: u32 = u32(0)\n  while len(v) >= u32(16) && i <= len(v) - u32(16) {\n    acc = simd.or_u8x16(acc, simd.load_u8x16(v, i))\n    i = i + u32(16)\n  }\n  simd.any_u8x16(acc) ? u32(1) | u32(0)\n}"
	walk := `  bind x0, w1 = v
  clobber w9, w10, w12, v16, v17
  movi v16.16b, #0
  mov w9, #0
loop:
  cmp w1, #16
  b.lo done
  sub w12, w1, #16
  cmp w9, w12
  b.hi done
  ldr q17, [x0, w9, uxtw]
  orr v16.16b, v16.16b, v17.16b
  add w9, w9, #16
  b loop
done:
  umaxv b16, v16.16b
  umov w10, v16.b[0]
  cmp w10, #0
  cset w0, ne
  ret`
	verdict := verifyCase(t, decl, oak, walk)
	if verdict.Kind != VerdictProven || !strings.Contains(verdict.Message, "acc[0..7]↔v16.lo") {
		t.Fatalf("the vector accumulator loop must be proven with its lanes coupled, got %s: %s", verdict.Kind, verdict.Message)
	}
	// Accumulating with and instead of or: refuted on a concrete input.
	wrong := verifyCase(t, decl, oak, strings.Replace(walk, "orr v16.16b", "and v16.16b", 1))
	if wrong.Kind != VerdictMismatch {
		t.Fatalf("the wrong accumulation must be a mismatch, got %s: %s", wrong.Kind, wrong.Message)
	}
}

// A byte copy into a frame array at a data-dependent index (the UTF-8
// kernel's tail): under the checker's index guard the store names sixteen
// possible slots, each taking the value when the index selects it, so the
// array is loop-carried memory and its lanes couple to the slots — single
// byte slots when the array was zeroed byte by byte, packed into the two
// words when it was zeroed as a pair (docs/spec/94-assembler.md §8).
func TestVerifyFrameArrayLoop(t *testing.T) {
	decl := "tailcopy: (v: []u8) -> u32"
	oak := "{\n  tail: [16]u8 = [u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0), u8(0)]\n  i: u32 = u32(0)\n  while i < len(v) && i < u32(16) {\n    tail[i] = v[i]\n    i = i + u32(1)\n  }\n  u32(tail[3])\n}"
	body := func(init string) string {
		return "  bind x0, w1 = v\n  clobber w9, w10, w11, x12, v16\n  frame 16\n  sub sp, sp, #16\n" + init + `  mov w9, #0
loop:
  cmp w9, #16
  b.hs done
  cmp w9, w1
  b.hs done
  ldrb w10, [x0, w9, uxtw]
  add x12, sp, #0
  cmp w9, #16
  b.hs trap
  strb w10, [x12, w9, uxtw]
  add w9, w9, #1
  b loop
done:
  ldr q16, [sp]
  add sp, sp, #16
  umov w0, v16.b[3]
  ret
trap:
  brk #1`
	}
	var bytes strings.Builder
	for k := 0; k < 16; k++ {
		fmt.Fprintf(&bytes, "  strb wzr, [sp, #%d]\n", k)
	}
	for name, init := range map[string]string{"byte slots": bytes.String(), "word slots": "  stp xzr, xzr, [sp]\n"} {
		verdict := verifyCase(t, decl, oak, body(init))
		if verdict.Kind != VerdictProven {
			t.Fatalf("%s: the tail copy must be proven, got %s: %s", name, verdict.Kind, verdict.Message)
		}
		// Storing every byte at index 0 instead: refuted on a concrete input.
		wrong := verifyCase(t, decl, oak, strings.Replace(body(init), "strb w10, [x12, w9, uxtw]", "strb w10, [x12]", 1))
		if wrong.Kind != VerdictMismatch {
			t.Fatalf("%s: the wrong index must be a mismatch, got %s: %s", name, wrong.Kind, wrong.Message)
		}
	}
}
