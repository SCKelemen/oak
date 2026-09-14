package asm

import (
	"strings"
	"testing"
)

// Atomics under the sequential model (docs/spec/65-machine-memory.md
// section 7a, asm/atomics.go): a compare-exchange on a span cell is the
// element's value and a guarded write, on the Oak side and for both of
// AArch64's spellings — the LSE `casal` and the exclusive loop, whose
// store succeeds in the sequential model so the retry is decided.
const casDecl = "cas_cell: (v: [*]Atomic[u32], i: u32, expected, desired: u32) -> u32"
const casBody = "atomic_compare_exchange_acq_rel_acquire(v[i], expected, desired)"

const casLSE = "  bind x0, w1 = v\n  bind w2 = i\n  bind w3 = expected\n  bind w4 = desired\n  clobber x8\n  cmp w2, w1\n  b.hs trap\n  add x8, x0, w2, uxtw #2\n  casal w3, w4, [x8]\n  mov w0, w3\n  ret\ntrap:\n  brk #1"

const casLoop = "  bind x0, w1 = v\n  bind w2 = i\n  bind w3 = expected\n  bind w4 = desired\n  clobber x8, x9\n  cmp w2, w1\n  b.hs trap\n  add x8, x0, w2, uxtw #2\nretry:\n  ldaxr w0, [x8]\n  cmp w0, w3\n  b.ne fail\n  stlxr w9, w4, [x8]\n  cbnz w9, retry\n  ret\nfail:\n  clrex\n  ret\ntrap:\n  brk #1"

func TestVerifyAtomicsCompareExchange(t *testing.T) {
	for name, body := range map[string]string{"lse": casLSE, "exclusive loop": casLoop} {
		v := verifyCase(t, casDecl, casBody, body)
		if v.Kind != VerdictProven || !strings.Contains(v.Message, "the span memory it writes (v)") {
			t.Errorf("%s: a compare-exchange must be proven in its result and its span, got %s: %s", name, v.Kind, v.Message)
		}
	}
	// The wrong desired value is a mismatch in the span.
	wrong := verifyCase(t, casDecl, casBody, strings.Replace(casLSE, "  casal w3, w4, [x8]", "  add w4, w4, #1\n  casal w3, w4, [x8]", 1))
	if wrong.Kind != VerdictMismatch {
		t.Errorf("a compare-exchange storing another value must be a mismatch, got %s: %s", wrong.Kind, wrong.Message)
	}
	// An unconditional store where the Oak body compares first is a mismatch.
	unguarded := verifyCase(t, casDecl, casBody, strings.Replace(casLSE, "  casal w3, w4, [x8]\n  mov w0, w3", "  ldar w0, [x8]\n  stlr w4, [x8]", 1))
	if unguarded.Kind != VerdictMismatch {
		t.Errorf("an unconditional store for a compare-exchange must be a mismatch, got %s: %s", unguarded.Kind, unguarded.Message)
	}
}

func TestVerifyAtomicsReadModifyWrite(t *testing.T) {
	decl := "bump_cell: (v: [*]Atomic[u32], i: u32, x: u32) -> u32"
	head := "  bind x0, w1 = v\n  bind w2 = i\n  bind w3 = x\n  clobber x8, x9, x10\n  cmp w2, w1\n  b.hs trap\n  add x8, x0, w2, uxtw #2\n"
	tail := "\ntrap:\n  brk #1"
	fetchAddLoop := head + "retry:\n  ldxr w0, [x8]\n  add w9, w0, w3\n  stxr w10, w9, [x8]\n  cbnz w10, retry\n  ret" + tail
	fetchAddLSE := head + "  ldaddal w3, w0, [x8]\n  ret" + tail
	exchangeLSE := head + "  swpal w3, w0, [x8]\n  ret" + tail
	for name, c := range map[string][2]string{
		"fetch-add loop": {"atomic_fetch_add_acq_rel(v[i], x)", fetchAddLoop},
		"fetch-add lse":  {"atomic_fetch_add_acq_rel(v[i], x)", fetchAddLSE},
		"exchange lse":   {"atomic_exchange_acq_rel(v[i], x)", exchangeLSE},
	} {
		v := verifyCase(t, decl, c[0], c[1])
		if v.Kind != VerdictProven || !strings.Contains(v.Message, "the span memory it writes (v)") {
			t.Errorf("%s: must be proven in its result and its span, got %s: %s", name, v.Kind, v.Message)
		}
	}
	// A store in statement position, then the load: the write is followed.
	store := verifyCase(t, "set_cell: (v: [*]Atomic[u32], i: u32, x: u32) -> u32", "{\n  atomic_store_release(v[i], x)\n  atomic_load_acquire(v[i])\n}",
		head+"  stlr w3, [x8]\n  mov w0, w3\n  ret"+tail)
	if store.Kind != VerdictProven {
		t.Errorf("an atomic store then load must be proven, got %s: %s", store.Kind, store.Message)
	}
	// An exchange whose asm stores the wrong value is a mismatch.
	wrong := verifyCase(t, decl, "atomic_exchange_acq_rel(v[i], x)", head+"  add w9, w3, #1\n  swpal w9, w0, [x8]\n  ret"+tail)
	if wrong.Kind != VerdictMismatch {
		t.Errorf("an exchange storing another value must be a mismatch, got %s: %s", wrong.Kind, wrong.Message)
	}
}
