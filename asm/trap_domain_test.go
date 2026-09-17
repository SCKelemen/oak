package asm

import (
	"strings"
	"testing"
)

// A guard outside the concrete witness set must not disappear from a
// universal proof merely because the remaining paths return the right value.
func TestVerifyTrapDomainOutsideWitnesses(t *testing.T) {
	v := verifyCase(t, "rare: (b: u32) -> u32", "b",
		"  bind w0 = b\n  cmp w0, #1234\n  b.eq trap\n  ret\ntrap:\n  brk #1")
	if v.Kind != VerdictWitnessed || !strings.Contains(v.Message, "trap-domain obligation is not proven") {
		t.Fatalf("an extra machine trap at b=1234 must fail its trap-domain obligation: %s: %s", v.Kind, v.Message)
	}
}

func TestVerifyTrapDomainSymbolic(t *testing.T) {
	guard := "  bind w0 = b\n  cmp w0, #1234\n  b.eq trap\n  ret\ntrap:\n  brk #1"
	for _, test := range []struct {
		name, source string
		want         VerdictKind
	}{
		{"same_assert", "{\n assert(b != u32(1234))\n b\n}", VerdictProven},
		{"unrelated_assert", "{\n assert(b != u32(0))\n b\n}", VerdictWitnessed},
		{"unsupported_assert", "{\n assert(unknown_predicate(b))\n b\n}", VerdictWitnessed},
	} {
		t.Run(test.name, func(t *testing.T) {
			v := verifyCase(t, "rare: (b: u32) -> u32", test.source, guard)
			if v.Kind != test.want {
				t.Fatalf("want %s, got %s: %s", test.want, v.Kind, v.Message)
			}
		})
	}
	// An assertion on the other source arm cannot justify the machine's
	// unconditional exclusion. No small concrete witness reaches b=1234.
	source := "a < u32(10) ? {\n assert(b != u32(1234))\n b\n} | b"
	wrong := "  bind w0 = a\n  bind w1 = b\n  cmp w1, #1234\n  b.eq trap\n  mov w0, w1\n  ret\ntrap:\n  brk #1"
	correct := strings.Replace(wrong, "  cmp w1, #1234", "  cmp w0, #10\n  b.hs done\n  cmp w1, #1234", 1)
	correct = strings.Replace(correct, "  mov w0, w1", "done:\n  mov w0, w1", 1)
	for _, test := range []struct {
		name, machine string
		want          VerdictKind
	}{{"wrong_arm", wrong, VerdictWitnessed}, {"matching_arm", correct, VerdictProven}} {
		t.Run(test.name, func(t *testing.T) {
			v := verifyCase(t, "nested: (a, b: u32) -> u32", source, test.machine)
			if v.Kind != test.want {
				t.Fatalf("want %s, got %s: %s", test.want, v.Kind, v.Message)
			}
		})
	}
}

func TestVerifyTrapDomainMemoryAndVector(t *testing.T) {
	for _, test := range []struct {
		name, declaration, source, machine string
	}{
		{"read", "peek: (v: []u32, i: u32) -> u32", "v[i]",
			"  bind x0, w1 = v\n  bind w2 = i\n  cmp w2, #1234\n  b.eq trap\n  cmp w2, w1\n  b.hs trap\n  ldr w0, [x0, w2, uxtw #2]\n  ret\ntrap:\n  brk #1"},
		{"write", "set: (v: [*]u32, i: u32, x: u32) -> ()", "{\n v[i] = x\n}",
			"  bind x0, w1 = v\n  bind w2 = i\n  bind w3 = x\n  cmp w2, #1234\n  b.eq trap\n  cmp w2, w1\n  b.hs trap\n  str w3, [x0, w2, uxtw #2]\n  ret\ntrap:\n  brk #1"},
		{"vector", "keep: (v: simd.U8x16, i: u32) -> simd.U8x16", "v",
			"  bind v0 = v\n  bind w0 = i\n  cmp w0, #1234\n  b.eq trap\n  ret\ntrap:\n  brk #1"},
	} {
		t.Run(test.name, func(t *testing.T) {
			v := verifyCase(t, test.declaration, test.source, test.machine)
			if v.Kind != VerdictWitnessed || !strings.Contains(v.Message, "trap-domain obligation is not proven") {
				t.Fatalf("an extra trap must not bypass admission via %s: %s: %s", test.name, v.Kind, v.Message)
			}
			if test.name != "vector" {
				machine := strings.Replace(test.machine, "  cmp w2, #1234\n  b.eq trap\n", "", 1)
				v := verifyCase(t, test.declaration, test.source, machine)
				if v.Kind != VerdictProven {
					t.Fatalf("matching bounds must still prove: %s: %s", v.Kind, v.Message)
				}
			}
		})
	}
}

// The source trap predicate must use a mathematical end index, not a
// wrapping u32 addition. Check both the symbolic collector and witnesses.
func TestTrapDomainVectorBoundsDoNotWrap(t *testing.T) {
	sig, err := parseSignatureWithBody("read: (v: []u8, i: u32) -> simd.U8x16 = simd.load_u8x16(v, i)")
	if err != nil {
		t.Fatal(err)
	}
	for _, concrete := range []bool{false, true} {
		for _, test := range []struct {
			index uint64
			trap  bool
		}{{0, false}, {48, false}, {49, true}, {0xfffffff0, true}, {0xffffffff, true}} {
			env := map[string]uint64{spanLenName("v"): 64, "i": test.index}
			var input map[string]uint64
			if concrete {
				input = env
			}
			lo := prepareLowering(&Function{Arch: "arm64"}, sig, input)
			lo.trapDomainTracked = true
			typ, ok := lo.oakTypeOf(sig.ReturnType)
			if !ok {
				t.Fatal("missing vector type")
			}
			_, reason, lowered := lo.aggregateValue(sig.Body, typ)
			trapped := lo.witnessTrapped
			for _, trap := range lo.traps {
				trapped = trapped || trap.eval(env)&1 != 0
			}
			if trapped != test.trap || (!lowered && !(concrete && test.trap)) {
				t.Fatalf("concrete=%v i=%d: trap=%v want %v, lowered=%v (%s)", concrete, test.index, trapped, test.trap, lowered, reason)
			}
		}
	}
}

// The machine's trap paths leave the value/effect domain only after an
// independent symbolic obligation. Witnesses remain an early refutation
// (machineTrapsWhereOakYields): an asm that traps on b = 0 against an Oak
// body returning 7 there is a mismatch — the machine traps where Oak
// yields a value — while against an Oak body asserting b != 0 it is
// proven, the two differing only where both trap; the same asm without
// the trap is a mismatch against either.
func TestVerifyTrapDomain(t *testing.T) {
	trapping := "  bind w0 = a\n  bind w1 = b\n  cbz w1, trap\n  ret\ntrap:\n  brk #1"
	yields := verifyCase(t, "pick: (a, b: u32) -> u32", "b == u32(0) ? u32(7) | a", trapping)
	if yields.Kind != VerdictMismatch || !strings.Contains(yields.Message, "traps where Oak yields") {
		t.Errorf("the machine trapping where the Oak body yields a value must be a mismatch, got %s: %s", yields.Kind, yields.Message)
	}
	asserting := "{\n  assert(b != u32(0))\n  a\n}"
	agreeing := verifyCase(t, "pick: (a, b: u32) -> u32", asserting, trapping)
	if agreeing.Kind != VerdictProven {
		t.Errorf("a difference only where both sides trap must not be a mismatch, got %s: %s", agreeing.Kind, agreeing.Message)
	}
	unguarded := verifyCase(t, "pick: (a, b: u32) -> u32", "b == u32(0) ? u32(7) | a",
		"  bind w0 = a\n  bind w1 = b\n  ret")
	if unguarded.Kind != VerdictMismatch {
		t.Errorf("without the trap the difference at b = 0 is a mismatch, got %s: %s", unguarded.Kind, unguarded.Message)
	}
	// A trap on one arm of a nested fork excludes exactly that arm's
	// inputs, where the Oak arm asserts the same.
	nestedOak := "a < u32(10) ? {\n  assert(b != u32(0))\n  a\n} | {\n  b\n}"
	nested := verifyCase(t, "pick2: (a, b: u32) -> u32", nestedOak,
		"  bind w0 = a\n  bind w1 = b\n  cmp w0, #10\n  b.hs other\n  cbz w1, trap\n  ret\nother:\n  mov w0, w1\n  ret\ntrap:\n  brk #1")
	if nested.Kind != VerdictProven {
		t.Errorf("a nested trap arm must leave only its inputs, got %s: %s", nested.Kind, nested.Message)
	}
	// The guard's inputs stay in the domain on the other arm: b = 0 with
	// a >= 10 returns b on both sides; returning a there is a mismatch.
	wrongArm := verifyCase(t, "pick2: (a, b: u32) -> u32", nestedOak,
		"  bind w0 = a\n  bind w1 = b\n  cmp w0, #10\n  b.hs other\n  cbz w1, trap\n  ret\nother:\n  ret\ntrap:\n  brk #1")
	if wrongArm.Kind != VerdictMismatch {
		t.Errorf("the other arm's inputs stay in the domain, got %s: %s", wrongArm.Kind, wrongArm.Message)
	}
	// An arm speculated by the backend whose guard traps on the inputs
	// of the other arm (a shift count from the other arm's arithmetic):
	// the machine traps where the Oak body, taking the other arm, yields.
	speculated := verifyCase(t, "place: (b: u32, k: u32) -> u32", "k < u32(8) ? b << (k * u32(4)) | b >> ((k - u32(8)) * u32(4))",
		"  bind w0 = b\n  bind w1 = k\n  clobber x9, x10, x11\n  lsl w9, w1, #2\n  cmp w9, #32\n  b.hs trap\n  lsl w10, w0, w9\n  sub w9, w1, #8\n  lsl w9, w9, #2\n  cmp w9, #32\n  b.hs trap\n  lsr w11, w0, w9\n  cmp w1, #8\n  csel w0, w10, w11, lo\n  ret\ntrap:\n  brk #1")
	if speculated.Kind != VerdictMismatch || !strings.Contains(speculated.Message, "traps where Oak yields") {
		t.Errorf("a speculated arm whose guard traps must be a mismatch, got %s: %s", speculated.Kind, speculated.Message)
	}
}

// ldapr, the RCpc acquire load the Apple cores' compilers emit, reads the
// element as ldar does.
func TestVerifyAcquireLoadRCpc(t *testing.T) {
	v := verifyCase(t, "peek: (v: [*]Atomic[u32], i: u32) -> u32", "atomic_load_acquire(v[i])",
		"  bind x0, w1 = v\n  bind w2 = i\n  clobber x8\n  cmp w2, w1\n  b.hs trap\n  add x8, x0, w2, uxtw #2\n  ldapr w0, [x8]\n  ret\ntrap:\n  brk #1")
	if v.Kind != VerdictProven {
		t.Errorf("an ldapr of a cell must be proven against the atomic load, got %s: %s", v.Kind, v.Message)
	}
	if !strings.Contains(v.Message, "peek") {
		t.Errorf("the verdict names the unit: %s", v.Message)
	}
}
