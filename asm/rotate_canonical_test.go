package asm

import (
	"fmt"
	"strings"
	"testing"
)

func TestCanonicalConstantRotate(t *testing.T) {
	for _, width := range []int{32, 64} {
		x := paramTerm("x", width)
		for count := 1; count < width; count++ {
			original := binaryTerm("ror", x, constTerm(uint64(count), width))
			want := binaryTerm("or", binaryTerm("shr", x, constTerm(uint64(count), width)), binaryTerm("shl", x, constTerm(uint64(width-count), width)))
			got := canonical(original)
			if !equalTerms(got, want) {
				t.Fatalf("width %d count %d: got %s, want %s", width, count, got, want)
			}
			values := []uint64{0, 1, 2, 3, mask(width), mask(width) >> 1, uint64(1) << (width - 1), 0x0123456789abcdef, 0xfedcba9876543210}
			for bit := 0; bit < width; bit++ {
				values = append(values, uint64(1)<<bit)
			}
			for _, value := range values {
				env := map[string]uint64{"x": value}
				if got.eval(env) != original.eval(env) {
					t.Fatalf("width %d count %d x=%#x: rewrite changed evaluation", width, count, value)
				}
			}
		}
	}
}

func TestCanonicalRotateGuard(t *testing.T) {
	for _, width := range []int{32, 64} {
		x := paramTerm("x", width)
		// Zero and wrapped counts are normalized by canonicalBitwise's
		// separate modulo-width laws; these shapes remain unsupported.
		for _, count := range []*term{paramTerm("count", width), constTerm(7, width/2)} {
			original := binaryTerm("ror", x, count)
			if got := canonical(original); !equalTerms(got, original) {
				t.Fatalf("width %d unsupported count %s:%d changed to %s", width, count, count.width, got)
			}
		}
	}
	for _, width := range []int{8, 16} {
		original := binaryTerm("ror", paramTerm("x", width), constTerm(3, width))
		if got := canonical(original); !equalTerms(got, original) {
			t.Fatalf("unsupported width %d changed", width)
		}
	}
	// A node with a wider child is not silently changed into a rotate
	// of that wider value. Canonicalization must retain its operation width.
	original := &term{kind: termBinary, op: "ror", width: 32, left: paramTerm("x", 64), right: constTerm(7, 32)}
	if got := canonical(original); !equalTerms(got, original) {
		t.Fatalf("mixed-width rotate changed to %s", got)
	}
}

func TestCanonicalRotateRejectsNearMisses(t *testing.T) {
	x, y := paramTerm("x", 32), paramTerm("y", 32)
	rotate := canonical(binaryTerm("ror", x, constTerm(7, 32)))
	for name, wrong := range map[string]*term{
		"wrong complementary count": binaryTerm("or", binaryTerm("shr", x, constTerm(7, 32)), binaryTerm("shl", x, constTerm(24, 32))),
		"different source":          binaryTerm("or", binaryTerm("shr", x, constTerm(7, 32)), binaryTerm("shl", y, constTerm(25, 32))),
		"arithmetic right shift":    binaryTerm("or", binaryTerm("sar", x, constTerm(7, 32)), binaryTerm("shl", x, constTerm(25, 32))),
	} {
		if termEquivalent(rotate, canonical(wrong), 32, map[[3]any]bool{}) {
			t.Errorf("%s must not be structurally equivalent", name)
		}
	}
	wide := paramTerm("wide", 64)
	before := canonical(binaryTerm("ror", truncate(wide, 32), constTerm(7, 32)))
	after := canonical(truncate(binaryTerm("ror", wide, constTerm(7, 64)), 32))
	if termEquivalent(before, after, 32, map[[3]any]bool{}) {
		t.Fatal("truncation before and after rotation must not be structurally equivalent")
	}
	if before.eval(map[string]uint64{"wide": 1}) == after.eval(map[string]uint64{"wide": 1}) {
		t.Fatal("truncation regression fixture must distinguish the two operations")
	}
}

// Each round is BLAKE3's integer add/xor/rotate quarter round. The source
// keeps its two-shift spelling and is parsed/lowered independently of the
// machine instructions; this is not a comparison with expected constants.
func TestVerifyRotateQuarterRoundsStructurally(t *testing.T) {
	for _, rounds := range []int{1, 7} {
		t.Run(fmt.Sprint(rounds), func(t *testing.T) {
			decl, oak, machine := rotateQuarterRoundFixture(rounds)
			verdict := verifyCase(t, decl, oak, machine)
			if verdict.Kind != VerdictProven || !strings.Contains(verdict.Message, "the same term on both sides") {
				t.Fatalf("%d quarter rounds must prove structurally, got %s: %s", rounds, verdict.Kind, verdict.Message)
			}
			wrong := strings.Replace(machine, "ror w3, w3, #16", "ror w3, w3, #15", 1)
			if verdict := verifyCase(t, decl, oak, wrong); verdict.Kind != VerdictMismatch {
				t.Fatalf("wrong rotation must be refuted, got %s: %s", verdict.Kind, verdict.Message)
			}
		})
	}
}

func rotateQuarterRoundFixture(rounds int) (decl, oakBody, asmBody string) {
	decl = "quarter: (a0, b0, c0, d0, mx, my: u32) -> u32"
	var oak, machine strings.Builder
	oak.WriteString("{\n a: u32 = a0\n b: u32 = b0\n c: u32 = c0\n d: u32 = d0\n")
	machine.WriteString(" bind w0 = a0\n bind w1 = b0\n bind w2 = c0\n bind w3 = d0\n bind w4 = mx\n bind w5 = my\n")
	for round := 0; round < rounds; round++ {
		for half, counts := range [][2]int{{16, 12}, {8, 7}} {
			message := []string{"mx", "my"}[half]
			fmt.Fprintf(&oak, " a = a + b + %s\n d = ((d ^ a) >> u32(%d)) | ((d ^ a) << u32(%d))\n c = c + d\n b = ((b ^ c) >> u32(%d)) | ((b ^ c) << u32(%d))\n", message, counts[0], 32-counts[0], counts[1], 32-counts[1])
			fmt.Fprintf(&machine, " add w0, w0, w1\n add w0, w0, w%d\n eor w3, w3, w0\n ror w3, w3, #%d\n add w2, w2, w3\n eor w1, w1, w2\n ror w1, w1, #%d\n", 4+half, counts[0], counts[1])
		}
	}
	oak.WriteString(" a ^ b ^ c ^ d\n}")
	machine.WriteString(" eor w0, w0, w1\n eor w0, w0, w2\n eor w0, w0, w3\n ret")
	return decl, oak.String(), machine.String()
}

func BenchmarkVerifyRotateQuarterRounds(b *testing.B) {
	b.Setenv("OAK_VERIFY_BUDGET", "base")
	for _, rounds := range []int{1, 7} {
		b.Run(fmt.Sprint(rounds), func(b *testing.B) {
			decl, oak, machine := rotateQuarterRoundFixture(rounds)
			unit, errors := ParseUnit("quarter.oakasm", decl+" = {\n"+machine+"\n}\n")
			if len(errors) != 0 {
				b.Fatal(errors)
			}
			sig, err := parseSignature(decl)
			if err != nil {
				b.Fatal(err)
			}
			if findings := Check(unit.Functions[0], sig, nil); len(findings) != 0 {
				b.Fatal(findings)
			}
			source, err := parseSignatureWithBody(decl + " = " + oak)
			if err != nil {
				b.Fatal(err)
			}
			var verdict Verdict
			b.ReportAllocs()
			b.ResetTimer()
			for i := 0; i < b.N; i++ {
				verdict = Verify(unit.Functions[0], sig, source.Body)
			}
			b.StopTimer()
			b.Logf("verdict: %s", verdict.Kind)
		})
	}
}
