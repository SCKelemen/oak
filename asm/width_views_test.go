package asm

import (
	"fmt"
	"testing"
)

func TestZeroExtendPreservesTruncatedParameter(t *testing.T) {
	for _, narrow := range []int{1, 8, 16, 32} {
		t.Run(fmt.Sprint(narrow), func(t *testing.T) {
			input := paramTerm("value", 64)
			view := truncate(input, narrow)
			wide := zeroExtend(view, 64)
			if wide.kind != termBinary || wide.op != "and" || wide.left != view || view.declaredWidth() != 64 {
				t.Fatalf("lost the mask or original input provenance: %s", wide)
			}
			for _, value := range []uint64{0, 1, mask(narrow), 1 << narrow, 1<<63 | 3, ^uint64(0), ^uint64(1)} {
				env := map[string]uint64{"value": value}
				want := value & mask(narrow)
				for _, term := range []*term{wide, canonical(wide), zeroExtend(truncate(wide, narrow), 64)} {
					if got := term.eval(env); got != want {
						t.Fatalf("width %d, input %#x: %s = %#x, want %#x", narrow, value, term, got, want)
					}
				}
				for _, signed := range []bool{false, true} {
					wantExtended := want
					if signed && want&(1<<(narrow-1)) != 0 {
						wantExtended |= ^mask(narrow)
					}
					if got := extendTerm(view, narrow, 64, signed).eval(env); got != wantExtended {
						t.Fatalf("fused explicit extension: width %d, signed %v, input %#x: got %#x, want %#x", narrow, signed, value, got, wantExtended)
					}
				}
			}
		})
	}
	// An originally narrow parameter remains bounded by its input contract;
	// its widening need not add a mask or invent a new input declaration.
	for _, width := range []int{1, 8, 16, 32} {
		wide := zeroExtend(paramTerm("narrow", width), 64)
		if wide.kind != termParam || wide.width != 64 || wide.declaredWidth() != width {
			t.Fatalf("changed narrow parameter provenance: %s", wide)
		}
	}
}

func TestVerifyWWriteRetainsParameterTruncation(t *testing.T) {
	for _, body := range []string{
		"bind x0 = value\nmov w0, w0\nret",
		"bind x0 = value\nframe 16\nsub sp, sp, #16\nstr w0, [sp]\nldr w0, [sp]\nadd sp, sp, #16\nret",
	} {
		decl := "narrow: (value: u64) -> u64"
		if got := verifyCase(t, decl, "u64(u32(value))", body); got.Kind != VerdictProven {
			t.Fatalf("W write must prove zero-extension: %s: %s", got.Kind, got.Message)
		}
		// Previously both sequences could falsely prove identity by recovering
		// the original input's high bits during the symbolic W-register write.
		if got := verifyCase(t, decl, "value", body); got.Kind != VerdictMismatch {
			t.Fatalf("W write must refute identity: %s: %s", got.Kind, got.Message)
		}
	}
}
