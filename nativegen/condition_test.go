package nativegen

import (
	"testing"

	"github.com/SCKelemen/oak/asm"
)

func TestUnsignedOneBranch(t *testing.T) {
	for _, test := range []struct {
		name     string
		left     asm.Operand
		right    asm.Operand
		code     string
		mnemonic string
		ok       bool
	}{
		{"w lo", wr(1), asm.Immediate{Value: 1}, "lo", "cbz", true},
		{"x hs", xr(2), asm.Immediate{Value: 1}, "hs", "cbnz", true},
		{"signed", wr(1), asm.Immediate{Value: 1}, "lt", "", false},
		{"other immediate", wr(1), asm.Immediate{Value: 2}, "lo", "", false},
		{"shifted immediate", wr(1), asm.Immediate{Value: 1, Shift: 12}, "lo", "", false},
		{"zero register", wr(31), asm.Immediate{Value: 1}, "lo", "", false},
		{"non-register left", asm.Immediate{Value: 0}, asm.Immediate{Value: 1}, "lo", "", false},
	} {
		t.Run(test.name, func(t *testing.T) {
			mnemonic, register, ok := unsignedOneBranch(test.left, test.right, test.code)
			if ok != test.ok || mnemonic != test.mnemonic {
				t.Fatalf("unsignedOneBranch = (%q, %#v, %v), want mnemonic %q, ok %v",
					mnemonic, register, ok, test.mnemonic, test.ok)
			}
			if ok && register != test.left {
				t.Fatalf("tested register = %#v, want %#v", register, test.left)
			}
		})
	}
}
