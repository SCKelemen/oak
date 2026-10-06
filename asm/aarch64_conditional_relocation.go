package asm

import "fmt"

const aarch64CondBranch19ImmediateMask = uint32(0x00ffffe0)

func aarch64ConditionalBranchMnemonic(mnemonic string) bool {
	return mnemonic == "b." || mnemonic == "cbz" || mnemonic == "cbnz"
}

// Only ordinary B.cond and the W/X forms of CBZ/CBNZ admit CONDBR19.
// In particular, BC.cond (bit 4), literal loads, and other branch families
// cannot acquire a conditional-branch relocation by sharing an immediate.
func aarch64CondBranch19OpcodeMatches(word uint32) bool {
	return word&0xff000010 == 0x54000000 || word&0x7e000000 == 0x34000000
}

// patchAArch64CondBranch19 is pure: callers write only after all checks pass.
// Unsigned magnitude subtraction prevents distant addresses from wrapping
// into the signed 21-bit byte interval. The immediate alone is replaced.
func patchAArch64CondBranch19(original uint32, place, target uint64) (uint32, error) {
	if !aarch64CondBranch19OpcodeMatches(original) {
		return 0, fmt.Errorf("AArch64 condbr19: word %#08x is not B.cond, CBZ, or CBNZ", original)
	}
	if place&3 != 0 || target&3 != 0 {
		return 0, fmt.Errorf("AArch64 condbr19: place %#x and target %#x must be four-byte aligned", place, target)
	}
	var encoded uint64
	if target >= place {
		bytes := target - place
		if bytes > (1<<20)-4 {
			return 0, fmt.Errorf("AArch64 condbr19: target %#x exceeds positive reach from %#x", target, place)
		}
		encoded = bytes >> 2
	} else {
		bytes := place - target
		if bytes > 1<<20 {
			return 0, fmt.Errorf("AArch64 condbr19: target %#x exceeds negative reach from %#x", target, place)
		}
		encoded = (1 << 19) - (bytes >> 2)
	}
	patched := original&^aarch64CondBranch19ImmediateMask | uint32(encoded)<<5
	if reached, ok := decodePatchedAArch64CondBranch19Target(patched, place); !ok || reached != target {
		return 0, fmt.Errorf("AArch64 condbr19: decoded target %#x, want %#x", reached, target)
	}
	return patched, nil
}

// Decode from the word independently of the magnitude-based field builder.
func decodePatchedAArch64CondBranch19Target(word uint32, place uint64) (uint64, bool) {
	if !aarch64CondBranch19OpcodeMatches(word) || place&3 != 0 {
		return 0, false
	}
	delta := int64(int32(word<<8)>>13) * 4
	if delta >= 0 {
		if place > ^uint64(0)-uint64(delta) {
			return 0, false
		}
		return place + uint64(delta), true
	}
	if uint64(-delta) > place {
		return 0, false
	}
	return place - uint64(-delta), true
}
