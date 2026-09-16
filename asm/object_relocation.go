package asm

import "fmt"

const (
	aarch64Branch26OpcodeMask = uint32(0xfc000000)
	aarch64Branch26Immediate  = uint32(0x03ffffff)
	aarch64Branch26Sign       = uint32(0x02000000)
	aarch64BOpcode            = uint32(0x14000000)
	aarch64BLOpcode           = uint32(0x94000000)
)

// patchAArch64Branch26 resolves one A64 B/BL relocation. It is deliberately
// pure: the caller may write the returned word only after every structural,
// arithmetic, and round-trip check below succeeds.
func patchAArch64Branch26(kind string, original uint32, place, target uint64) (uint32, error) {
	wantOpcode := uint32(0)
	switch kind {
	case "call26":
		wantOpcode = aarch64BLOpcode
	case "jump26", "branch26":
		wantOpcode = aarch64BOpcode
	default:
		return 0, fmt.Errorf("AArch64 branch26: relocation kind %q is not a B or BL relocation", kind)
	}
	if original&aarch64Branch26OpcodeMask != wantOpcode {
		return 0, fmt.Errorf("AArch64 branch26: %s relocation has instruction %#08x, want opcode %#08x", kind, original, wantOpcode)
	}
	if place&3 != 0 || target&3 != 0 {
		return 0, fmt.Errorf("AArch64 branch26: %s place %#x and target %#x must be four-byte aligned", kind, place, target)
	}

	var encoded uint64
	if target >= place {
		bytes := target - place
		// The positive endpoint is (2^25 - 1) words.
		if bytes > (1<<27)-4 {
			return 0, fmt.Errorf("AArch64 branch26: %s target %#x is beyond the positive 26-bit reach from %#x", kind, target, place)
		}
		encoded = bytes >> 2
	} else {
		bytes := place - target
		// The negative endpoint is -2^25 words.
		if bytes > 1<<27 {
			return 0, fmt.Errorf("AArch64 branch26: %s target %#x is beyond the negative 26-bit reach from %#x", kind, target, place)
		}
		words := bytes >> 2
		encoded = (uint64(1) << 26) - words
	}

	patched := original&^aarch64Branch26Immediate |
		uint32(encoded)&aarch64Branch26Immediate
	if patched&aarch64Branch26OpcodeMask != wantOpcode ||
		patched&^aarch64Branch26Immediate != original&^aarch64Branch26Immediate {
		return 0, fmt.Errorf("AArch64 branch26: %s patch changed fixed opcode bits", kind)
	}

	// Decode independently from the candidate word and require it to reach the
	// requested target. This catches a wrong sign, scale, field, or endpoint in
	// the construction above before the executable text is mutated.
	if reached, ok := decodePatchedAArch64Branch26Target(patched, place); !ok || reached != target {
		return 0, fmt.Errorf("AArch64 branch26: %s decoded target %#x, want %#x", kind, reached, target)
	}
	return patched, nil
}

// decodePatchedAArch64Branch26Target independently decodes the target of an
// A64 B or BL word. The Boolean is false for another opcode, an unaligned
// place, or an address-space overflow/underflow.
func decodePatchedAArch64Branch26Target(word uint32, place uint64) (uint64, bool) {
	opcode := word & aarch64Branch26OpcodeMask
	if (opcode != aarch64BOpcode && opcode != aarch64BLOpcode) || place&3 != 0 {
		return 0, false
	}
	imm26 := word & aarch64Branch26Immediate
	if imm26&aarch64Branch26Sign == 0 {
		bytes := uint64(imm26) << 2
		if place > ^uint64(0)-bytes {
			return 0, false
		}
		return place + bytes, true
	}
	bytes := (uint64(1<<26) - uint64(imm26)) << 2
	if bytes > place {
		return 0, false
	}
	return place - bytes, true
}
