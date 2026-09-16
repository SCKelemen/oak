package asm

import "fmt"

const (
	aarch64Branch26OpcodeMask = uint32(0xfc000000)
	aarch64Branch26Immediate  = uint32(0x03ffffff)
	aarch64Branch26Sign       = uint32(0x02000000)
	aarch64BOpcode            = uint32(0x14000000)
	aarch64BLOpcode           = uint32(0x94000000)
	aarch64ADRPOpcodeMask     = uint32(0x9f000000)
	aarch64ADRPOpcode         = uint32(0x90000000)
	aarch64ADDXImmShift0Mask  = uint32(0xffc00000)
	aarch64ADDXImmShift0      = uint32(0x91000000)
	aarch64ADRPImmediateMask  = uint32(0x60ffffe0)
	aarch64ADDImm12Mask       = uint32(0x003ffc00)
)

type aarch64ADRL21Patch struct {
	adrp uint32
	add  uint32
}

// patchAArch64ADRL21 resolves the two-word
//
//	adrp xD, page(symbol)
//	add  xD, xD, #lo12(symbol)
//
// relocation used by the executable writer. It validates the complete pair,
// computes its page displacement without narrowing uint64 addresses to int64,
// and independently decodes the candidate before returning it. The caller can
// therefore preserve both original words on every refusal.
func patchAArch64ADRL21(adrp, add uint32, place, target uint64) (aarch64ADRL21Patch, error) {
	var result aarch64ADRL21Patch
	if place&3 != 0 {
		return result, fmt.Errorf("AArch64 adrl21: instruction place %#x must be four-byte aligned", place)
	}
	if place > ^uint64(0)-7 {
		return result, fmt.Errorf("AArch64 adrl21: two-instruction pair at %#x exceeds the address space", place)
	}
	if adrp&aarch64ADRPOpcodeMask != aarch64ADRPOpcode {
		return result, fmt.Errorf("AArch64 adrl21: first word %#08x is not ADRP", adrp)
	}
	if add&aarch64ADDXImmShift0Mask != aarch64ADDXImmShift0 {
		return result, fmt.Errorf("AArch64 adrl21: second word %#08x is not 64-bit ADD immediate with LSL #0", add)
	}
	adrpRD := adrp & 31
	addRD := add & 31
	addRN := add >> 5 & 31
	if adrpRD == 31 || adrpRD != addRD || adrpRD != addRN {
		return result, fmt.Errorf("AArch64 adrl21: ADRP Rd=%d and ADD Rn/Rd=%d/%d do not name one non-SP register", adrpRD, addRN, addRD)
	}

	placePage := place >> 12
	targetPage := target >> 12
	var encoded uint64
	if targetPage >= placePage {
		pages := targetPage - placePage
		if pages >= 1<<20 {
			return result, fmt.Errorf("AArch64 adrl21: target %#x is beyond ADRP's positive page reach from %#x", target, place)
		}
		encoded = pages
	} else {
		pages := placePage - targetPage
		if pages > 1<<20 {
			return result, fmt.Errorf("AArch64 adrl21: target %#x is beyond ADRP's negative page reach from %#x", target, place)
		}
		encoded = 1<<21 - pages
	}

	patchedADRP := adrp&^aarch64ADRPImmediateMask |
		uint32(encoded&3)<<29 | uint32(encoded>>2&0x7ffff)<<5
	patchedADD := add&^aarch64ADDImm12Mask | uint32(target&0xfff)<<10
	if patchedADRP&^aarch64ADRPImmediateMask != adrp&^aarch64ADRPImmediateMask ||
		patchedADD&^aarch64ADDImm12Mask != add&^aarch64ADDImm12Mask {
		return result, fmt.Errorf("AArch64 adrl21: patch changed a fixed or register field")
	}
	if reached, ok := decodePatchedAArch64ADRL21Target(patchedADRP, patchedADD, place); !ok || reached != target {
		return result, fmt.Errorf("AArch64 adrl21: decoded target %#x, want %#x", reached, target)
	}
	return aarch64ADRL21Patch{adrp: patchedADRP, add: patchedADD}, nil
}

// decodePatchedAArch64ADRL21Target independently interprets the immediate
// fields of an already validated ADRP+ADD pair. It repeats the structural
// checks because it is the round-trip guard used before executable mutation.
func decodePatchedAArch64ADRL21Target(adrp, add uint32, place uint64) (uint64, bool) {
	if place&3 != 0 || adrp&aarch64ADRPOpcodeMask != aarch64ADRPOpcode ||
		add&aarch64ADDXImmShift0Mask != aarch64ADDXImmShift0 {
		return 0, false
	}
	adrpRD := adrp & 31
	if adrpRD == 31 || add&31 != adrpRD || add>>5&31 != adrpRD {
		return 0, false
	}
	encoded := uint64(adrp>>29&3) | uint64(adrp>>5&0x7ffff)<<2
	placePage := place >> 12
	var targetPage uint64
	if encoded&(1<<20) == 0 {
		if placePage > (^uint64(0)>>12)-encoded {
			return 0, false
		}
		targetPage = placePage + encoded
	} else {
		pages := 1<<21 - encoded
		if pages > placePage {
			return 0, false
		}
		targetPage = placePage - pages
	}
	return targetPage<<12 | uint64(add>>10&0xfff), true
}

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
