package asm

import "fmt"

type rv64PCRelPatch struct{ upper, lower uint32 }

// rv64PCRelPair admits exactly the call and address pairs emitted by Oak.
// Keeping both fixed fields and register identities is essential: patching
// arbitrary U/I words does not establish that the pair reaches the symbol.
func rv64PCRelPair(kind string, upper, lower uint32) bool {
	if upper&0x7f != 0x17 { // AUIPC
		return false
	}
	rd := upper >> 7 & 31
	if rd == 0 || lower>>15&31 != rd || lower>>7&31 != rd {
		return false
	}
	switch kind {
	case "riscv_call_plt":
		return rd == 1 && lower&0x707f == 0x67 // JALR ra, imm(ra)
	case "riscv_pcrel":
		return lower&0x707f == 0x13 // ADDI rd, rd, imm
	}
	return false
}

// patchRV64PCRel uses the RV64 (not RV32) signed AUIPC semantics. Its exact
// displacement interval is [-2^31-2^11, 2^31-2^11-1]: rounding the upper
// immediate can overflow even when the displacement fits a signed 32-bit int.
// Addresses must not wrap. IALIGN=16 is admitted here; the image's C flag and
// function layout determine whether a particular executable admits RVC.
func patchRV64PCRel(kind string, upper, lower uint32, place, target uint64) (rv64PCRelPatch, error) {
	if !rv64PCRelPair(kind, upper, lower) {
		return rv64PCRelPatch{}, fmt.Errorf("RV64 %s: invalid AUIPC pair %#08x/%#08x", kind, upper, lower)
	}
	if place&1 != 0 || place > ^uint64(0)-7 || (kind == "riscv_call_plt" && target&1 != 0) {
		return rv64PCRelPatch{}, fmt.Errorf("RV64 %s: invalid pair or target alignment/address", kind)
	}
	var delta int64
	if target >= place {
		distance := target - place
		if distance > (1<<31)-(1<<11)-1 {
			return rv64PCRelPatch{}, fmt.Errorf("RV64 %s: target exceeds positive AUIPC reach", kind)
		}
		delta = int64(distance)
	} else {
		distance := place - target
		if distance > (1<<31)+(1<<11) {
			return rv64PCRelPatch{}, fmt.Errorf("RV64 %s: target exceeds negative AUIPC reach", kind)
		}
		delta = -int64(distance)
	}
	hi := (delta + 0x800) >> 12
	lo := delta - (hi << 12)
	patch := rv64PCRelPatch{
		upper: upper&0xfff | uint32(hi&0xfffff)<<12,
		lower: lower&0xfffff | uint32(lo&0xfff)<<20,
	}
	if reached, ok := decodeRV64PCRelTarget(kind, patch.upper, patch.lower, place); !ok || reached != target {
		return rv64PCRelPatch{}, fmt.Errorf("RV64 %s: patched pair does not reach target %#x", kind, target)
	}
	return patch, nil
}

// Decode the instruction fields independently of the split/patch arithmetic.
func decodeRV64PCRelTarget(kind string, upper, lower uint32, place uint64) (uint64, bool) {
	if !rv64PCRelPair(kind, upper, lower) || place&1 != 0 || place > ^uint64(0)-7 {
		return 0, false
	}
	delta := int64(int32(upper&0xfffff000)) + int64(int32(lower)>>20)
	var target uint64
	if delta >= 0 {
		if place > ^uint64(0)-uint64(delta) {
			return 0, false
		}
		target = place + uint64(delta)
	} else {
		if uint64(-delta) > place {
			return 0, false
		}
		target = place - uint64(-delta)
	}
	if kind == "riscv_call_plt" {
		target &^= 1 // Architectural JALR clears bit zero.
	}
	return target, true
}
