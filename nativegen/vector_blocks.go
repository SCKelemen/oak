package nativegen

import (
	"github.com/SCKelemen/oak/asm"
)

// Vector block loads (docs/spec/94-assembler.md §9 "Vector block loads").
// For lanes wider than a byte the lowering forms a vector load's address
// in a register (`vecAddress`), so the vectorized reduction's four loads
// read
//
//	add x10, x19, w3, uxtw #2
//	ldr q16, [x10]
//	add w10, w3, #4
//	add x9, x19, w10, uxtw #2
//	ldr q17, [x9]
//	…
//
// where one address and the immediate offsets serve every load of the
// block:
//
//	add x10, x19, w3, uxtw #2
//	ldr q16, [x10]
//	ldr q17, [x10, #16]
//	…
//
// Within one basic block, a vector load whose address is `add xA, xB, wJ,
// uxtw #s` with `wJ` either the group's index `wI` or `add wJ, wI, #k`
// reads the same span at element `wI + k`, so it is the first load's
// address at the byte offset `k << s`. The pass requires that nothing
// between the two loads writes the base, the index, or the kept address,
// and that nothing after the block reads the registers it drops — the
// dropped address and index temporaries are scratch registers the
// lowering formed for those loads alone. The offset must be a multiple of
// sixteen inside the `ldr q` immediate's range.
//
// Neither the seam checker nor the verifier needed extending: the slack
// guard that admits the first load marks a region of its bound's elements
// (`elementRegionOf`, sixteen `u32` elements is 64 bytes) and
// `regionAdmits` takes every offset inside it, while the verifier reads a
// vector load through an element address at a non-zero offset as the
// span's elements from that index (`asm/verify_vector.go` loadVector).

// vectorBlockLoad is a candidate: the load at items[at] through the
// address written at items[addrAt] by `add xA, xB, wJ, uxtw #s`, where
// wJ is the group's index plus k (its `add` at items[idxAt], or -1).
type vectorBlockLoad struct {
	at, addrAt, idxAt int
	dest              asm.Register
	addr, base, idx   int
	k, shift          int64
}

// blockVectorLoads rewrites the items of one function. The registers a
// fusion drops must be dead after the load that dropped them, which the
// whole-function liveness of the general registers answers
// (nativegen/cleanup.go liveAfter).
func blockVectorLoads(items []asm.Item) ([]asm.Item, int) {
	live := liveAfter(items)
	fused := 0
	start := 0
	var out []asm.Item
	for i := 0; i <= len(items); i++ {
		boundary := i == len(items)
		if !boundary {
			switch it := items[i].(type) {
			case asm.Label:
				boundary = true
			case asm.Instruction:
				boundary = isTransfer(it)
			}
		}
		if !boundary {
			continue
		}
		end := i
		if i < len(items) {
			if _, isLabel := items[i].(asm.Label); !isLabel {
				end = i + 1
			}
		}
		block, n := blockVectorBlock(items[start:end], live[start:end])
		fused += n
		out = append(out, block...)
		if end == i {
			if i < len(items) {
				out = append(out, items[i])
			}
			start = i + 1
		} else {
			start = end
		}
	}
	return out, fused
}

// vectorAddressOf reads `add xA, xB, wJ, uxtw #s` at items[at].
func vectorAddressOf(item asm.Item) (dest, base, idx int, shift int64, ok bool) {
	ins, isIns := item.(asm.Instruction)
	if !isIns || ins.Mnemonic != "add" || len(ins.Operands) != 3 {
		return 0, 0, 0, 0, false
	}
	d, okD := ins.Operands[0].(asm.Register)
	b, okB := ins.Operands[1].(asm.Register)
	ext, okE := ins.Operands[2].(asm.Extended)
	if !okD || !okB || !okE || d.Class != asm.ClassX || b.Class != asm.ClassX || ext.Kind != "uxtw" || ext.Reg.Class != asm.ClassW {
		return 0, 0, 0, 0, false
	}
	return d.Num, b.Num, ext.Reg.Num, ext.Amount, true
}

// indexOffsetOf reads `add wJ, wI, #k` at items[at].
func indexOffsetOf(item asm.Item) (dest, src int, k int64, ok bool) {
	ins, isIns := item.(asm.Instruction)
	if !isIns || ins.Mnemonic != "add" || len(ins.Operands) != 3 {
		return 0, 0, 0, false
	}
	d, okD := ins.Operands[0].(asm.Register)
	src2, okS := ins.Operands[1].(asm.Register)
	imm, okI := ins.Operands[2].(asm.Immediate)
	if !okD || !okS || !okI || d.Class != asm.ClassW || src2.Class != asm.ClassW || imm.Shift != 0 || imm.Value <= 0 {
		return 0, 0, 0, false
	}
	return d.Num, src2.Num, imm.Value, true
}

// wholeVectorLoad reads `ldr qD, [xA]`.
func wholeVectorLoad(item asm.Item) (dest asm.Register, addr int, ok bool) {
	ins, isIns := item.(asm.Instruction)
	if !isIns || ins.Mnemonic != "ldr" || len(ins.Operands) != 2 {
		return asm.Register{}, 0, false
	}
	d, okD := ins.Operands[0].(asm.Register)
	mem, okM := ins.Operands[1].(asm.Memory)
	if !okD || !okM || d.Class != asm.ClassV || d.Vec != "q" || mem.Index != nil || mem.Mode != asm.MemOffset || mem.Offset != 0 || mem.Base.Class != asm.ClassX {
		return asm.Register{}, 0, false
	}
	return d, mem.Base.Num, true
}

// vectorBlockCandidates lists a block's vector loads through an address
// the block formed, each with the index it reads resolved to a root index
// and a constant: the lowering may reach the index through a copy (`mov
// wJ, wI`, before the late cleanup forwards it) or an offset (`add wJ,
// wI, #k`), and the instruction that wrote it is the last one before the
// address that did.
func vectorBlockCandidates(block []asm.Item) []vectorBlockLoad {
	var out []vectorBlockLoad
	for at := 1; at < len(block); at++ {
		dest, addr, isLoad := wholeVectorLoad(block[at])
		if !isLoad {
			continue
		}
		// The address is the instruction before the load.
		d, base, idx, shift, isAddr := vectorAddressOf(block[at-1])
		if !isAddr || d != addr {
			continue
		}
		cand := vectorBlockLoad{at: at, addrAt: at - 1, idxAt: -1, dest: dest, addr: addr, base: base, idx: idx, shift: shift}
		// The index's own definition, if the block holds it: a copy or an
		// offset of the root index. Only one step — the lowering spells no
		// longer chain for an element index.
		for p := at - 2; p >= 0; p-- {
			ins, isIns := block[p].(asm.Instruction)
			if !isIns {
				break
			}
			if !writesReg(ins, cand.idx) {
				continue
			}
			if dj, src, k, isOffset := indexOffsetOf(block[p]); isOffset && dj == cand.idx {
				cand.idxAt, cand.idx, cand.k = p, src, k
			} else if dj, src, isCopy := indexCopyOf(block[p]); isCopy && dj == cand.idx {
				cand.idxAt, cand.idx = p, src
			}
			break
		}
		out = append(out, cand)
	}
	return out
}

// indexCopyOf reads `mov wJ, wI` between two w registers.
func indexCopyOf(item asm.Item) (dest, src int, ok bool) {
	ins, isIns := item.(asm.Instruction)
	if !isIns || ins.Mnemonic != "mov" || len(ins.Operands) != 2 {
		return 0, 0, false
	}
	d, okD := ins.Operands[0].(asm.Register)
	s, okS := ins.Operands[1].(asm.Register)
	if !okD || !okS || d.Class != asm.ClassW || s.Class != asm.ClassW || d.ZeroRegister() || s.ZeroRegister() {
		return 0, 0, false
	}
	return d.Num, s.Num, true
}

// blockVectorBlock fuses the vector loads of one basic block; live[i] is
// the set of general registers live after block[i].
func blockVectorBlock(block []asm.Item, live []uint32) ([]asm.Item, int) {
	loads := vectorBlockCandidates(block)
	if len(loads) < 2 {
		return block, 0
	}
	dead := func(at, reg int) bool {
		return at < len(live) && live[at]&(1<<uint(reg)) == 0
	}
	removed := map[int]bool{}
	rewritten := map[int]asm.Instruction{}
	fused := 0
	for i := 0; i < len(loads); i++ {
		a := loads[i]
		if removed[a.at] || removed[a.addrAt] {
			continue
		}
		for j := i + 1; j < len(loads); j++ {
			b := loads[j]
			if removed[b.at] || b.base != a.base || b.idx != a.idx || b.shift != a.shift || b.k <= a.k {
				continue
			}
			offset := (b.k - a.k) << uint(a.shift)
			if offset%16 != 0 || offset > 65520 {
				continue
			}
			// Nothing between the kept load and this one may write the
			// base, the index, or the kept address; the dropped address
			// and index adds are this load's own.
			clean := true
			for p := a.at + 1; p < b.at; p++ {
				if p == b.addrAt || p == b.idxAt || removed[p] {
					continue
				}
				ins, isIns := block[p].(asm.Instruction)
				if !isIns || writesReg(ins, a.base) || writesReg(ins, a.idx) || writesReg(ins, a.addr) {
					clean = false
					break
				}
			}
			if !clean {
				continue
			}
			// The registers this load's own instructions wrote must be
			// dead after it.
			if !dead(b.at, b.addr) {
				continue
			}
			if b.idxAt >= 0 {
				if idxReg, _, _, isOffset := indexOffsetOf(block[b.idxAt]); isOffset && !dead(b.at, idxReg) {
					continue
				}
				if idxReg, _, isCopy := indexCopyOf(block[b.idxAt]); isCopy && !dead(b.at, idxReg) {
					continue
				}
			}
			load := block[b.at].(asm.Instruction)
			load.Operands = []asm.Operand{b.dest, asm.Memory{Base: xr(a.addr), Offset: offset, Mode: asm.MemOffset}}
			rewritten[b.at] = load
			removed[b.addrAt] = true
			if b.idxAt >= 0 {
				removed[b.idxAt] = true
			}
			fused++
		}
	}
	if fused == 0 {
		return block, 0
	}
	out := make([]asm.Item, 0, len(block))
	for i, item := range block {
		if removed[i] {
			continue
		}
		if ins, changed := rewritten[i]; changed {
			out = append(out, ins)
			continue
		}
		out = append(out, item)
	}
	return out, fused
}

// FusedVectorBlocks reports how many vector loads a lowering read at an
// immediate offset off a shared element address under Lane.VectorBlocks.
func FusedVectorBlocks(fn *asm.Function) int { return fusedVectorBlocks[fn] }

var fusedVectorBlocks = map[*asm.Function]int{}
