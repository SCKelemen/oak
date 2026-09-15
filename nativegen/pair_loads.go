package nativegen

import (
	"github.com/SCKelemen/oak/asm"
)

// Pair loads (docs/spec/94-assembler.md §9 "Pair loads"). Within one basic
// block, two element loads of one span at consecutive indices —
//
//	ldr x9, [x19, w3, uxtw #3]
//	add x2, x2, x9
//	add w10, w3, #1
//	ldr x10, [x19, w10, uxtw #3]
//
// — become the block's element address formed once and one pair load at
// the immediate offset:
//
//	add x11, x19, w3, uxtw #3
//	ldp x9, x10, [x11]
//	add x2, x2, x9
//
// The second load moves up to the first, so the pass requires that
// nothing between them writes the base, the index, or the block address,
// reads or writes the second destination, or stores to memory; the index
// temporary the second load consumed (`add w10, w3, #1`) is dropped with
// it. The block address is a scratch register the block never names, so
// the register allocation stands. The seam checker admits the pair through
// the element region the index's slack guard marks (`add xE, xB, wI, uxtw
// #s` under wI + K <= len, docs/spec/94-assembler.md §7), and the verifier
// reads a pair load as two loads (asm/verify.go). The four loads of an
// unrolled reduction (nativegen/reduction.go) become two pairs.

// elementLoad is a candidate: the load at items[at], of size bytes, of the
// span at base indexed by idx + k, with the index temporary written at
// items[at-1] when k > 0.
type elementLoad struct {
	at     int
	dest   asm.Register
	base   int
	idx    int
	k      int64
	size   int64
	hasAdd bool
}

// pairLoads rewrites the items of one function.
func pairLoads(items []asm.Item) []asm.Item {
	// The block address must be a register the whole function never names:
	// a scratch register the second lowering pass handed to a variable as a
	// home is live across blocks that never mention it.
	mentioned := registersMentioned(items)
	// Basic blocks: split at labels and after transfers.
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
				end = i + 1 // the transfer closes its block
			}
		}
		out = append(out, pairBlock(items[start:end], mentioned)...)
		if end == i {
			if i < len(items) {
				out = append(out, items[i])
			}
			start = i + 1
		} else {
			start = end
		}
	}
	return out
}

func isTransfer(ins asm.Instruction) bool {
	switch ins.Mnemonic {
	case "b", "b.", "bl", "blr", "br", "ret", "cbz", "cbnz", "tbz", "tbnz", "brk", "eret", "svc", "hvc", "smc":
		return true
	}
	return false
}

// pairBlock pairs the loads of one basic block; mentioned is the set of
// registers the function names, which a block address is taken outside of.
func pairBlock(block []asm.Item, mentioned map[int]bool) []asm.Item {
	loads := elementLoads(block)
	if len(loads) < 2 {
		return block
	}
	removed := map[int]bool{}
	type replacement struct {
		address *asm.Instruction // the block address formed before the pair, or nil
		pair    asm.Instruction
	}
	replaced := map[int]replacement{}
	// The block address per (base, idx, size), valid while nothing writes
	// its inputs or itself.
	type blockAddr struct {
		reg   int
		since int
	}
	addresses := map[[3]int64]blockAddr{}
	for i := 0; i < len(loads); i++ {
		a := loads[i]
		if removed[a.at] || a.dest.Class == asm.ClassV {
			continue
		}
		for j := i + 1; j < len(loads); j++ {
			b := loads[j]
			if removed[b.at] || b.base != a.base || b.idx != a.idx || b.size != a.size || b.k != a.k+1 || b.dest.Class != a.dest.Class {
				continue
			}
			if a.dest.Num == b.dest.Num {
				break // one register cannot hold both halves
			}
			offset := a.k * a.size
			if offset%a.size != 0 || offset > 504 || offset < -512 {
				break
			}
			// Nothing between the two loads (the second's index add
			// excluded) may write the base or the index, touch the
			// second destination, or store.
			clean := true
			for p := a.at + 1; p < b.at; p++ {
				if b.hasAdd && p == b.at-1 {
					continue
				}
				ins, isIns := block[p].(asm.Instruction)
				if !isIns {
					clean = false
					break
				}
				if writesMemory(ins.Mnemonic) || mentionsReg(ins, b.dest.Num) || writesReg(ins, a.base) || writesReg(ins, a.idx) {
					clean = false
					break
				}
			}
			if !clean {
				break
			}
			key := [3]int64{int64(a.base), int64(a.idx), a.size}
			addr, have := addresses[key]
			var formed *asm.Instruction
			if have {
				// Still valid only if nothing since wrote the address or its inputs.
				for p := addr.since; p < a.at; p++ {
					if ins, isIns := block[p].(asm.Instruction); isIns && (writesReg(ins, addr.reg) || writesReg(ins, a.base) || writesReg(ins, a.idx)) {
						have = false
						break
					}
				}
			}
			if !have {
				reg := freeScratch(mentioned)
				if reg < 0 {
					return block
				}
				mentioned[reg] = true
				shift := int64(0)
				for s := a.size; s > 1; s >>= 1 {
					shift++
				}
				ins := asm.Instruction{Mnemonic: "add", Operands: []asm.Operand{xr(reg), xr(a.base), asm.Extended{Reg: wr(a.idx), Kind: "uxtw", Amount: shift}}, Line: lineOf(block[a.at])}
				formed = &ins
				addr = blockAddr{reg: reg, since: a.at}
				addresses[key] = addr
			}
			pair := asm.Instruction{Mnemonic: "ldp", Operands: []asm.Operand{a.dest, b.dest, asm.Memory{Base: xr(addr.reg), Offset: offset, Mode: asm.MemOffset}}, Line: lineOf(block[a.at])}
			replaced[a.at] = replacement{address: formed, pair: pair}
			removed[b.at] = true
			if b.hasAdd {
				removed[b.at-1] = true
			}
			if a.hasAdd {
				removed[a.at-1] = true
			}
			removed[a.at] = true // rewritten in place
			break
		}
	}
	if len(replaced) == 0 {
		return block
	}
	var out []asm.Item
	for p, item := range block {
		if r, isReplaced := replaced[p]; isReplaced {
			if r.address != nil {
				out = append(out, *r.address)
			}
			out = append(out, r.pair)
			continue
		}
		if removed[p] {
			continue
		}
		out = append(out, item)
	}
	return out
}

// elementLoads finds the block's scaled element loads of a span base by a
// w index, with the immediate add that formed the index when the index is
// a temporary written just before.
func elementLoads(block []asm.Item) []elementLoad {
	var loads []elementLoad
	for at, item := range block {
		ins, isIns := item.(asm.Instruction)
		if !isIns || ins.Mnemonic != "ldr" || len(ins.Operands) != 2 {
			continue
		}
		dest, isReg := ins.Operands[0].(asm.Register)
		mem, isMem := ins.Operands[1].(asm.Memory)
		if !isReg || !isMem || mem.Index == nil || mem.Extend != "uxtw" || mem.Mode != asm.MemOffset || mem.Offset != 0 || mem.Base.Class != asm.ClassX {
			continue
		}
		size := int64(1) << uint(mem.Shift)
		if (dest.Class == asm.ClassX && size != 8) || (dest.Class == asm.ClassW && size != 4) || (dest.Class != asm.ClassX && dest.Class != asm.ClassW) {
			continue
		}
		load := elementLoad{at: at, dest: dest, base: mem.Base.Num, idx: mem.Index.Num, size: size}
		// The index formed by `add wT, wI, #k` just before, consumed only here.
		if at > 0 {
			if add, isAdd := block[at-1].(asm.Instruction); isAdd && add.Mnemonic == "add" && len(add.Operands) == 3 {
				t, okT := add.Operands[0].(asm.Register)
				src, okS := add.Operands[1].(asm.Register)
				k, okK := add.Operands[2].(asm.Immediate)
				// The temporary dies at the load: the load overwrites it (the
				// usual shape, the destination is the temporary's register)
				// or nothing reads it again before a write.
				dies := dest.Num == t.Num || !readsAfter(block, at+1, t.Num)
				if okT && okS && okK && t.Class == asm.ClassW && src.Class == asm.ClassW && t.Num == mem.Index.Num && t.Num != src.Num && k.Shift == 0 && k.Value > 0 && dies {
					load.idx, load.k, load.hasAdd = src.Num, k.Value, true
				}
			}
		}
		loads = append(loads, load)
	}
	return loads
}

// readsAfter reports whether the register is read from index from before
// it is written again (the index temporary must be dead after its load).
func readsAfter(block []asm.Item, from, reg int) bool {
	for p := from; p < len(block); p++ {
		ins, isIns := block[p].(asm.Instruction)
		if !isIns {
			return false
		}
		if readsReg(ins, reg) {
			return true
		}
		if writesReg(ins, reg) {
			return false
		}
	}
	return false
}

func lineOf(item asm.Item) int {
	if ins, isIns := item.(asm.Instruction); isIns {
		return ins.Line
	}
	return 0
}

// freeScratch picks a scratch register the block never names.
func freeScratch(mentioned map[int]bool) int {
	for r := scratchHigh; r >= scratchLow; r-- {
		if !mentioned[r] {
			return r
		}
	}
	return -1
}

// registersMentioned collects every general register number the block names.
func registersMentioned(block []asm.Item) map[int]bool {
	out := map[int]bool{}
	for _, item := range block {
		ins, isIns := item.(asm.Instruction)
		if !isIns {
			continue
		}
		for _, r := range generalRegisters(ins) {
			out[r] = true
		}
	}
	return out
}

// generalRegisters lists the general register numbers an instruction names.
func generalRegisters(ins asm.Instruction) []int {
	var regs []int
	for _, operand := range ins.Operands {
		switch o := operand.(type) {
		case asm.Register:
			if (o.Class == asm.ClassX || o.Class == asm.ClassW) && !o.ZeroRegister() {
				regs = append(regs, o.Num)
			}
		case asm.Memory:
			regs = append(regs, o.Base.Num)
			if o.Index != nil {
				regs = append(regs, o.Index.Num)
			}
		case asm.Extended:
			regs = append(regs, o.Reg.Num)
		}
	}
	return regs
}

func mentionsReg(ins asm.Instruction, reg int) bool {
	for _, r := range generalRegisters(ins) {
		if r == reg {
			return true
		}
	}
	return false
}

// writesReg: the first register operand of a writing instruction (loads
// and data processing), both registers of a pair load.
func writesReg(ins asm.Instruction, reg int) bool {
	if writesMemory(ins.Mnemonic) || ins.Mnemonic == "cmp" || ins.Mnemonic == "cmn" || ins.Mnemonic == "tst" || ins.Mnemonic == "ccmp" || ins.Mnemonic == "prfm" {
		return false
	}
	n := 1
	if ins.Mnemonic == "ldp" || ins.Mnemonic == "ldpsw" {
		n = 2
	}
	for i := 0; i < n && i < len(ins.Operands); i++ {
		if r, isReg := ins.Operands[i].(asm.Register); isReg && (r.Class == asm.ClassX || r.Class == asm.ClassW) && r.Num == reg {
			return true
		}
	}
	return false
}

// readsReg: every general register the instruction names other than a
// destination it only writes.
func readsReg(ins asm.Instruction, reg int) bool {
	regs := generalRegisters(ins)
	if len(regs) == 0 {
		return false
	}
	start := 0
	if !writesMemory(ins.Mnemonic) && ins.Mnemonic != "cmp" && ins.Mnemonic != "cmn" && ins.Mnemonic != "tst" && ins.Mnemonic != "ccmp" {
		start = 1 // the destination
		if ins.Mnemonic == "ldp" {
			start = 2
		}
	}
	// A destination operand register also read (an in-place update) is
	// found again among the sources below; the memory operand's registers
	// come after the destination in the list.
	for i := start; i < len(regs); i++ {
		if regs[i] == reg {
			return true
		}
	}
	return false
}

func writesMemory(mnemonic string) bool {
	switch mnemonic {
	case "str", "strb", "strh", "stp", "stur", "sturb", "sturh", "stlr", "stlrb", "stlrh", "stxr", "stlxr", "st1", "st2", "st3", "st4", "stnp", "swp", "swpa", "swpl", "swpal", "cas", "casa", "casl", "casal":
		return true
	}
	return len(mnemonic) > 2 && mnemonic[:2] == "st"
}
