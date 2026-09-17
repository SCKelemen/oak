package nativegen

import "github.com/SCKelemen/oak/asm"

// forwardGlobalLoads replaces an exact scalar-global load immediately after
// a store to the same cell. The store stays in place. Narrow loads become the
// truncation the memory round trip performed; full-width loads become a move,
// or disappear when they return to the stored register. Candidate selection
// remains gated by the whole-body verifier.
func forwardGlobalLoads(fn *asm.Function) int {
	if fn == nil || (fn.Arch != "" && fn.Arch != asm.ArchArm64) {
		return 0
	}
	forwarded := 0
	out := make([]asm.Item, 0, len(fn.Items))
	for i := 0; i < len(fn.Items); i++ {
		store, isStore := fn.Items[i].(asm.Instruction)
		if !isStore || i+1 >= len(fn.Items) {
			out = append(out, fn.Items[i])
			continue
		}
		load, isLoad := fn.Items[i+1].(asm.Instruction)
		replacement, keep, ok := forwardGlobalLoadAt(fn, i, store, load)
		if !isLoad || !ok {
			out = append(out, fn.Items[i])
			continue
		}
		out = append(out, store)
		if keep {
			out = append(out, replacement)
		}
		forwarded++
		i++
	}
	if forwarded != 0 {
		fn.Items = out
	}
	return forwarded
}

func forwardGlobalLoadAt(fn *asm.Function, at int, store, load asm.Instruction) (asm.Instruction, bool, bool) {
	if store.Cond != "" || load.Cond != "" || len(store.Operands) != 2 || len(load.Operands) != 2 {
		return asm.Instruction{}, false, false
	}
	source, sourceOK := store.Operands[0].(asm.Register)
	dest, destOK := load.Operands[0].(asm.Register)
	storeMemory, storeMemoryOK := store.Operands[1].(asm.Memory)
	loadMemory, loadMemoryOK := load.Operands[1].(asm.Memory)
	if !sourceOK || !destOK || !storeMemoryOK || !loadMemoryOK || dest.ZeroRegister() ||
		!sameGlobalMemory(storeMemory, loadMemory) {
		return asm.Instruction{}, false, false
	}
	global, ok := globalAddressBefore(fn, at, storeMemory.Base.Num)
	if !ok || global.Aggregate {
		return asm.Instruction{}, false, false
	}
	replacement := load
	replacement.Cond = ""
	replacement.CheckedFacts = nil
	switch global.Bits {
	case 8:
		if store.Mnemonic != "strb" || load.Mnemonic != "ldrb" || source.Class != asm.ClassW || dest.Class != asm.ClassW {
			return asm.Instruction{}, false, false
		}
		replacement.Mnemonic = "and"
		replacement.Operands = []asm.Operand{dest, source, asm.Immediate{Value: 0xff}}
	case 16:
		if store.Mnemonic != "strh" || load.Mnemonic != "ldrh" || source.Class != asm.ClassW || dest.Class != asm.ClassW {
			return asm.Instruction{}, false, false
		}
		replacement.Mnemonic = "and"
		replacement.Operands = []asm.Operand{dest, source, asm.Immediate{Value: 0xffff}}
	case 32:
		if store.Mnemonic != "str" || load.Mnemonic != "ldr" || source.Class != asm.ClassW || dest.Class != asm.ClassW {
			return asm.Instruction{}, false, false
		}
		if source.Num == dest.Num {
			return asm.Instruction{}, false, true
		}
		replacement.Mnemonic = "mov"
		replacement.Operands = []asm.Operand{dest, source}
	case 64:
		if store.Mnemonic != "str" || load.Mnemonic != "ldr" || source.Class != asm.ClassX || dest.Class != asm.ClassX {
			return asm.Instruction{}, false, false
		}
		if source.Num == dest.Num {
			return asm.Instruction{}, false, true
		}
		replacement.Mnemonic = "mov"
		replacement.Operands = []asm.Operand{dest, source}
	default:
		return asm.Instruction{}, false, false
	}
	return replacement, true, true
}

func sameGlobalMemory(left, right asm.Memory) bool {
	return left.Mode == asm.MemOffset && right.Mode == asm.MemOffset &&
		left.Index == nil && right.Index == nil && left.Offset == 0 && right.Offset == 0 &&
		left.Base.Class == asm.ClassX && right.Base.Class == asm.ClassX &&
		left.Base.Num == right.Base.Num && left.Shift == 0 && right.Shift == 0 &&
		left.Extend == "" && right.Extend == "" && !left.MulVL && !right.MulVL
}

// globalAddressBefore authenticates base as the last exact adrp/add address
// materialization before at. The retained store is independently checked at
// the assembler seam, including dominance on every control-flow path.
func globalAddressBefore(fn *asm.Function, at, base int) (asm.Global, bool) {
	for i := at - 1; i >= 0; i-- {
		ins, isIns := fn.Items[i].(asm.Instruction)
		if !isIns {
			continue
		}
		if ins.Mnemonic == "bl" || ins.Mnemonic == "blr" {
			return asm.Global{}, false
		}
		if !writesGeneral(ins, base) {
			continue
		}
		if ins.Mnemonic != "add" || ins.Cond != "" || len(ins.Operands) != 3 {
			return asm.Global{}, false
		}
		dest, destOK := generalReg(ins.Operands[0])
		source, sourceOK := generalReg(ins.Operands[1])
		low, lowOK := ins.Operands[2].(asm.Symbol)
		if !destOK || !sourceOK || !lowOK || dest.Class != asm.ClassX || source.Class != asm.ClassX ||
			dest.Num != base || source.Num != base || low.Name == "" || !low.Lo12 {
			return asm.Global{}, false
		}
		for j := i - 1; j >= 0; j-- {
			page, isPage := fn.Items[j].(asm.Instruction)
			if !isPage {
				continue
			}
			if page.Mnemonic == "bl" || page.Mnemonic == "blr" {
				return asm.Global{}, false
			}
			if !writesGeneral(page, base) {
				continue
			}
			if page.Mnemonic != "adrp" || page.Cond != "" || len(page.Operands) != 2 {
				return asm.Global{}, false
			}
			pageDest, pageDestOK := generalReg(page.Operands[0])
			high, highOK := page.Operands[1].(asm.Symbol)
			global, declared := fn.Globals[low.Name]
			if !pageDestOK || !highOK || pageDest.Class != asm.ClassX || pageDest.Num != base ||
				high.Name != low.Name || high.Lo12 || !declared {
				return asm.Global{}, false
			}
			return global, true
		}
		return asm.Global{}, false
	}
	return asm.Global{}, false
}

// ForwardedGlobalLoads reports exact scalar-global store/load pairs forwarded
// by a verifier-gated candidate.
func ForwardedGlobalLoads(fn *asm.Function) int { return forwardedGlobalLoads[fn] }

var forwardedGlobalLoads = map[*asm.Function]int{}
