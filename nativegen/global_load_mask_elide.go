package nativegen

import "github.com/SCKelemen/oak/asm"

// elideGlobalLoadMasks strengthens narrow scalar-global forwarding after
// forwardGlobalLoads has replaced a reload with its exact truncation. It turns
// that mask into a move, or removes it when source and destination coincide.
// The matcher establishes only the machine shape; the whole-body verifier must
// prove that the Oak value stored at each site was already width-normalized.
func elideGlobalLoadMasks(fn *asm.Function) int {
	if fn == nil || (fn.Arch != "" && fn.Arch != asm.ArchArm64) {
		return 0
	}
	elided := 0
	out := make([]asm.Item, 0, len(fn.Items))
	for i := 0; i < len(fn.Items); i++ {
		store, isStore := fn.Items[i].(asm.Instruction)
		if !isStore || i+1 >= len(fn.Items) {
			out = append(out, fn.Items[i])
			continue
		}
		mask, isMask := fn.Items[i+1].(asm.Instruction)
		replacement, keep, ok := elideGlobalLoadMaskAt(fn, i, store, mask)
		if !isMask || !ok {
			out = append(out, fn.Items[i])
			continue
		}
		out = append(out, store)
		if keep {
			out = append(out, replacement)
		}
		elided++
		i++
	}
	if elided != 0 {
		fn.Items = out
	}
	return elided
}

func elideGlobalLoadMaskAt(fn *asm.Function, at int, store, mask asm.Instruction) (asm.Instruction, bool, bool) {
	if store.Cond != "" || mask.Cond != "" || len(store.Operands) != 2 ||
		mask.Mnemonic != "and" || len(mask.Operands) != 3 {
		return asm.Instruction{}, false, false
	}
	source, sourceOK := store.Operands[0].(asm.Register)
	memory, memoryOK := store.Operands[1].(asm.Memory)
	dest, destOK := mask.Operands[0].(asm.Register)
	maskSource, maskSourceOK := mask.Operands[1].(asm.Register)
	immediate, immediateOK := mask.Operands[2].(asm.Immediate)
	if !sourceOK || !memoryOK || !destOK || !maskSourceOK || !immediateOK ||
		source.Class != asm.ClassW || dest.Class != asm.ClassW || maskSource.Class != asm.ClassW ||
		dest.ZeroRegister() || source.Num != maskSource.Num || immediate.Shift != 0 || immediate.MSL ||
		!sameGlobalMemory(memory, memory) {
		return asm.Instruction{}, false, false
	}
	global, ok := globalAddressBefore(fn, at, memory.Base.Num)
	if !ok || global.Aggregate {
		return asm.Instruction{}, false, false
	}
	switch global.Bits {
	case 8:
		if store.Mnemonic != "strb" || immediate.Value != 0xff {
			return asm.Instruction{}, false, false
		}
	case 16:
		if store.Mnemonic != "strh" || immediate.Value != 0xffff {
			return asm.Instruction{}, false, false
		}
	default:
		return asm.Instruction{}, false, false
	}
	if source.Num == dest.Num {
		return asm.Instruction{}, false, true
	}
	replacement := mask
	replacement.Mnemonic = "mov"
	replacement.Operands = []asm.Operand{dest, source}
	replacement.CheckedFacts = nil
	replacement.OptIRCallSite = 0
	return replacement, true, true
}

// ElidedGlobalLoadMasks reports masks replaced or removed by the stronger,
// verifier-gated scalar-global forwarding candidate.
func ElidedGlobalLoadMasks(fn *asm.Function) int { return elidedGlobalLoadMasks[fn] }

var elidedGlobalLoadMasks = map[*asm.Function]int{}
