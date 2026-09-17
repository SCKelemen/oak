package nativegen

import "github.com/SCKelemen/oak/asm"

type globalAddressSite struct {
	start, def int
	dest       asm.Register
	symbol     string
	uses       []int
}

// shareGlobalAddresses carries the exact address of one declared scalar
// package global through later adrp/add materializations. It is deliberately a
// late AArch64 cleanup: candidate selection still requires the unchanged
// whole-body verifier to authorize the result.
func shareGlobalAddresses(fn *asm.Function) int {
	if fn == nil || (fn.Arch != "" && fn.Arch != asm.ArchArm64) {
		return 0
	}
	total := 0
	for {
		removed := shareOneGlobalAddress(fn)
		if removed == 0 {
			return total
		}
		total += removed
	}
}

func shareOneGlobalAddress(fn *asm.Function) int {
	items := fn.Items
	succ, ok := itemSuccessors(items)
	if !ok || itemCFGHasCycle(succ) {
		return 0
	}
	live := liveAfter(items)
	var sites []globalAddressSite
	for i := 0; i+1 < len(items); i++ {
		if site, found := globalAddressAt(fn, live, i); found {
			sites = append(sites, site)
		}
	}
	for firstIndex, first := range sites {
		group := []globalAddressSite{first}
		for _, site := range sites[firstIndex+1:] {
			if site.symbol != first.symbol || !itemDominates(succ, first.def, site.def) ||
				!globalAddressPathCallFree(items, succ, first.def+1, site.def) {
				continue
			}
			group = append(group, site)
		}
		if len(group) < 2 {
			continue
		}
		scratch, found := globalAddressScratch(fn.Clobbers, items, first.start)
		if !found {
			continue
		}
		out := append([]asm.Item(nil), items...)
		remove := make([]bool, len(items))
		page := out[first.start].(asm.Instruction)
		pageOperands := append([]asm.Operand(nil), page.Operands...)
		pageOperands[0] = scratch
		page.Operands = pageOperands
		page.CheckedFacts = nil
		out[first.start] = page
		low := out[first.def].(asm.Instruction)
		lowOperands := append([]asm.Operand(nil), low.Operands...)
		lowOperands[0], lowOperands[1] = scratch, scratch
		low.Operands = lowOperands
		low.CheckedFacts = nil
		out[first.def] = low
		for _, use := range first.uses {
			out[use] = renameReads(out[use].(asm.Instruction), first.dest.Num, scratch)
		}
		for _, site := range group[1:] {
			remove[site.start], remove[site.def] = true, true
			for _, use := range site.uses {
				out[use] = renameReads(out[use].(asm.Instruction), site.dest.Num, scratch)
			}
		}
		fn.Items = fn.Items[:0]
		for i, item := range out {
			if !remove[i] {
				fn.Items = append(fn.Items, item)
			}
		}
		return len(group) - 1
	}
	return 0
}

const globalAddressMaterializationSpan = 8

func globalAddressAt(fn *asm.Function, live []uint32, start int) (globalAddressSite, bool) {
	page, isPage := fn.Items[start].(asm.Instruction)
	if !isPage || page.Mnemonic != "adrp" || page.Cond != "" || len(page.Operands) != 2 {
		return globalAddressSite{}, false
	}
	dest, destOK := generalReg(page.Operands[0])
	symbol, symbolOK := page.Operands[1].(asm.Symbol)
	global, declared := fn.Globals[symbol.Name]
	if !destOK || dest.Class != asm.ClassX || !symbolOK || symbol.Name == "" || symbol.Lo12 || !declared || global.Aggregate {
		return globalAddressSite{}, false
	}
	def, found := nextGeneralRegisterMention(fn.Items, start+1, start+globalAddressMaterializationSpan, dest.Num)
	if !found {
		return globalAddressSite{}, false
	}
	low := fn.Items[def].(asm.Instruction)
	if low.Mnemonic != "add" || low.Cond != "" || len(low.Operands) != 3 {
		return globalAddressSite{}, false
	}
	lowDest, lowDestOK := generalReg(low.Operands[0])
	lowSource, lowSourceOK := generalReg(low.Operands[1])
	lowSymbol, lowSymbolOK := low.Operands[2].(asm.Symbol)
	if !lowDestOK || !lowSourceOK || !lowSymbolOK || lowDest.Class != asm.ClassX || lowSource.Class != asm.ClassX ||
		lowDest.Num != dest.Num || lowSource.Num != dest.Num || lowSymbol.Name != symbol.Name || !lowSymbol.Lo12 {
		return globalAddressSite{}, false
	}
	uses, _, ok := localDefinitionUses(fn.Items, live, def, dest.Num)
	if !ok || len(uses) == 0 {
		return globalAddressSite{}, false
	}
	return globalAddressSite{start: start, def: def, dest: dest, symbol: symbol.Name, uses: uses}, true
}

func globalAddressPathCallFree(items []asm.Item, succ [][]int, start, target int) bool {
	from := reachableItems(succ, start, -1)
	to := reverseReachable(succ, target)
	if target < 0 || target >= len(items) || !from[target] {
		return false
	}
	for i, item := range items {
		if i == target || !from[i] || !to[i] {
			continue
		}
		if ins, isIns := item.(asm.Instruction); isIns && (ins.Mnemonic == "bl" || ins.Mnemonic == "blr") {
			return false
		}
	}
	return true
}

func globalAddressScratch(clobbers []asm.Register, items []asm.Item, from int) (asm.Register, bool) {
	declared := map[int]bool{}
	for _, reg := range clobbers {
		if reg.Class == asm.ClassW || reg.Class == asm.ClassX {
			declared[reg.Num] = true
		}
	}
	for _, candidate := range []int{17, 16, 15, 14, 13, 12, 11, 10, 9} {
		if !declared[candidate] {
			continue
		}
		used := false
		for i := from; i < len(items); i++ {
			if ins, isIns := items[i].(asm.Instruction); isIns && (readsGeneral(ins, candidate) || writesGeneral(ins, candidate)) {
				used = true
				break
			}
		}
		if !used {
			return xr(candidate), true
		}
	}
	return asm.Register{}, false
}

// SharedGlobalAddresses reports how many repeated scalar-global address pairs
// a verifier-gated candidate removed.
func SharedGlobalAddresses(fn *asm.Function) int { return sharedGlobalAddresses[fn] }

var sharedGlobalAddresses = map[*asm.Function]int{}
