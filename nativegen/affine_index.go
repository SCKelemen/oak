package nativegen

import (
	"strings"

	"github.com/SCKelemen/oak/asm"
)

// carryLoopIndices proposes a carried index for a rotated scalar fill:
//
//	i = 0; while i < N { index = base + i; guard(index); store(index); i++ }
//
// becomes index = base; end = base + N; while index != end { guard(index);
// store(index); index++ }. All arithmetic is modular u32. Equality at the
// endpoint handles wrap without assuming base + N fits. The existing loop
// verifier must prove the affine coupling and every guard/write; this pass
// is a gated candidate, never authority to change a trusted body.
//
// This first matcher accepts one scalar store, a unit step, an immediate
// positive trip count, and a dominating zero initializer. Both replaced
// temporaries must be dead at the exit. It reuses the old counter for the
// endpoint, so there is no new register or ABI obligation. No memory access
// is widened, reordered, elided, or moved out of the loop.
func carryLoopIndices(items []asm.Item) ([]asm.Item, int) {
	changed := 0
	for h := 2; h+8 < len(items); h++ {
		label, ok := items[h].(asm.Label)
		if !ok || !strings.HasPrefix(label.Name, "loop_") {
			continue
		}
		if out, ok := carryLoopIndex(items, h, label.Name); ok {
			items = out
			changed++
			h++ // the rewrite adds one item before the next loop
		}
	}
	return items, changed
}

func carryLoopIndex(items []asm.Item, h int, name string) ([]asm.Item, bool) {
	// Entry compare/branch, then exactly seven instructions and an exit
	// label. No unmodeled body instruction can consume flags, mutate the
	// base, use the old counter, or introduce another path through the loop.
	var loop [7]asm.Instruction
	for k := range loop {
		ins, ok := items[h+1+k].(asm.Instruction)
		if !ok {
			return nil, false
		}
		loop[k] = ins
	}
	entryCmp, cmpOK := items[h-2].(asm.Instruction)
	entryBranch, branchOK := items[h-1].(asm.Instruction)
	exit, exitOK := items[h+8].(asm.Label)
	if !cmpOK || !branchOK || !exitOK || entryCmp.Mnemonic != "cmp" || len(entryCmp.Operands) != 2 ||
		!affineBranch(entryBranch, "hs", exit.Name) || !affineBranch(loop[6], "lo", name) {
		return nil, false
	}
	counter, counterOK := generalReg(entryCmp.Operands[0])
	bound, boundOK := entryCmp.Operands[1].(asm.Immediate)
	if !counterOK || counter.Class != asm.ClassW || !boundOK || bound.Shift != 0 || bound.Value <= 0 || bound.Value > 4095 {
		return nil, false
	}
	add, guard, store, step, tailCmp := loop[0], loop[1], loop[3], loop[4], loop[5]
	if add.Mnemonic != "add" || len(add.Operands) != 3 || add.Cond != "" ||
		step.Mnemonic != "add" || len(step.Operands) != 3 || step.Cond != "" ||
		tailCmp.Mnemonic != "cmp" || len(tailCmp.Operands) != 2 {
		return nil, false
	}
	index, indexOK := generalReg(add.Operands[0])
	left, leftOK := generalReg(add.Operands[1])
	right, rightOK := generalReg(add.Operands[2])
	if !indexOK || !leftOK || !rightOK || index.Class != asm.ClassW || left.Class != asm.ClassW || right.Class != asm.ClassW {
		return nil, false
	}
	base := left
	if left.Num == counter.Num {
		base, right = right, left
	}
	tailBound, tailBoundOK := tailCmp.Operands[1].(asm.Immediate)
	if right.Num != counter.Num || base.Num == counter.Num || index.Num == counter.Num || index.Num == base.Num ||
		!affineReg(step.Operands[0], counter) || !affineReg(step.Operands[1], counter) ||
		!affineReg(tailCmp.Operands[0], counter) || !tailBoundOK || tailBound != bound {
		return nil, false
	}
	stride, strideOK := step.Operands[2].(asm.Immediate)
	if !strideOK || stride.Shift != 0 || stride.Value != 1 ||
		guard.Mnemonic != "cmp" || len(guard.Operands) != 2 || !affineReg(guard.Operands[0], index) ||
		readsGeneral(guard, counter.Num) {
		return nil, false
	}
	trap, trapOK := affineTrapTarget(items, loop[2])
	if !trapOK || trap == name || trap == exit.Name {
		return nil, false
	}
	switch store.Mnemonic {
	case "str", "strb", "strh":
	default:
		return nil, false
	}
	if len(store.Operands) != 2 || readsGeneral(store, counter.Num) {
		return nil, false
	}
	value, valueOK := store.Operands[0].(asm.Register)
	if !valueOK || (value.Class != asm.ClassW && value.Class != asm.ClassX) {
		return nil, false
	}
	mem, memOK := store.Operands[1].(asm.Memory)
	if !memOK || mem.Mode != asm.MemOffset || mem.MulVL || mem.Index == nil || !affineReg(*mem.Index, index) ||
		mem.Extend != "uxtw" || mem.Base.Class != asm.ClassX || mem.Base.ZeroRegister() || mem.Base.Num == index.Num {
		return nil, false
	}
	// Nothing else may reach the header, including an entry bypassing the
	// new setup. All other body positions are instructions, not labels.
	for i, item := range items {
		if ins, ok := item.(asm.Instruction); ok && i != h+7 {
			for _, operand := range ins.Operands {
				if sym, ok := operand.(asm.Symbol); ok && sym.Name == name {
					return nil, false
				}
			}
		}
	}
	if !affineZeroBefore(items, h-2, counter) {
		return nil, false
	}
	live := liveAfter(items)
	if live[h+8]&((1<<uint(counter.Num))|(1<<uint(index.Num))) != 0 {
		return nil, false
	}
	compare := entryCmp
	compare.Operands = []asm.Operand{index, counter}
	compare.CheckedFacts = nil
	entryBranch.Cond = "eq"
	entryBranch.CheckedFacts = nil
	step.Operands = []asm.Operand{index, index, stride}
	step.CheckedFacts = nil
	back := loop[6]
	back.Cond = "ne"
	back.CheckedFacts = nil
	endpoint := add
	endpoint.Operands = []asm.Operand{counter, base, bound}
	endpoint.CheckedFacts = nil
	add.CheckedFacts = nil
	var out []asm.Item
	out = append(out, items[:h-2]...)
	out = append(out, add, endpoint, compare, entryBranch, items[h])
	out = append(out, guard, loop[2], store, step, compare, back)
	out = append(out, items[h+8:]...)
	return out, true
}

func affineReg(operand asm.Operand, want asm.Register) bool {
	r, ok := generalReg(operand)
	return ok && r.Num == want.Num && r.Class == want.Class
}

func affineBranch(ins asm.Instruction, cond, target string) bool {
	if ins.Mnemonic != "b." || ins.Cond != cond || len(ins.Operands) != 1 {
		return false
	}
	sym, ok := ins.Operands[0].(asm.Symbol)
	return ok && sym.Name == target
}

func affineTrapTarget(items []asm.Item, branch asm.Instruction) (string, bool) {
	if branch.Mnemonic != "b." || branch.Cond != "hs" || len(branch.Operands) != 1 {
		return "", false
	}
	sym, ok := branch.Operands[0].(asm.Symbol)
	if !ok {
		return "", false
	}
	for i, item := range items {
		if label, ok := item.(asm.Label); ok && label.Name == sym.Name && i+1 < len(items) {
			ins, ok := items[i+1].(asm.Instruction)
			return sym.Name, ok && ins.Mnemonic == "brk"
		}
	}
	return "", false
}

func affineZeroBefore(items []asm.Item, before int, counter asm.Register) bool {
	for i := before - 1; i >= 0; i-- {
		ins, ok := items[i].(asm.Instruction)
		if !ok || ins.Mnemonic == "bl" || ins.Mnemonic == "blr" || ins.Mnemonic == "b" || ins.Mnemonic == "ret" {
			return false
		}
		if !writesGeneral(ins, counter.Num) {
			continue
		}
		if (ins.Mnemonic != "mov" && ins.Mnemonic != "movz") || len(ins.Operands) != 2 || !affineReg(ins.Operands[0], counter) {
			return false
		}
		if r, ok := ins.Operands[1].(asm.Register); ok {
			return ins.Mnemonic == "mov" && r.Class == asm.ClassW && r.ZeroRegister()
		}
		imm, ok := ins.Operands[1].(asm.Immediate)
		return ok && imm.Value == 0
	}
	return false
}

// CarriedLoopIndices reports the loops changed by the proof-gated pass.
func CarriedLoopIndices(fn *asm.Function) int { return carriedLoopIndices[fn] }

var carriedLoopIndices = map[*asm.Function]int{}
