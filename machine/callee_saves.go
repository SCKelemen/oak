package machine

import (
	"slices"

	"github.com/SCKelemen/oak/asm"
)

// TrimCalleeSaves removes unused general-register callee-save traffic from a
// canonical lowered frame. It first removes dead register copies whose
// destinations are among the saved registers, then removes the corresponding
// save and restore or narrows a pair when only one member remains live. The
// stack frame and every offset stay unchanged.
//
// The transform is deliberately narrower than ordinary dead-code elimination:
// it requires one return and an exactly matched lowering-generated prologue and
// epilogue. A shape it does not recognize is returned unchanged. The caller
// still submits every changed body to the seam checker and semantic verifier.
func TrimCalleeSaves(fn *asm.Function) (*asm.Function, int, error) {
	if fn == nil {
		return nil, 0, nil
	}
	lifted, err := Lift(cloneFunction(fn))
	if err != nil {
		return nil, 0, err
	}
	groups, scaffold, ok := lifted.canonicalCalleeSaveFrame()
	if !ok || len(groups) == 0 {
		return lifted.Asm, 0, nil
	}

	deadCopies, err := lifted.removeDeadCalleeCopies(groups)
	if err != nil {
		return nil, 0, err
	}
	saved := map[Reg]bool{}
	for _, group := range groups {
		for _, reg := range group.regs {
			saved[reg] = true
		}
	}
	used := map[Reg]bool{}
	for _, ins := range lifted.Instrs {
		if scaffold[ins] {
			continue
		}
		for _, access := range append(append([]Access(nil), ins.Defs...), ins.Uses...) {
			if saved[access.Reg] {
				used[access.Reg] = true
			}
		}
	}

	removed := map[*Instr]bool{}
	rewritten := map[*Instr]asm.Instruction{}
	pruned := map[Reg]bool{}
	for _, group := range groups {
		var kept []Reg
		keptAt := int64(0)
		for i, reg := range group.regs {
			if used[reg] {
				kept = append(kept, reg)
				keptAt = group.offset + int64(8*i)
			} else {
				pruned[reg] = true
			}
		}
		switch len(kept) {
		case 0:
			removed[group.save], removed[group.restore] = true, true
		case 1:
			if len(group.regs) == 2 {
				rewritten[group.save] = lifted.t.frame.save(kept[0], keptAt, group.save.Asm.Line)
				rewritten[group.restore] = lifted.t.frame.restore(kept[0], keptAt, group.restore.Asm.Line)
			}
		}
	}
	if len(pruned) == 0 {
		// Do not turn this into a generic dead-copy pass. Its purpose is the
		// memory traffic and ABI scaffold which a dead callee home leaves.
		return cloneFunction(fn), 0, nil
	}
	for _, block := range lifted.Blocks {
		kept := block.Instrs[:0]
		for _, ins := range block.Instrs {
			if removed[ins] {
				continue
			}
			if replacement, ok := rewritten[ins]; ok {
				ins.Asm = replacement
			}
			kept = append(kept, ins)
		}
		block.Instrs = kept
	}
	lifted.reindex()
	lifted.Asm.Items = lifted.Items()
	lifted.Asm.Clobbers = slices.DeleteFunc(lifted.Asm.Clobbers, func(clobber asm.Register) bool {
		reg, _, _, ok, err := lifted.t.regOf(clobber)
		return err == nil && ok && pruned[reg]
	})
	return lifted.Asm, deadCopies + len(pruned), nil
}

type calleeSaveGroup struct {
	save, restore *Instr
	regs          []Reg
	offset        int64
}

// canonicalCalleeSaveFrame pairs the lowering's leading x19... saves with the
// corresponding restores in the unique return block.
func (f *Function) canonicalCalleeSaveFrame() ([]calleeSaveGroup, map[*Instr]bool, bool) {
	if len(f.Blocks) == 0 || len(f.Blocks[0].Instrs) == 0 {
		return nil, nil, false
	}
	entry, shape := f.Blocks[0], f.t.frame
	at := 0
	if isStackAdjustment(entry.Instrs[at].Asm, "sub") {
		at++
	}
	if at < len(entry.Instrs) {
		if _, ok := shape.isPairSave(entry.Instrs[at].Asm); ok {
			at++
		}
	}
	var groups []calleeSaveGroup
	saved := 0
	base := int64(0)
	for at < len(entry.Instrs) {
		regs, offset, ok := shape.isSave(entry.Instrs[at].Asm)
		if !ok {
			break
		}
		if len(regs) < 1 || len(regs) > 2 || saved+len(regs) > len(shape.saveOrder) ||
			!slices.Equal(regs, shape.saveOrder[saved:saved+len(regs)]) {
			return nil, nil, false
		}
		if len(groups) == 0 {
			base = offset
		}
		if offset != base+int64(8*saved) {
			return nil, nil, false
		}
		groups = append(groups, calleeSaveGroup{save: entry.Instrs[at], regs: regs, offset: offset})
		saved += len(regs)
		at++
	}
	if len(groups) == 0 {
		return nil, nil, false
	}

	var epilogue *Block
	rets := 0
	for _, ins := range f.Instrs {
		if ins.Ret {
			rets++
			epilogue = ins.Block
		}
	}
	if rets != 1 || epilogue == nil {
		return nil, nil, false
	}
	restoreAt := -1
	for i, ins := range epilogue.Instrs {
		regs, offset, ok := shape.isRestore(ins.Asm)
		if ok && slices.Equal(regs, groups[0].regs) && offset == groups[0].offset {
			restoreAt = i
			break
		}
	}
	if restoreAt < 0 || restoreAt+len(groups) > len(epilogue.Instrs) {
		return nil, nil, false
	}
	scaffold := map[*Instr]bool{}
	for i := range groups {
		restore := epilogue.Instrs[restoreAt+i]
		regs, offset, ok := shape.isRestore(restore.Asm)
		if !ok || !slices.Equal(regs, groups[i].regs) || offset != groups[i].offset {
			return nil, nil, false
		}
		groups[i].restore = restore
		scaffold[groups[i].save], scaffold[restore] = true, true
	}
	if restoreAt+len(groups) < len(epilogue.Instrs) {
		if regs, _, ok := shape.isRestore(epilogue.Instrs[restoreAt+len(groups)].Asm); ok {
			for _, reg := range regs {
				if f.t.calleeSaved(reg) {
					return nil, nil, false
				}
			}
		}
	}
	return groups, scaffold, true
}

func (f *Function) removeDeadCalleeCopies(groups []calleeSaveGroup) (int, error) {
	saved := map[Reg]bool{}
	for _, group := range groups {
		for _, reg := range group.regs {
			saved[reg] = true
		}
	}
	removed := 0
	for {
		webs, err := f.Webs()
		if err != nil {
			return 0, err
		}
		deadDefinition := map[*Instr]bool{}
		for _, web := range webs {
			if len(web.Uses) != 0 {
				continue
			}
			for _, definition := range web.Defs {
				if definition.Instr != nil {
					deadDefinition[definition.Instr] = true
				}
			}
		}
		changed := false
		for _, block := range f.Blocks {
			kept := block.Instrs[:0]
			for _, ins := range block.Instrs {
				dead := ins.Copy && len(ins.Defs) == 1 && saved[ins.Defs[0].Reg] && deadDefinition[ins] && f.t.pure(ins.Asm)
				if dead {
					removed++
					changed = true
					continue
				}
				kept = append(kept, ins)
			}
			block.Instrs = kept
		}
		if !changed {
			return removed, nil
		}
		f.reindex()
	}
}

func isStackAdjustment(instruction asm.Instruction, mnemonic string) bool {
	if instruction.Mnemonic != mnemonic || len(instruction.Operands) != 3 {
		return false
	}
	first, firstOK := instruction.Operands[0].(asm.Register)
	second, secondOK := instruction.Operands[1].(asm.Register)
	_, immediate := instruction.Operands[2].(asm.Immediate)
	return firstOK && secondOK && immediate && first.Class == asm.ClassSP && second.Class == asm.ClassSP
}
