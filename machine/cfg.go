package machine

import (
	"fmt"

	"github.com/SCKelemen/oak/asm"
)

// buildBlocks splits the items into blocks: a block begins at a label or
// after a terminator; labels and alignment directives lead the block they
// precede.
func (f *Function) buildBlocks() error {
	var cur *Block
	var lead []asm.Item
	begin := func(label string) {
		cur = &Block{Index: len(f.Blocks), Label: label, Lead: lead}
		lead = nil
		f.Blocks = append(f.Blocks, cur)
		if label != "" {
			f.labels[label] = cur
		}
	}
	for _, item := range f.Asm.Items {
		switch it := item.(type) {
		case asm.Label:
			if _, dup := f.labels[it.Name]; dup {
				return fmt.Errorf("machine: label %s defined twice", it.Name)
			}
			if cur != nil && len(cur.Instrs) == 0 && cur.Label == "" && len(f.Blocks) > 0 {
				// An empty unlabeled block (an alignment before a label):
				// the label takes it over.
				cur.Label = it.Name
				cur.Lead = append(cur.Lead, item)
				f.labels[it.Name] = cur
				continue
			}
			lead = append(lead, item)
			begin(it.Name)
		case asm.Align:
			lead = append(lead, item)
			if cur == nil || len(cur.Instrs) > 0 {
				// An alignment directive begins the block it aligns.
				begin("")
			} else {
				cur.Lead = append(cur.Lead, item)
				lead = nil
			}
		case asm.Instruction:
			if cur == nil || len(lead) > 0 {
				begin("")
			}
			ins := &Instr{Index: len(f.Instrs), Asm: it, Block: cur}
			f.Instrs = append(f.Instrs, ins)
			cur.Instrs = append(cur.Instrs, ins)
			if terminator(it) {
				cur = nil
			}
		default:
			return fmt.Errorf("machine: item of an unknown kind")
		}
	}
	if len(lead) > 0 {
		// Trailing labels or directives: a block of their own.
		begin("")
	}
	return nil
}

// connect adds the control-flow edges: a branch to its target, a
// conditional branch and a block without a terminator to the next block
// as well; a return or a trap ends the flow.
func (f *Function) connect() error {
	edge := func(from, to *Block) {
		from.Succs = append(from.Succs, to)
		to.Preds = append(to.Preds, from)
	}
	for i, b := range f.Blocks {
		var next *Block
		if i+1 < len(f.Blocks) {
			next = f.Blocks[i+1]
		}
		if len(b.Instrs) == 0 {
			if next != nil {
				edge(b, next)
			}
			continue
		}
		last := b.Instrs[len(b.Instrs)-1]
		switch {
		case last.Ret || last.Trap:
		case last.Branch:
			target := branchTarget(last.Asm)
			to, ok := f.labels[target]
			if !ok {
				return fmt.Errorf("machine: line %d: branch to an unknown label %q", last.Asm.Line, target)
			}
			edge(b, to)
			if conditional(last.Asm) && next != nil {
				edge(b, next)
			}
		default:
			if next != nil {
				edge(b, next)
			}
		}
	}
	return nil
}

// conditional reports a branch that may fall through: b.cond and the
// compare-and-branch forms.
func conditional(ins asm.Instruction) bool {
	switch ins.Mnemonic {
	case "cbz", "cbnz", "tbz", "tbnz", "b.":
		return true
	case "b":
		return ins.Cond != ""
	}
	return false
}
