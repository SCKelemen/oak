package machine

import "fmt"

// Global cleanups over the lifted IR, on the webs and the dominator tree
// (docs/notes/optimizer-search-2026-09.md §11 "late copy cleanup", Phase
// C's first pass): copy propagation, which reads a copied value from its
// source wherever the source is unchanged, and dead-code elimination,
// which drops an instruction whose every result no one reads when the
// instruction does nothing else. Both leave stores, calls, branches,
// compares, and anything with a side effect alone; the checker and the
// verifier judge the result like any other candidate.

// Simplify runs copy propagation and dead-code elimination to a fixpoint
// (bounded) and reports how many copies it propagated and instructions it
// removed. The function is rewritten in place; its instruction list and
// indices are current afterwards.
func (f *Function) Simplify() (propagated, eliminated int, err error) {
	for round := 0; round < 8; round++ {
		webs, werr := f.Webs()
		if werr != nil {
			return propagated, eliminated, werr
		}
		f.Liveness(webs)
		p := f.propagateCopies(webs)
		propagated += p
		if p > 0 {
			// The webs changed: rebuild before deciding what is dead.
			if webs, werr = f.Webs(); werr != nil {
				return propagated, eliminated, werr
			}
		}
		e := f.eliminateDead(webs)
		eliminated += e
		if p == 0 && e == 0 {
			return propagated, eliminated, nil
		}
	}
	return propagated, eliminated, nil
}

// propagateCopies rewrites the reads of a copy's destination to its
// source when the source has exactly one definition (so it is unchanged
// wherever the destination is read: a use with one reaching definition is
// dominated by it), the destination is defined only by the copy, every
// read can be respelled (none is a contract's implicit read), and the copy
// is as wide as what flows through it. The copy itself is left for
// dead-code elimination.
func (f *Function) propagateCopies(webs []*Web) int {
	siteWeb := map[site]*Web{}
	for _, w := range webs {
		for _, d := range w.Defs {
			if d.Instr != nil {
				siteWeb[site{d.Instr, d.Access, true}] = w
			}
		}
		for _, u := range w.Uses {
			siteWeb[site{u.Instr, u.Access, false}] = w
		}
	}
	count := 0
	for _, ins := range f.Instrs {
		if !ins.Copy || len(ins.Defs) != 1 || len(ins.Uses) < 1 {
			continue
		}
		dst, src := siteWeb[site{ins, ins.Defs[0], true}], siteWeb[site{ins, ins.Uses[0], false}]
		if dst == nil || src == nil || dst == src || dst.Pinned {
			continue
		}
		if len(dst.Defs) != 1 || len(src.Defs) != 1 || len(dst.Uses) == 0 {
			continue
		}
		if dst.Reg.Class != src.Reg.Class || !copySafe(ins, dst, src) {
			continue
		}
		ok := true
		for _, u := range dst.Uses {
			if u.Access.Implicit || u.Instr == ins || !src.liveAt(usePos(u.Instr)) {
				// The source must still hold its one definition at the
				// read: another web of the register (a call's result, a
				// later assignment) ends its range before that.
				ok = false
				break
			}
		}
		if !ok {
			continue
		}
		for _, u := range dst.Uses {
			f.t.setRegAt(&u.Instr.Asm, u.Access, src.Reg)
		}
		// The destination's reads now belong to the source: refresh the
		// accesses so a later copy in this round sees them.
		for _, u := range dst.Uses {
			for k := range u.Instr.Uses {
				if u.Instr.Uses[k] == u.Access {
					u.Instr.Uses[k].Reg = src.Reg
				}
			}
		}
		count++
		// One propagation per round per source keeps the bookkeeping
		// simple; the next round takes the rest.
		break
	}
	return count
}

// eliminateDead removes the instructions whose every definition no one
// reads, when the instruction is pure on this lane: no store, call,
// branch, compare, atomic, or system effect, and no load from anywhere
// but the frame.
func (f *Function) eliminateDead(webs []*Web) int {
	live := map[site]bool{}
	for _, w := range webs {
		if len(w.Uses) == 0 {
			continue
		}
		for _, d := range w.Defs {
			if d.Instr != nil {
				live[site{d.Instr, d.Access, true}] = true
			}
		}
	}
	removed := 0
	for _, b := range f.Blocks {
		kept := b.Instrs[:0]
		for _, ins := range b.Instrs {
			dead := len(ins.Defs) > 0 && f.t.pure(ins.Asm)
			for _, d := range ins.Defs {
				// A write to a callee-saved or reserved register no one
				// reads is a restore, or a save obligation's: it stays.
				if d.Implicit || live[site{ins, d, true}] || f.t.calleeSaved(d.Reg) || f.t.reserved(d.Reg) {
					dead = false
					break
				}
			}
			if dead {
				removed++
				continue
			}
			kept = append(kept, ins)
		}
		b.Instrs = kept
	}
	if removed > 0 {
		f.reindex()
	}
	return removed
}

// reindex rebuilds the linear instruction list after removals.
func (f *Function) reindex() {
	f.Instrs = f.Instrs[:0]
	for _, b := range f.Blocks {
		for _, ins := range b.Instrs {
			ins.Index = len(f.Instrs)
			ins.Block = b
			f.Instrs = append(f.Instrs, ins)
		}
	}
}

// String spells a web for diagnostics.
func (w *Web) String() string {
	return fmt.Sprintf("%s[%d defs, %d uses, %d–%d]", w.Reg, len(w.Defs), len(w.Uses), w.From, w.To)
}
