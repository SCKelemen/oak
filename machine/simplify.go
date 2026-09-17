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

// simplifyRounds bounds the fixpoint: one copy propagates a round (the
// webs are rebuilt between), so a body with hundreds of promoted slot
// reads needs hundreds of rounds; the loop ends at the first round that
// changes nothing.
const simplifyRounds = 1024

// Simplify runs copy propagation and dead-code elimination to a fixpoint
// (bounded) and reports how many copies it propagated and instructions it
// removed. The function is rewritten in place; its instruction list and
// indices are current afterwards.
func (f *Function) Simplify() (propagated, eliminated int, err error) {
	for round := 0; round < simplifyRounds; round++ {
		webs, werr := f.Webs()
		if werr != nil {
			return propagated, eliminated, werr
		}
		f.Liveness(webs)
		copyDst := f.propagateCopy(webs)
		if copyDst != nil {
			propagated++
		}
		// Only the copy's destination became unread. The source is still
		// read by the copy, and every transferred read reaches its existing
		// definitions. DCE can use the original webs except this destination;
		// ranges, widths and pinning are rebuilt at the next round.
		e := f.eliminateDead(webs, copyDst)
		eliminated += e
		if copyDst == nil && e == 0 {
			return propagated, eliminated, nil
		}
	}
	return propagated, eliminated, nil
}

// propagateCopy rewrites the reads of a copy's destination to its
// source when the source still holds the copied value at every read,
// the destination is defined only by the copy, every
// read can be respelled (none is a contract's implicit read), and the copy
// is as wide as what flows through it. It returns the destination web, or nil
// if nothing propagated. The physical source and destination always differ,
// so the destination is now unread: DCE may use the original webs excluding
// it. The copy itself is left for elimination; further propagation always
// needs fresh webs.
func (f *Function) propagateCopy(webs []*Web) *Web {
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
	for _, ins := range f.Instrs {
		if !ins.Copy || len(ins.Defs) != 1 || len(ins.Uses) < 1 {
			continue
		}
		if ins.Defs[0].Reg == ins.Uses[0].Reg {
			// Distinct webs can name the same physical register. Respellings
			// would change nothing and could consume every fixpoint round,
			// starving later copies. Keep the instruction: a narrow self-copy
			// can still clear upper bits, so only width-aware removal is safe.
			continue
		}
		dst, src := siteWeb[site{ins, ins.Defs[0], true}], siteWeb[site{ins, ins.Uses[0], false}]
		if dst == nil || src == nil || dst == src || dst.Pinned {
			continue
		}
		if len(dst.Defs) != 1 || len(dst.Uses) == 0 {
			continue
		}
		if dst.Reg.Class != src.Reg.Class || !copySafe(ins, dst, src) {
			continue
		}
		ok := true
		for _, u := range dst.Uses {
			if u.Access.Implicit || u.Instr == ins {
				ok = false
				break
			}
			if len(src.Defs) == 1 {
				// The source must still hold its one definition at the
				// read: another web of the register (a call's result, a
				// later assignment) ends its range before that.
				if !src.liveAt(usePos(u.Instr)) {
					ok = false
					break
				}
				continue
			}
			// A source defined more than once (a loop-carried value, a
			// promoted slot written each round) still holds the copied
			// value at a read in the copy's own block that nothing between
			// the two redefines.
			if !f.holdsBetween(src.Reg, ins, u.Instr) {
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
		// Refresh the lifted accesses for the next analysis.
		for _, u := range dst.Uses {
			for k := range u.Instr.Uses {
				if u.Instr.Uses[k] == u.Access {
					u.Instr.Uses[k].Reg = src.Reg
				}
			}
		}
		// Keep the original single-copy order and fixpoint bound.
		return dst
	}
	return nil
}

// holdsBetween reports that register r, read by the copy at from, is
// not written between from and to: to follows from in the same block, and
// no instruction strictly between them defines r (explicitly or as a
// call's clobber).
func (f *Function) holdsBetween(r Reg, from, to *Instr) bool {
	if from.Block == nil || from.Block != to.Block || to.Index <= from.Index {
		return false
	}
	for i := from.Index + 1; i < to.Index; i++ {
		ins := f.Instrs[i]
		if ins.Call {
			return false
		}
		for _, d := range ins.Defs {
			if d.Reg == r {
				return false
			}
		}
	}
	return true
}

// eliminateDead removes the instructions whose every definition no one
// reads, when the instruction is pure on this lane: no store, call,
// branch, compare, atomic, or system effect, and no load from anywhere
// but the frame. copyDst, if non-nil, is the single-definition destination
// whose every read propagateCopy just transferred to its source.
func (f *Function) eliminateDead(webs []*Web, copyDst *Web) int {
	live := map[site]bool{}
	for _, w := range webs {
		if w == copyDst || len(w.Uses) == 0 {
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
