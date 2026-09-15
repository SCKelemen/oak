package machine

import (
	"sort"

	"github.com/SCKelemen/oak/asm"
)

// Loop-invariant code motion over the lifted IR
// (docs/notes/optimizer-search-2026-09.md §11 "invariant hoisting", Phase
// C): an instruction inside a loop whose inputs the loop never changes
// computes the same value every trip; when it does nothing but compute
// that value, it moves to the loop's preheader and runs once. The pass
// works on the natural loops of the dominator tree, innermost first, so
// an invariant of an inner loop can climb again with the outer one, and
// it moves one instruction at a time, recomputing the webs and the
// liveness after each move so every decision reads current ranges. The
// checker and the verifier judge the result like any other candidate.

// HoistInvariants moves the loop-invariant instructions of every loop
// into its preheader and reports how many moved.
func (f *Function) HoistInvariants() (int, error) {
	total := 0
	for round := 0; round < 4; round++ {
		moved := 0
		dom := f.Dominators()
		loops := dom.Loops()
		// Innermost first.
		sort.SliceStable(loops, func(i, j int) bool { return loops[i].Depth > loops[j].Depth })
		for _, l := range loops {
			if l.Preheader == nil {
				continue
			}
			for moves := 0; moves < 64; moves++ {
				webs, err := f.Webs()
				if err != nil {
					return total, err
				}
				f.Liveness(webs)
				if !f.hoistOne(l, webs) {
					break
				}
				moved++
			}
		}
		total += moved
		if moved == 0 {
			break
		}
	}
	return total, nil
}

// hoistOne moves the first hoistable instruction of the loop into the
// preheader and reports whether it found one.
func (f *Function) hoistOne(l *Loop, webs []*Web) bool {
	inLoop := map[*Block]bool{}
	for _, b := range l.Blocks {
		inLoop[b] = true
	}
	siteWeb := map[site]*Web{}
	byReg := map[Reg][]*Web{}
	for _, w := range webs {
		for _, d := range w.Defs {
			if d.Instr != nil {
				siteWeb[site{d.Instr, d.Access, true}] = w
			}
		}
		for _, u := range w.Uses {
			siteWeb[site{u.Instr, u.Access, false}] = w
		}
		byReg[w.Reg] = append(byReg[w.Reg], w)
	}
	// What the loop does to memory: a store through sp or a call means a
	// frame load inside it may see a different value each trip.
	frameChanges := false
	for _, b := range l.Blocks {
		for _, ins := range b.Instrs {
			if ins.Call {
				frameChanges = true
			}
			for _, op := range ins.Asm.Operands {
				if m, ok := op.(asm.Memory); ok && m.Base.Class == asm.ClassSP && len(ins.Defs) == 0 {
					frameChanges = true // a store (loads define their register)
				}
			}
		}
	}
	// The insertion point: before the preheader's terminator, and the
	// position a hoisted definition would take.
	pre := l.Preheader
	at := len(pre.Instrs)
	if at > 0 && f.t.terminator(pre.Instrs[at-1].Asm) {
		at--
	}
	var newFrom int
	if at > 0 {
		newFrom = defPos(pre.Instrs[at-1])
	} else if len(l.Header.Instrs) > 0 {
		newFrom = usePos(l.Header.Instrs[0]) - 1
	}
	for _, b := range l.Blocks {
		for k, ins := range b.Instrs {
			if !f.hoistable(ins, l, inLoop, siteWeb, byReg, frameChanges, newFrom) {
				continue
			}
			// Move it.
			b.Instrs = append(b.Instrs[:k], b.Instrs[k+1:]...)
			pre.Instrs = append(pre.Instrs[:at], append([]*Instr{ins}, pre.Instrs[at:]...)...)
			ins.Block = pre
			f.reindex()
			return true
		}
	}
	return false
}

// hoistable decides whether one instruction of the loop may move to the
// preheader.
func (f *Function) hoistable(ins *Instr, l *Loop, inLoop map[*Block]bool, siteWeb map[site]*Web, byReg map[Reg][]*Web, frameChanges bool, newFrom int) bool {
	a := ins.Asm
	if ins.Call || ins.Ret || ins.Trap || ins.Branch || !f.t.pure(a) || f.t.readsFlags(a) {
		return false
	}
	if len(ins.Defs) != 1 || ins.Defs[0].Implicit {
		return false
	}
	w := siteWeb[site{ins, ins.Defs[0], true}]
	if w == nil || w.Pinned || len(w.Defs) != 1 || f.t.reserved(w.Reg) || len(w.Uses) == 0 {
		return false
	}
	// A frame load: only when the loop leaves the frame alone.
	for _, op := range a.Operands {
		if _, ok := op.(asm.Memory); ok && frameChanges {
			return false
		}
	}
	// Every input is defined outside the loop (an entry value, or an
	// instruction of another block), so it is the same every trip.
	for _, u := range ins.Uses {
		if u.Implicit {
			return false
		}
		uw := siteWeb[site{ins, u, false}]
		if uw == nil {
			return false
		}
		for _, d := range uw.Defs {
			if d.Instr != nil && inLoop[d.Instr.Block] {
				return false
			}
		}
	}
	// Moving the definition stretches the web from the preheader to its
	// last use — and, read inside the loop, around every trip, to the
	// loop's end: no other web of the register may be live anywhere in
	// that stretch, or the move would clobber it.
	to := w.To
	for _, b := range l.Blocks {
		if len(b.Instrs) > 0 {
			if end := defPos(b.Instrs[len(b.Instrs)-1]); end > to {
				to = end
			}
		}
	}
	for _, other := range byReg[w.Reg] {
		if other == w {
			continue
		}
		for _, s := range other.Segs {
			if s.from <= to && newFrom <= s.to {
				return false
			}
		}
	}
	return true
}
