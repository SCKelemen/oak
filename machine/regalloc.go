package machine

import (
	"fmt"
	"sort"

	"github.com/SCKelemen/oak/asm"
)

// Allocation is what reallocation did to a body.
type Allocation struct {
	Webs []*Web
	// Promoted counts the frame slots moved into registers (Promote);
	// Propagated the copies whose reads moved to their source and
	// Eliminated the dead instructions removed (Simplify); Hoisted the
	// loop invariants moved to their preheaders (HoistInvariants); Renamed
	// the webs that changed register; Coalesced the copies removed because
	// their source and destination share a register.
	Promoted, Propagated, Eliminated, Hoisted, Renamed, Coalesced int
	// Pool lists the registers allocation may use: the ones the lowering
	// already wrote (so every callee-saved one among them is saved and
	// restored by the prologue and epilogue as emitted).
	Pool map[Reg]bool
}

// Reallocate lifts an AArch64 body, builds its webs, and recolors the
// webs nothing pins with a linear scan over their live ranges: a web
// takes the register a copy partner already holds when that register is
// free over its range (so the copy becomes a no-op and is removed), else
// its own, else the lowest free register of the pool. Ranges crossing a
// call take callee-saved registers only, and a wide vector web never
// v8–v15 across a call. The pool is the registers the lowering wrote, so
// the frame, the prologue, and the epilogue stand as emitted. A body the
// lift refuses, or a web that finds no register, is an error: the caller
// keeps the body it had.
//
// The result is a new function value with the rewritten items and the
// clobbers it needs; the input is not modified.
func Reallocate(fn *asm.Function) (*asm.Function, *Allocation, error) {
	promotedFn, promoted, err := Promote(fn)
	if err != nil {
		return nil, nil, err
	}
	lifted, err := Lift(promotedFn)
	if err != nil {
		return nil, nil, err
	}
	propagated, eliminated, err := lifted.Simplify()
	if err != nil {
		return nil, nil, err
	}
	hoisted, err := lifted.HoistInvariants()
	if err != nil {
		return nil, nil, err
	}
	if hoisted > 0 {
		// Hoisting may leave copies to propagate and dead code behind.
		p, e, serr := lifted.Simplify()
		if serr != nil {
			return nil, nil, serr
		}
		propagated, eliminated = propagated+p, eliminated+e
	}
	webs, err := lifted.Webs()
	if err != nil {
		return nil, nil, err
	}
	lifted.Liveness(webs)
	t := lifted.t
	alloc := &Allocation{Webs: webs, Pool: map[Reg]bool{}, Promoted: promoted, Propagated: propagated, Eliminated: eliminated, Hoisted: hoisted}
	for _, ins := range lifted.Instrs {
		for _, d := range ins.Defs {
			if !d.Implicit && !t.reserved(d.Reg) {
				alloc.Pool[d.Reg] = true
			}
		}
	}
	// The caller-saved registers the body leaves alone are free for
	// ranges that cross no call (allocation declares what it writes).
	for _, r := range t.callerSaved {
		alloc.Pool[r] = true
	}
	// A web that finds no register keeps its own — pinned — and allocation
	// starts over, so at worst every web keeps the lowering's coloring.
	for {
		err := allocate(lifted, webs, alloc)
		if err == nil {
			break
		}
		stuck, ok := err.(*uncolorable)
		if !ok {
			return nil, nil, err
		}
		stuck.web.Pinned, stuck.web.Why = true, "no other register is free over its range"
		for _, w := range webs {
			w.Colored, w.Assigned = false, Reg{}
		}
	}
	// Rewrite the registers and drop the copies that became no-ops.
	webAt := map[site]*Web{}
	for _, w := range webs {
		for _, d := range w.Defs {
			if d.Instr != nil {
				webAt[site{d.Instr, d.Access, true}] = w
			}
		}
		for _, u := range w.Uses {
			webAt[site{u.Instr, u.Access, false}] = w
		}
		if w.Assigned != w.Reg {
			alloc.Renamed++
		}
	}
	for _, ins := range lifted.Instrs {
		for _, d := range ins.Defs {
			if d.Implicit {
				continue
			}
			if w := webAt[site{ins, d, true}]; w != nil {
				t.setRegAt(&ins.Asm, d, w.Assigned)
			}
		}
		for _, u := range ins.Uses {
			if u.Implicit {
				continue
			}
			if w := webAt[site{ins, u, false}]; w != nil {
				t.setRegAt(&ins.Asm, u, w.Assigned)
			}
		}
	}
	for _, b := range lifted.Blocks {
		kept := b.Instrs[:0]
		for _, ins := range b.Instrs {
			if ins.Copy {
				dst, src := webAt[site{ins, ins.Defs[0], true}], webAt[site{ins, ins.Uses[0], false}]
				if dst != nil && src != nil && dst.Assigned == src.Assigned && copySafe(ins, dst, src) {
					alloc.Coalesced++
					continue
				}
			}
			kept = append(kept, ins)
		}
		b.Instrs = kept
	}
	out := lifted.Asm
	out.Items = lifted.Items()
	// Every register the body now writes is declared: the lowering's
	// clobbers, plus any caller-saved register allocation newly used.
	declared := map[Reg]bool{}
	for _, c := range out.Clobbers {
		if r, _, _, ok, err := t.regOf(c); err == nil && ok {
			declared[r] = true
		}
	}
	for _, ins := range lifted.Instrs {
		for _, d := range ins.Defs {
			if d.Implicit {
				continue
			}
			w := webAt[site{ins, d, true}]
			if w == nil || declared[w.Assigned] || t.calleeSaved(w.Assigned) || t.reserved(w.Assigned) {
				continue
			}
			declared[w.Assigned] = true
			out.Clobbers = append(out.Clobbers, t.clobber(w.Assigned))
		}
	}
	return out, alloc, nil
}

// copySafe reports whether removing a copy whose webs share a register
// preserves the value: a copy narrower than the source's widest write
// would have truncated (a w move zeroes the upper half), and a copy
// narrower than the destination's widest read would have supplied the
// zeroed upper part.
func copySafe(ins *Instr, dst, src *Web) bool {
	return src.DefBits <= ins.CopyBits || dst.UseBits <= ins.CopyBits
}

// allocate colors the webs.
func allocate(f *Function, webs []*Web, alloc *Allocation) error {
	// Calls, for the crossing test.
	var calls []int
	for _, ins := range f.Instrs {
		if ins.Call {
			calls = append(calls, defPos(ins))
		}
	}
	crossesCall := func(w *Web) bool {
		for _, c := range calls {
			if w.crosses(c) {
				return true
			}
		}
		return false
	}
	// Copy partners, for the hints.
	partners := map[*Web][]*Web{}
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
		if !ins.Copy {
			continue
		}
		dst, src := siteWeb[site{ins, ins.Defs[0], true}], siteWeb[site{ins, ins.Uses[0], false}]
		if dst == nil || src == nil || dst == src || !copySafe(ins, dst, src) {
			continue
		}
		partners[dst] = append(partners[dst], src)
		partners[src] = append(partners[src], dst)
	}
	// Assigned ranges per register.
	assigned := map[Reg][]*Web{}
	free := func(r Reg, w *Web) bool {
		for _, other := range assigned[r] {
			if overlaps(other, w) {
				return false
			}
		}
		return true
	}
	// Pinned webs first: they keep their registers. Two pinned webs on one
	// register with overlapping hulls means the hull is coarser than the
	// lowering's real ranges; the lift stands aside.
	var open []*Web
	for _, w := range webs {
		if w.From < 0 {
			// Never live: no definition reaches a use, and no use. It keeps
			// its register and occupies nothing.
			w.Assigned, w.Colored = w.Reg, true
			continue
		}
		if !w.Pinned {
			open = append(open, w)
			continue
		}
		if !free(w.Reg, w) {
			return fmt.Errorf("machine: pinned webs of %s overlap (%s)", w.Reg, w.Why)
		}
		w.Assigned, w.Colored = w.Reg, true
		assigned[w.Reg] = append(assigned[w.Reg], w)
	}
	sort.SliceStable(open, func(i, j int) bool { return open[i].From < open[j].From })
	pool := make([]Reg, 0, len(alloc.Pool))
	for r := range alloc.Pool {
		pool = append(pool, r)
	}
	sort.Slice(pool, func(i, j int) bool {
		if pool[i].Class != pool[j].Class {
			return pool[i].Class < pool[j].Class
		}
		return pool[i].Num < pool[j].Num
	})
	t := f.t
	admissible := func(r Reg, w *Web) bool {
		if r.Class != w.Reg.Class || t.reserved(r) {
			return false
		}
		if crossesCall(w) && (!t.calleeSaved(r) || w.Wide) {
			// Across a call only a callee-saved register, and never one
			// whose preserved part is narrower than the value (v8–v15 keep
			// 64 bits).
			return false
		}
		return free(r, w)
	}
	for _, w := range open {
		chosen, ok := Reg{}, false
		// A copy partner's register, so the copy goes away.
		for _, p := range partners[w] {
			if !p.Colored {
				continue
			}
			if r := p.Assigned; (alloc.Pool[r] || r == w.Reg) && admissible(r, w) {
				chosen, ok = r, true
				break
			}
		}
		// Its own register.
		if !ok && admissible(w.Reg, w) {
			chosen, ok = w.Reg, true
		}
		// The lowest free register of the pool.
		for _, r := range pool {
			if ok {
				break
			}
			if admissible(r, w) {
				chosen, ok = r, true
			}
		}
		if !ok {
			return &uncolorable{w}
		}
		w.Assigned, w.Colored = chosen, true
		assigned[chosen] = append(assigned[chosen], w)
	}
	return nil
}

func itoa(n int) string { return fmt.Sprintf("%d", n) }

// cloneFunction copies a function so the lift may rewrite its items.
func cloneFunction(fn *asm.Function) *asm.Function {
	out := *fn
	out.Items = make([]asm.Item, len(fn.Items))
	for i, item := range fn.Items {
		if ins, ok := item.(asm.Instruction); ok {
			ins.Operands = append([]asm.Operand(nil), ins.Operands...)
			item = ins
		}
		out.Items[i] = item
	}
	out.Clobbers = append([]asm.Register(nil), fn.Clobbers...)
	return &out
}

// uncolorable is allocation's report that a web found no register.
type uncolorable struct{ web *Web }

func (u *uncolorable) Error() string {
	return fmt.Sprintf("machine: no register for the web of %s at positions %d–%d", u.web.Reg, u.web.From, u.web.To)
}

// Sites is how many sites reallocation changed in all.
func (a *Allocation) Sites() int {
	return a.Promoted + a.Propagated + a.Eliminated + a.Hoisted + a.Renamed + a.Coalesced
}
