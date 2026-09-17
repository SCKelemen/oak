package machine

// Liveness over webs: which webs are live into and out of each block, and
// each web's live range as the hull of the positions it is live at. An
// instruction at linear index i reads at position 2i and writes at 2i+1,
// so a web that dies in an instruction and one born there never overlap.

// position of an instruction's reads and writes.
func usePos(ins *Instr) int { return 2 * ins.Index }
func defPos(ins *Instr) int { return 2*ins.Index + 1 }

// Liveness computes live-in and live-out per block and fills each web's
// From and To. It returns the live-in sets for inspection.
func (f *Function) Liveness(webs []*Web) (liveIn, liveOut []map[*Web]bool) {
	// The sets are bitsets over the webs' positions in the slice: the
	// simplifier recomputes liveness after every propagated copy, and the
	// maps this held — fresh in and out maps per block per iteration —
	// were half of its time in map assignment. The callers receive the
	// maps they always did, built once at the end.
	position := make(map[*Web]int, len(webs))
	for i, w := range webs {
		position[w] = i
	}
	words := (len(webs) + 63) / 64
	newSet := func() []uint64 { return make([]uint64, words) }
	set := func(s []uint64, i int) { s[i>>6] |= 1 << (uint(i) & 63) }
	has := func(s []uint64, i int) bool { return s[i>>6]&(1<<(uint(i)&63)) != 0 }
	// Per instruction (by its index), the webs it defines and uses.
	defW := make([][]int, len(f.Instrs))
	useW := make([][]int, len(f.Instrs))
	for i, w := range webs {
		for _, d := range w.Defs {
			if d.Instr != nil {
				defW[d.Instr.Index] = append(defW[d.Instr.Index], i)
			}
		}
		for _, u := range w.Uses {
			useW[u.Instr.Index] = append(useW[u.Instr.Index], i)
		}
	}
	// Block gen (upward-exposed uses) and kill (definitions).
	n := len(f.Blocks)
	gen := make([][]uint64, n)
	kill := make([][]uint64, n)
	for i, b := range f.Blocks {
		gen[i], kill[i] = newSet(), newSet()
		for _, ins := range b.Instrs {
			for _, w := range useW[ins.Index] {
				if !has(kill[i], w) {
					set(gen[i], w)
				}
			}
			for _, w := range defW[ins.Index] {
				set(kill[i], w)
			}
		}
	}
	in := make([][]uint64, n)
	out := make([][]uint64, n)
	for i := range f.Blocks {
		in[i], out[i] = newSet(), newSet()
	}
	for changed := true; changed; {
		changed = false
		for i := n - 1; i >= 0; i-- {
			b := f.Blocks[i]
			o := out[i]
			for k := range o {
				o[k] = 0
			}
			for _, s := range b.Succs {
				for k, word := range in[s.Index] {
					o[k] |= word
				}
			}
			for k := range o {
				next := gen[i][k] | (o[k] &^ kill[i][k])
				if next != in[i][k] {
					in[i][k] = next
					changed = true
				}
			}
		}
	}
	// Live ranges: a backward walk of each block from its live-out set
	// closes a segment at every definition and opens one at every use, so
	// a value saved before a call and reloaded after it is not live across
	// the call.
	for _, w := range webs {
		w.From, w.To, w.Segs = -1, -1, nil
	}
	add := func(w *Web, from, to int) {
		w.Segs = append(w.Segs, seg{from, to})
		if w.From < 0 || from < w.From {
			w.From = from
		}
		if to > w.To {
			w.To = to
		}
	}
	end := make([]int, len(webs)) // a live web's position of death in the block; -1 when not live
	for i := range end {
		end[i] = -1
	}
	var touched []int
	for i, b := range f.Blocks {
		if len(b.Instrs) == 0 {
			continue
		}
		touched = touched[:0]
		last := defPos(b.Instrs[len(b.Instrs)-1])
		for w := range webs {
			if has(out[i], w) {
				end[w] = last
				touched = append(touched, w)
			}
		}
		for k := len(b.Instrs) - 1; k >= 0; k-- {
			ins := b.Instrs[k]
			for _, w := range defW[ins.Index] {
				if to := end[w]; to >= 0 {
					add(webs[w], defPos(ins), to)
					end[w] = -1
				} else {
					add(webs[w], defPos(ins), defPos(ins)) // a dead definition
				}
			}
			for _, w := range useW[ins.Index] {
				if end[w] < 0 {
					end[w] = usePos(ins)
					touched = append(touched, w)
				}
			}
		}
		start := usePos(b.Instrs[0])
		for _, w := range touched {
			if to := end[w]; to >= 0 {
				add(webs[w], start, to)
				end[w] = -1
			}
		}
	}
	liveIn = make([]map[*Web]bool, n)
	liveOut = make([]map[*Web]bool, n)
	for i := range f.Blocks {
		liveIn[i], liveOut[i] = map[*Web]bool{}, map[*Web]bool{}
		for w := range webs {
			if has(in[i], w) {
				liveIn[i][webs[w]] = true
			}
			if has(out[i], w) {
				liveOut[i][webs[w]] = true
			}
		}
	}
	// Entry webs hold their register from position 0.
	for _, w := range webs {
		for _, d := range w.Defs {
			if d.Instr == nil && w.From != 0 {
				if w.From < 0 {
					add(w, 0, 0)
				} else {
					add(w, 0, w.From)
				}
			}
		}
	}
	return liveIn, liveOut
}

// overlaps reports whether two live ranges share a position.
func overlaps(a, b *Web) bool {
	for _, x := range a.Segs {
		for _, y := range b.Segs {
			if x.from <= y.to && y.from <= x.to {
				return true
			}
		}
	}
	return false
}

// crosses reports whether the web is live across a definition position:
// live before it and still after it.
func (w *Web) crosses(pos int) bool {
	for _, s := range w.Segs {
		if s.from < pos && pos <= s.to {
			return true
		}
	}
	return false
}

// liveAt reports whether the web is live at a position.
func (w *Web) liveAt(pos int) bool {
	for _, s := range w.Segs {
		if s.from <= pos && pos <= s.to {
			return true
		}
	}
	return false
}
