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
	// Per instruction, the webs it defines and uses.
	defW := map[*Instr][]*Web{}
	useW := map[*Instr][]*Web{}
	for _, w := range webs {
		for _, d := range w.Defs {
			if d.Instr != nil {
				defW[d.Instr] = append(defW[d.Instr], w)
			}
		}
		for _, u := range w.Uses {
			useW[u.Instr] = append(useW[u.Instr], w)
		}
	}
	// Block gen (upward-exposed uses) and kill (definitions).
	n := len(f.Blocks)
	gen := make([]map[*Web]bool, n)
	kill := make([]map[*Web]bool, n)
	for i, b := range f.Blocks {
		gen[i], kill[i] = map[*Web]bool{}, map[*Web]bool{}
		for _, ins := range b.Instrs {
			for _, w := range useW[ins] {
				if !kill[i][w] {
					gen[i][w] = true
				}
			}
			for _, w := range defW[ins] {
				kill[i][w] = true
			}
		}
	}
	liveIn = make([]map[*Web]bool, n)
	liveOut = make([]map[*Web]bool, n)
	for i := range f.Blocks {
		liveIn[i], liveOut[i] = map[*Web]bool{}, map[*Web]bool{}
	}
	for changed := true; changed; {
		changed = false
		for i := n - 1; i >= 0; i-- {
			b := f.Blocks[i]
			out := map[*Web]bool{}
			for _, s := range b.Succs {
				for w := range liveIn[s.Index] {
					out[w] = true
				}
			}
			in := map[*Web]bool{}
			for w := range gen[i] {
				in[w] = true
			}
			for w := range out {
				if !kill[i][w] {
					in[w] = true
				}
			}
			if len(in) != len(liveIn[i]) || len(out) != len(liveOut[i]) {
				changed = true
			} else {
				for w := range in {
					if !liveIn[i][w] {
						changed = true
						break
					}
				}
			}
			liveIn[i], liveOut[i] = in, out
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
	for i, b := range f.Blocks {
		if len(b.Instrs) == 0 {
			continue
		}
		end := map[*Web]int{}
		last := defPos(b.Instrs[len(b.Instrs)-1])
		for w := range liveOut[i] {
			end[w] = last
		}
		for k := len(b.Instrs) - 1; k >= 0; k-- {
			ins := b.Instrs[k]
			for _, w := range defW[ins] {
				if to, live := end[w]; live {
					add(w, defPos(ins), to)
					delete(end, w)
				} else {
					add(w, defPos(ins), defPos(ins)) // a dead definition
				}
			}
			for _, w := range useW[ins] {
				if _, live := end[w]; !live {
					end[w] = usePos(ins)
				}
			}
		}
		start := usePos(b.Instrs[0])
		for w, to := range end {
			add(w, start, to)
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
