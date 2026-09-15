package machine

// Dominators and natural loops over the lifted control-flow graph
// (docs/notes/optimizer-search-2026-09.md §10.2, Phase C): the
// dominator tree by the iterative algorithm of Cooper, Harvey, and
// Kennedy over a reverse postorder, and the loops its back edges define.
// Both are analyses; nothing here changes a body.

// Dominance is the dominator tree of a function.
type Dominance struct {
	f     *Function
	idom  []int // immediate dominator by block index; -1 for the entry and unreachable blocks
	order []int // reverse postorder of the reachable blocks, by index
	rpo   []int // position in the reverse postorder, -1 for unreachable blocks
}

// Dominators computes the dominator tree.
func (f *Function) Dominators() *Dominance {
	n := len(f.Blocks)
	d := &Dominance{f: f, idom: make([]int, n), rpo: make([]int, n)}
	for i := range d.idom {
		d.idom[i], d.rpo[i] = -1, -1
	}
	if n == 0 {
		return d
	}
	// Reverse postorder from the entry.
	visited := make([]bool, n)
	var post []int
	var visit func(b *Block)
	visit = func(b *Block) {
		visited[b.Index] = true
		for _, s := range b.Succs {
			if !visited[s.Index] {
				visit(s)
			}
		}
		post = append(post, b.Index)
	}
	visit(f.Blocks[0])
	for i := len(post) - 1; i >= 0; i-- {
		d.rpo[post[i]] = len(d.order)
		d.order = append(d.order, post[i])
	}
	d.idom[0] = 0
	intersect := func(a, b int) int {
		for a != b {
			for d.rpo[a] > d.rpo[b] {
				a = d.idom[a]
			}
			for d.rpo[b] > d.rpo[a] {
				b = d.idom[b]
			}
		}
		return a
	}
	for changed, iter := true, 0; changed && iter <= n+1; iter++ {
		changed = false
		for _, bi := range d.order[1:] {
			b := f.Blocks[bi]
			newIdom := -1
			for _, p := range b.Preds {
				if d.rpo[p.Index] < 0 || d.idom[p.Index] < 0 {
					continue // unreachable, or not yet processed
				}
				if newIdom < 0 {
					newIdom = p.Index
				} else {
					newIdom = intersect(p.Index, newIdom)
				}
			}
			if newIdom >= 0 && d.idom[bi] != newIdom {
				d.idom[bi] = newIdom
				changed = true
			}
		}
	}
	d.idom[0] = -1
	return d
}

// Idom is the immediate dominator of a block, nil for the entry and for
// blocks the flow never reaches.
func (d *Dominance) Idom(b *Block) *Block {
	if b == nil || d.idom[b.Index] < 0 {
		return nil
	}
	return d.f.Blocks[d.idom[b.Index]]
}

// Reachable reports whether the flow reaches the block from the entry.
func (d *Dominance) Reachable(b *Block) bool { return b != nil && d.rpo[b.Index] >= 0 }

// Dominates reports whether a dominates b (every block dominates itself).
func (d *Dominance) Dominates(a, b *Block) bool {
	if a == nil || b == nil || !d.Reachable(a) || !d.Reachable(b) {
		return false
	}
	for x := b; x != nil; x = d.Idom(x) {
		if x == a {
			return true
		}
		if d.idom[x.Index] < 0 {
			break
		}
	}
	return false
}

// DominatesInstr reports whether instruction a dominates instruction b:
// a's block dominates b's, and within one block a comes first.
func (d *Dominance) DominatesInstr(a, b *Instr) bool {
	if a.Block == b.Block {
		return a.Index <= b.Index
	}
	return d.Dominates(a.Block, b.Block)
}

// Loop is a natural loop: its header, the latches (blocks with a back
// edge to the header), its blocks, and the unique preheader when the
// header has exactly one predecessor outside the loop.
type Loop struct {
	Header    *Block
	Latches   []*Block
	Blocks    []*Block
	Preheader *Block
	// Depth is the nesting depth: 1 for an outermost loop.
	Depth  int
	Parent *Loop
}

// Contains reports whether the block is in the loop.
func (l *Loop) Contains(b *Block) bool {
	for _, x := range l.Blocks {
		if x == b {
			return true
		}
	}
	return false
}

// Loops finds the natural loops: one per header, from the back edges
// (an edge whose target dominates its source), outermost first, with
// nesting depths and parents.
func (d *Dominance) Loops() []*Loop {
	byHeader := map[*Block]*Loop{}
	var loops []*Loop
	for _, b := range d.f.Blocks {
		if !d.Reachable(b) {
			continue
		}
		for _, s := range b.Succs {
			if !d.Dominates(s, b) {
				continue
			}
			l := byHeader[s]
			if l == nil {
				l = &Loop{Header: s, Blocks: []*Block{s}}
				byHeader[s] = l
				loops = append(loops, l)
			}
			l.Latches = append(l.Latches, b)
			// The body: everything that reaches the latch without passing
			// the header.
			in := map[*Block]bool{s: true}
			for _, x := range l.Blocks {
				in[x] = true
			}
			stack := []*Block{b}
			for len(stack) > 0 && len(in) <= len(d.f.Blocks) {
				x := stack[len(stack)-1]
				stack = stack[:len(stack)-1]
				if in[x] {
					continue
				}
				in[x] = true
				l.Blocks = append(l.Blocks, x)
				for _, p := range x.Preds {
					if !in[p] {
						stack = append(stack, p)
					}
				}
			}
		}
	}
	for _, l := range loops {
		for _, p := range l.Header.Preds {
			if !l.Contains(p) {
				if l.Preheader != nil {
					l.Preheader = nil
					break
				}
				l.Preheader = p
			}
		}
	}
	// Nesting: a loop's parent is the smallest other loop containing its
	// header.
	for _, l := range loops {
		for _, other := range loops {
			if other == l || !other.Contains(l.Header) || len(other.Blocks) <= len(l.Blocks) {
				continue
			}
			if l.Parent == nil || len(other.Blocks) < len(l.Parent.Blocks) {
				l.Parent = other
			}
		}
	}
	for _, l := range loops {
		l.Depth = 1
		for p := l.Parent; p != nil && l.Depth <= len(loops); p = p.Parent {
			l.Depth++
		}
	}
	// Outermost first, then by header order.
	for i := 1; i < len(loops); i++ {
		for j := i; j > 0 && (loops[j].Depth < loops[j-1].Depth || (loops[j].Depth == loops[j-1].Depth && loops[j].Header.Index < loops[j-1].Header.Index)); j-- {
			loops[j], loops[j-1] = loops[j-1], loops[j]
		}
	}
	return loops
}
