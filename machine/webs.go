package machine

import (
	"fmt"
	"slices"
)

// seg is one live range, inclusive of both positions.
type seg struct{ from, to int }

// A web is one virtual register: the set of definitions of one physical
// register that reach a common use, with those uses, joined transitively
// (Briggs). Every web of the lifted body is colored with the physical
// register the lowering chose; allocation may recolor the ones nothing
// pins. Entry webs hold the registers' values at entry — parameters, the
// callee-saved registers the prologue saves — and are pinned.

// site is one definition or use: an instruction and the access in it, or
// the entry pseudo-definition of a register (Instr nil).
type site struct {
	Instr  *Instr
	Access Access
	Def    bool
}

// Web is a virtual register.
type Web struct {
	Index int
	Reg   Reg // the physical register the lowering gave every site
	Defs  []site
	Uses  []site
	// Pinned webs keep their register: they hold a value at entry, cross
	// the procedure-call contract (a call's arguments, results, or
	// clobbers; a return's results), have no use (a clobber or a restore
	// the checker reads as a write), or sit in a reserved register.
	Pinned bool
	Why    string // why the web is pinned, for the report
	// DefBits and UseBits are the widest view any definition writes and
	// any use reads: a copy of fewer bits than either changes the value
	// and cannot be coalesced away.
	DefBits, UseBits int
	// Wide marks a vector web some access views as 128 bits: it does not
	// survive a call in v8–v15.
	Wide bool
	// From and To bound the web's live range in program positions (an
	// instruction i reads at 2i and writes at 2i+1); Segs are the ranges
	// it is live over, whose hull From–To is.
	From, To int
	Segs     []seg
	// Assigned is the register allocation chose, once Colored.
	Assigned Reg
	Colored  bool
}

// Webs builds the def-use webs of the lifted body from reaching
// definitions.
func (f *Function) Webs() ([]*Web, error) {
	// Definition sites: the entry pseudo-definition of every register,
	// then every instruction's definitions.
	var sites []site
	entry := map[Reg]int{}
	addEntry := func(r Reg, bits int) {
		if _, dup := entry[r]; dup {
			return
		}
		entry[r] = len(sites)
		sites = append(sites, site{Access: Access{Reg: r, Bits: bits, Implicit: true}})
	}
	for n := 0; n <= 30; n++ {
		addEntry(Reg{GPR, n}, 64)
	}
	for n := 0; n <= 31; n++ {
		addEntry(Reg{VEC, n}, 128)
	}
	for _, ins := range f.Instrs {
		// Pseudo-registers (frame slots under promotion) hold an unknown
		// at entry too.
		for _, u := range ins.Uses {
			addEntry(u.Reg, u.Bits)
		}
		for _, d := range ins.Defs {
			addEntry(d.Reg, d.Bits)
		}
	}
	defSite := make(map[*Instr]int, len(f.Instrs)) // first definition site per instruction
	for _, ins := range f.Instrs {
		defSite[ins] = len(sites)
		for _, d := range ins.Defs {
			sites = append(sites, site{Instr: ins, Access: d, Def: true})
		}
	}
	// Reaching sets are sorted and immutable. Transfers replace a register's
	// whole set, and joins allocate only when the sets differ. States can
	// therefore share their sets without a deep copy at every block or a
	// singleton allocation at every definition. Simplify rebuilds these webs
	// after each propagated copy, making those allocations particularly costly.
	singletons := make([]int, len(sites))
	for i := range singletons {
		singletons[i] = i
	}
	type rd map[Reg][]int
	clone := func(s rd) rd {
		out := make(rd, len(s))
		for r, set := range s {
			out[r] = set
		}
		return out
	}
	in := make([]rd, len(f.Blocks))
	out := make([]rd, len(f.Blocks))
	through := func(b *Block, state rd) rd {
		state = clone(state)
		for _, ins := range b.Instrs {
			for k, d := range ins.Defs {
				s := defSite[ins] + k
				state[d.Reg] = singletons[s : s+1]
			}
		}
		return state
	}
	for i := range f.Blocks {
		in[i], out[i] = rd{}, rd{}
	}
	changed := true
	for iter := 0; changed; iter++ {
		if iter > 10000 {
			return nil, fmt.Errorf("machine: reaching definitions did not converge")
		}
		changed = false
		for i, b := range f.Blocks {
			merged := rd{}
			if i == 0 || len(b.Preds) == 0 {
				// The entry holds every register's entry value; so, as far
				// as the lift can tell, does a block the flow never
				// reaches. A loop whose header is the entry block merges
				// its back edges below as well.
				for r, s := range entry {
					merged[r] = singletons[s : s+1]
				}
			}
			for _, p := range b.Preds {
				for r, set := range out[p.Index] {
					merged[r] = mergeReachingSites(merged[r], set)
				}
			}
			in[i] = merged
			next := through(b, in[i])
			if !sameRD(next, out[i]) {
				out[i] = next
				changed = true
			}
		}
	}
	// Union-find over sites; each use joins the definitions reaching it.
	parent := make([]int, len(sites))
	for i := range parent {
		parent[i] = i
	}
	var find func(int) int
	find = func(x int) int {
		for parent[x] != x {
			parent[x] = parent[parent[x]]
			x = parent[x]
		}
		return x
	}
	union := func(a, b int) { parent[find(a)] = find(b) }
	useOf := map[int][]site{} // root → uses (filled after unions settle)
	type pendingUse struct {
		s     site
		first int
	}
	var uses []pendingUse
	for i, b := range f.Blocks {
		state := clone(in[i])
		for _, ins := range b.Instrs {
			reaching := map[Access]int{} // a use's operand → one definition reaching it
			for _, u := range ins.Uses {
				set := state[u.Reg]
				if len(set) == 0 {
					// A read of a register nothing defined, not even at
					// entry: the entry set covers every register, so this
					// is a register outside the files.
					return nil, fmt.Errorf("machine: line %d: read of %s with no definition", ins.Asm.Line, u.Reg)
				}
				first := set[0]
				for _, k := range set[1:] {
					union(first, k)
				}
				reaching[u] = first
				uses = append(uses, pendingUse{site{Instr: ins, Access: u}, first})
			}
			for k, d := range ins.Defs {
				// An operand both read and written (an accumulating form, a
				// lane insertion) is one register: its definition joins the
				// web it reads.
				if !d.Implicit {
					if from, ok := reaching[d]; ok {
						union(defSite[ins]+k, from)
					}
				}
				s := defSite[ins] + k
				state[d.Reg] = singletons[s : s+1]
			}
		}
	}
	for _, pu := range uses {
		root := find(pu.first)
		useOf[root] = append(useOf[root], pu.s)
	}
	webOf := map[int]*Web{}
	var webs []*Web
	for i, s := range sites {
		root := find(i)
		w := webOf[root]
		if w == nil {
			w = &Web{Index: len(webs), Reg: s.Access.Reg, From: -1, To: -1}
			webOf[root] = w
			webs = append(webs, w)
		}
		if s.Access.Reg != w.Reg {
			return nil, fmt.Errorf("machine: a web joins %s and %s", s.Access.Reg, w.Reg)
		}
		w.Defs = append(w.Defs, s)
	}
	for root, us := range useOf {
		webOf[root].Uses = append(webOf[root].Uses, us...)
	}
	for _, w := range webs {
		w.pin(f.t)
	}
	return webs, nil
}

// mergeReachingSites returns the sorted union of two immutable sets. Empty
// and equal sets share storage; a changed union owns new storage. In particular,
// append must never use either input as its destination, even with spare capacity.
func mergeReachingSites(a, b []int) []int {
	if len(a) == 0 {
		return b
	}
	if len(b) == 0 || slices.Equal(a, b) {
		return a
	}
	merged := make([]int, 0, len(a)+len(b))
	i, j := 0, 0
	for i < len(a) && j < len(b) {
		switch {
		case a[i] < b[j]:
			merged = append(merged, a[i])
			i++
		case b[j] < a[i]:
			merged = append(merged, b[j])
			j++
		default:
			merged = append(merged, a[i])
			i++
			j++
		}
	}
	merged = append(merged, a[i:]...)
	return append(merged, b[j:]...)
}

func sameRD(a, b map[Reg][]int) bool {
	if len(a) != len(b) {
		return false
	}
	for r, sa := range a {
		sb, ok := b[r]
		if !ok || !slices.Equal(sa, sb) {
			return false
		}
	}
	return true
}

// pin decides whether the web keeps its register, and measures its views.
func (w *Web) pin(t *target) {
	for _, d := range w.Defs {
		if d.Instr == nil {
			w.Pinned, w.Why = true, "holds a value at entry"
		} else if d.Access.Implicit {
			w.Pinned, w.Why = true, "a call's result or clobber"
		}
		if d.Access.Bits > w.DefBits {
			w.DefBits = d.Access.Bits
		}
		if d.Access.Reg.Class == VEC && d.Access.Bits > 64 {
			w.Wide = true
		}
	}
	for _, u := range w.Uses {
		if u.Access.Implicit {
			w.Pinned, w.Why = true, "a call's argument or a return's result"
		}
		if u.Access.Bits > w.UseBits {
			w.UseBits = u.Access.Bits
		}
		if u.Access.Reg.Class == VEC && u.Access.Bits > 64 {
			w.Wide = true
		}
	}
	if len(w.Uses) == 0 && !w.Pinned {
		w.Pinned, w.Why = true, "written and never read (a restore or a clobber)"
	}
	if t.reserved(w.Reg) && !w.Pinned {
		w.Pinned, w.Why = true, "a reserved register"
	}
}

// Has reports whether the web has a definition or use in the instruction.
func (w *Web) has(ins *Instr) bool {
	for _, d := range w.Defs {
		if d.Instr == ins {
			return true
		}
	}
	for _, u := range w.Uses {
		if u.Instr == ins {
			return true
		}
	}
	return false
}
