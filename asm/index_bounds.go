package asm

// indexBounds is an inclusive unsigned interval. It describes values of a
// term, not an allocation or a promised span extent. Unknown is [0, mask].
// In particular, a guard, a parameter name, and an unchecked subslice length
// never grant a bound. Local owners and derived-span roots remain the memory
// lowering's responsibility.
type indexBounds struct{ lo, hi uint64 }

func (a indexBounds) disjoint(b indexBounds) bool {
	return a.hi < b.lo || b.hi < a.lo
}

// boundsAt adapts the native-width interval just as the bitvector evaluator
// adapts an operand. A truncation that might wrap loses the interval; known
// bits can still bound its low word. Memo entries always use native widths.
func boundsAt(t *term, width int, memo map[*term]indexBounds) indexBounds {
	b := termBounds(t, memo)
	if b.hi <= mask(width) {
		return b
	}
	v, k := adaptKnown(t, width)
	return indexBounds{v & k, (v & k) | (mask(width) &^ k)}
}

func termBounds(t *term, memo map[*term]indexBounds) indexBounds {
	if b, ok := memo[t]; ok {
		return b
	}
	m := mask(t.width)
	v, k := knownBits(t)
	b := indexBounds{v & k, (v & k) | (m &^ k)}
	var refined indexBounds
	refine := false
	switch t.kind {
	case termIte:
		l, r := boundsAt(t.left, t.width, memo), boundsAt(t.right, t.width, memo)
		refined, refine = indexBounds{min(l.lo, r.lo), max(l.hi, r.hi)}, true
	case termBinary:
		if t.op == "add" || t.op == "sub" {
			l, r := boundsAt(t.left, t.width, memo), boundsAt(t.right, t.width, memo)
			switch {
			case t.op == "add" && l.hi <= m-r.hi:
				// Subtraction in the precondition also avoids host uint64 overflow.
				refined, refine = indexBounds{l.lo + r.lo, l.hi + r.hi}, true
			case t.op == "sub" && l.lo >= r.hi:
				refined, refine = indexBounds{l.lo - r.hi, l.hi - r.lo}, true
			}
		}
	}
	if refine {
		b.lo, b.hi = max(b.lo, refined.lo), min(b.hi, refined.hi)
	}
	memo[t] = b
	return b
}
