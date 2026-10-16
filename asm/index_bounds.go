package asm

// indexBounds is an inclusive unsigned interval. It describes values of a
// term, not an allocation or a promised span extent. Unknown is [0, mask].
// In particular, a guard, a parameter name, and an unchecked subslice length
// never grant a bound. Local owners and derived-span roots remain the memory
// lowering's responsibility.
type indexBounds struct{ lo, hi uint64 }

// indexBoundsMemo belongs to one memory-read or blaster-consistency pass.
// Both analyses retain DAG sharing without mutating the terms, which other
// variable-order workers may be reading concurrently.
type indexBoundsMemo struct {
	bounds map[*term]indexBounds
	known  knownBitsMemo
}

func newIndexBoundsMemo() *indexBoundsMemo {
	return &indexBoundsMemo{bounds: map[*term]indexBounds{}, known: knownBitsMemo{}}
}

func (a indexBounds) disjoint(b indexBounds) bool {
	return a.hi < b.lo || b.hi < a.lo
}

// boundsAt adapts the native-width interval just as the bitvector evaluator
// adapts an operand. A truncation that might wrap loses the interval; known
// bits can still bound its low word. Memo entries always use native widths.
func boundsAt(t *term, width int, memo *indexBoundsMemo) indexBounds {
	b := termBounds(t, memo)
	if b.hi <= mask(width) {
		return b
	}
	v, k := memo.known.adapt(t, width)
	return indexBounds{v & k, (v & k) | (mask(width) &^ k)}
}

func termBounds(t *term, memo *indexBoundsMemo) indexBounds {
	if b, ok := memo.bounds[t]; ok {
		return b
	}
	m := mask(t.width)
	v, k := memo.known.bits(t)
	b := indexBounds{v & k, (v & k) | (m &^ k)}
	var refined indexBounds
	refine := false
	switch t.kind {
	case termIte:
		l, r := boundsAt(t.left, t.width, memo), boundsAt(t.right, t.width, memo)
		refined, refine = indexBounds{min(l.lo, r.lo), max(l.hi, r.hi)}, true
	case termBinary:
		switch t.op {
		case "add", "sub":
			l, r := boundsAt(t.left, t.width, memo), boundsAt(t.right, t.width, memo)
			switch {
			case t.op == "add" && l.hi <= m-r.hi:
				// Subtraction in the precondition also avoids host uint64 overflow.
				refined, refine = indexBounds{l.lo + r.lo, l.hi + r.hi}, true
			case t.op == "sub" && l.lo >= r.hi:
				refined, refine = indexBounds{l.lo - r.hi, l.hi - r.lo}, true
			}
		case "shl":
			if t.right.kind == termConst {
				shift := t.right.value % uint64(t.width)
				l := boundsAt(t.left, t.width, memo)
				if l.hi <= m>>shift {
					refined, refine = indexBounds{l.lo << shift, l.hi << shift}, true
				}
			}
		case "mul":
			variable, factor := t.left, t.right
			if variable.kind == termConst {
				variable, factor = factor, variable
			}
			if factor.kind == termConst {
				c := factor.value & m
				l := boundsAt(variable, t.width, memo)
				if c == 0 {
					refined, refine = indexBounds{}, true
				} else if l.hi <= m/c {
					refined, refine = indexBounds{l.lo * c, l.hi * c}, true
				}
			}
		}
	}
	if refine {
		b.lo, b.hi = max(b.lo, refined.lo), min(b.hi, refined.hi)
	}
	memo.bounds[t] = b
	return b
}

// boundedIndexSumsDisjoint proves two modular indices unequal after
// cancelling addends they have in common. The remaining addends must each
// have a non-wrapping unsigned sum; disjoint residual intervals then cannot
// denote the same word. This keeps an arbitrary shared base from erasing the
// useful bounds on derived regions:
//
//	base + (x & 255)       base + 256 + (y & 255)
//
// Addition is flattened only at the compared width. A narrower nested add
// wraps before extension and therefore remains one opaque addend.
func boundedIndexSumsDisjoint(a, b *term, width int, memo *indexBoundsMemo) bool {
	if a == nil || b == nil || width < 1 || width > 64 {
		return false
	}
	var leftStorage, rightStorage [boundedIndexAddendLimit]*term
	leftCount, leftOK := flattenBoundedIndexAddends(a, width, &leftStorage, 0)
	rightCount, rightOK := flattenBoundedIndexAddends(b, width, &rightStorage, 0)
	if !leftOK || !rightOK {
		return false
	}
	left, right := leftStorage[:leftCount], rightStorage[:rightCount]
	used := uint64(0)
	var leftRestStorage, rightRestStorage [boundedIndexAddendLimit]*term
	leftRest := leftRestStorage[:0]
	for _, x := range left {
		matched := false
		for j, y := range right {
			if used&(uint64(1)<<uint(j)) != 0 {
				continue
			}
			budget := sameTermBudget
			if x == y || sameTerm(x, y, &budget) {
				used |= uint64(1) << uint(j)
				matched = true
				break
			}
		}
		if !matched {
			leftRest = append(leftRest, x)
		}
	}
	rightRest := rightRestStorage[:0]
	for j, y := range right {
		if used&(uint64(1)<<uint(j)) == 0 {
			rightRest = append(rightRest, y)
		}
	}
	// Without cancellation the whole-term interval check is both cheaper and
	// at least as precise; this helper exists for a shared-base relation.
	if len(leftRest) == len(left) {
		return false
	}
	lb, lok := boundedIndexAddendSum(leftRest, width, memo)
	rb, rok := boundedIndexAddendSum(rightRest, width, memo)
	return lok && rok && lb.disjoint(rb)
}

const boundedIndexAddendLimit = 16

func flattenBoundedIndexAddends(t *term, width int, out *[boundedIndexAddendLimit]*term, n int) (int, bool) {
	if t.kind == termBinary && t.op == "add" && t.width == width {
		var ok bool
		if n, ok = flattenBoundedIndexAddends(t.left, width, out, n); !ok {
			return n, false
		}
		return flattenBoundedIndexAddends(t.right, width, out, n)
	}
	if n == len(out) {
		return n, false
	}
	out[n] = t
	return n + 1, true
}

func boundedIndexAddendSum(terms []*term, width int, memo *indexBoundsMemo) (indexBounds, bool) {
	out := indexBounds{}
	m := mask(width)
	for _, t := range terms {
		part := boundsAt(t, width, memo)
		if out.hi > m-part.hi {
			return indexBounds{}, false
		}
		out.lo += part.lo
		out.hi += part.hi
	}
	return out, true
}
