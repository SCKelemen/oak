package asm

// maxValue is an upper bound on a term's value at its width — the mask
// when nothing tighter is known. It is a syntactic bound (constants, masks,
// products and sums by constants, shifts, the wider of a conditional's
// arms), enough to see that a shift count such as `(at % 4) * 8` stays
// below the width, where Oak's trapping shift and the machine's wrapping
// one agree (docs/spec/94-assembler.md §9, twenty-ninth increment).
func maxValue(t *term) uint64 {
	return maxValueMemo(t, map[*term]uint64{})
}

// maxValueDeclared is maxValue with a parameter bounded by its declared
// width rather than the width of the node that mentions it (a Bool loop
// variable zero-extended into a 64-bit register is still at most 1).
func maxValueDeclared(t *term, widthOf func(string) int) uint64 {
	memo := map[*term]uint64{}
	var bound func(t *term) uint64
	bound = func(t *term) uint64 {
		if t.kind == termParam {
			if w := widthOf(t.name); w > 0 && w < t.width {
				return mask(w)
			}
			return mask(t.width)
		}
		if v, seen := memo[t]; seen {
			return v
		}
		v := maxValueOfWith(t, memo, bound)
		memo[t] = v
		return v
	}
	return bound(t)
}

// maxValue is the bound under the lowering's own memo, which every shift
// the lowering meets shares: a count that reads memory written by earlier
// summarized calls is a large DAG, and bounding it afresh at each shift
// was a visible share of a build.
func (lo *oakLowering) maxValue(t *term) uint64 {
	if lo.bounds == nil {
		lo.bounds = map[*term]uint64{}
	}
	return maxValueMemo(t, lo.bounds)
}

// maxValueMemo is maxValue over a term DAG: shared subterms bound once.
func maxValueMemo(t *term, memo map[*term]uint64) uint64 {
	if bound, seen := memo[t]; seen {
		return bound
	}
	bound := maxValueOf(t, memo)
	memo[t] = bound
	return bound
}

func maxValueOf(t *term, memo map[*term]uint64) uint64 {
	return maxValueOfWith(t, memo, func(u *term) uint64 { return maxValueMemo(u, memo) })
}

// maxValueOfWith bounds one node given a bound for its operands.
func maxValueOfWith(t *term, memo map[*term]uint64, sub func(*term) uint64) uint64 {
	m := mask(t.width)
	switch t.kind {
	case termConst:
		return t.value & m
	case termCmp:
		return 1
	case termIte:
		l, r := sub(t.left), sub(t.right)
		if l < r {
			l = r
		}
		if l > m {
			l = m
		}
		return l
	case termBinary:
		l := sub(t.left)
		var r uint64
		if t.right != nil {
			r = sub(t.right)
		}
		switch t.op {
		case "and":
			if l < r {
				return l & m
			}
			return r & m
		case "or", "xor":
			return bitsBound(l|r) & m
		case "add":
			if l+r < l || l+r > m {
				return m
			}
			return l + r
		case "mul":
			if l == 0 || r == 0 {
				return 0
			}
			if l > m/r {
				return m
			}
			return l * r
		case "shl":
			// The count wraps at the width, as the evaluation's does.
			if t.right.kind != termConst {
				return m
			}
			count := t.right.value % uint64(t.width)
			if l > m>>uint(count) {
				return m
			}
			return (l << uint(count)) & m
		case "shr":
			if t.right.kind != termConst {
				return m
			}
			return l >> uint(t.right.value%uint64(t.width))
		case "sub":
			// A remainder by a power of two spelled as a subtraction,
			// `x - (x >> k) << k` or `x - (x >> k) * 2^k` (the machine's
			// `at % 4` before a byte extract's shift count): below 2^k.
			if k, isRemainder := remainderShift(t.left, t.right); isRemainder {
				return mask(k) & m
			}
		}
	}
	return m
}

// remainderShift recognizes `(x >> k) << k` or `(x >> k) * 2^k` over the
// same x as minuend, reporting k.
func remainderShift(x, subtrahend *term) (int, bool) {
	if subtrahend == nil || subtrahend.kind != termBinary || subtrahend.right == nil || subtrahend.right.kind != termConst {
		return 0, false
	}
	var k uint64
	switch subtrahend.op {
	case "shl":
		k = subtrahend.right.value
	case "mul":
		v := subtrahend.right.value
		if v == 0 || v&(v-1) != 0 {
			return 0, false
		}
		for v > 1 {
			v >>= 1
			k++
		}
	default:
		return 0, false
	}
	inner := subtrahend.left
	if inner == nil || inner.kind != termBinary || inner.op != "shr" || inner.right == nil || inner.right.kind != termConst || inner.right.value != k {
		return 0, false
	}
	if k == 0 || k >= 64 || !equalTerms(inner.left, x) {
		return 0, false
	}
	return int(k), true
}

// bitsBound is the all-ones value covering v's highest set bit.
func bitsBound(v uint64) uint64 {
	out := uint64(0)
	for out < v {
		out = out<<1 | 1
	}
	return out
}
