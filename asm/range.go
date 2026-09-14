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
	m := mask(t.width)
	switch t.kind {
	case termConst:
		return t.value & m
	case termCmp:
		return 1
	case termIte:
		l, r := maxValueMemo(t.left, memo), maxValueMemo(t.right, memo)
		if l < r {
			l = r
		}
		if l > m {
			l = m
		}
		return l
	case termBinary:
		l := maxValueMemo(t.left, memo)
		var r uint64
		if t.right != nil {
			r = maxValueMemo(t.right, memo)
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
			if t.right.kind != termConst || t.right.value >= 64 {
				return m
			}
			if l > m>>uint(t.right.value) {
				return m
			}
			return (l << uint(t.right.value)) & m
		case "shr":
			if t.right.kind != termConst || t.right.value >= 64 {
				return m
			}
			return l >> uint(t.right.value)
		}
	}
	return m
}

// bitsBound is the all-ones value covering v's highest set bit.
func bitsBound(v uint64) uint64 {
	out := uint64(0)
	for out < v {
		out = out<<1 | 1
	}
	return out
}
