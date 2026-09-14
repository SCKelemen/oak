package asm

// Structural equality of terms in their low bits: the decision that
// precedes the diagrams in the coupling's obligations and follows their
// budget in the straight-line decider (docs/spec/94-assembler.md §8,
// thirty-first increment). A quotient times a divisor — a 32-bit multiply
// of two unknowns — exceeds every diagram's budget, and is the same term on
// both sides once the quotient is shared.

// termEquivalent reports two terms equal in their low w bits by structure:
// a mask covering those bits is transparent, the operations whose low bits
// depend on their operands' low bits alone (and, or, xor, add, sub, mul)
// recurse at w, a select compares its memory and index, everything else
// must agree exactly. Sound and cheap; it decides what the diagrams cannot
// afford (a 32-bit multiply of two unknowns), which is the common shape of
// a store's value after the coupling's substitution.
func termEquivalent(a, b *term, w int, memo map[[3]any]bool) bool {
	a, b = stripLowMask(a, w), stripLowMask(b, w)
	if a == b {
		return true
	}
	if a == nil || b == nil || a.kind != b.kind {
		return false
	}
	key := [3]any{a, b, w}
	if seen, done := memo[key]; done {
		return seen
	}
	memo[key] = true // a DAG: a pair under comparison is assumed equal while its children are compared
	equal := false
	switch a.kind {
	case termConst:
		equal = a.width >= w && b.width >= w && a.value&mask(w) == b.value&mask(w)
	case termParam:
		equal = a.name == b.name && a.width >= w && b.width >= w
	case termSelect:
		equal = a.name == b.name && a.width == b.width && a.width >= w && termEquivalent(a.left, b.left, 32, memo)
	case termBinary:
		switch a.op {
		case "and", "or", "xor", "add", "sub", "mul":
			equal = a.op == b.op && a.width >= w && b.width >= w && termEquivalent(a.left, b.left, w, memo) && termEquivalent(a.right, b.right, w, memo)
		default:
			equal = a.op == b.op && a.width == b.width && termEquivalent(a.left, b.left, a.width, memo) && termEquivalent(a.right, b.right, a.width, memo)
		}
	case termIte:
		equal = a.width >= w && b.width >= w && termEquivalent(a.cond, b.cond, 1, memo) && termEquivalent(a.left, b.left, w, memo) && termEquivalent(a.right, b.right, w, memo)
	case termCmp:
		equal = a.op == b.op && a.left.width == b.left.width && termEquivalent(a.left, b.left, a.left.width, memo) && termEquivalent(a.right, b.right, a.left.width, memo)
	case termFloat:
		equal = a.op == b.op && a.width == b.width && a.width >= w && termEquivalent(a.left, b.left, widthOrZero(a.left), memo) && termEquivalent(a.right, b.right, widthOrZero(a.right), memo) && termEquivalent(a.cond, b.cond, widthOrZero(a.cond), memo)
	}
	memo[key] = equal
	return equal
}

func widthOrZero(t *term) int {
	if t == nil {
		return 0
	}
	return t.width
}

// stripLowMask drops what leaves the low w bits alone: `t and c` when c
// covers them, and the extension idiom `(t shl k) sar k` / `(t shl k) shr
// k` (the RV64 lane's sext.w and zext) when the low w bits lie below k.
func stripLowMask(t *term, w int) *term {
	for t != nil && t.kind == termBinary {
		if t.op == "and" && t.right != nil && t.right.kind == termConst && t.right.value&mask(w) == mask(w) && t.left != nil {
			t = t.left
			continue
		}
		if (t.op == "sar" || t.op == "shr") && t.right != nil && t.right.kind == termConst && t.left != nil && t.left.kind == termBinary && t.left.op == "shl" && t.left.right != nil && t.left.right.kind == termConst && t.left.right.value == t.right.value && int(t.right.value) <= t.width && w <= t.width-int(t.right.value) && t.left.left != nil {
			t = t.left.left
			continue
		}
		break
	}
	return t
}
