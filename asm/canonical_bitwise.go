package asm

// canonicalBitwise gives fixed rotates and packed-word extractions the
// spelling used by the Oak lowering. These are value identities only: no
// memory access, instruction, or effect is admitted by this normalization.
// The already-canonical children stay shared, including through a hash's
// rounds; expanding their trees would make a small DAG exponentially large.
// Oak.BitwiseCanonical proves the algebra; it is not a refinement of this
// Go implementation or of the caller's source/architectural semantics.
func canonicalBitwise(t, left, right *term) *term {
	if left == nil || right == nil || left.width != t.width || right.width != t.width {
		return nil
	}
	if t.op == "and" && right.kind == termConst && left.kind == termBinary && left.op == "and" && left.right != nil && left.right.width == t.width && left.right.kind == termConst && left.right.value == right.value {
		return left // repeated masks at one width are idempotent
	}
	if (t.op == "shl" || t.op == "shr" || t.op == "sar") && t.width > 0 && t.width <= 64 && right.kind == termConst && right.value%uint64(t.width) == 0 {
		return left // shift counts wrap modulo the operation's width
	}
	if t.op == "ror" && (t.width == 32 || t.width == 64) && right.kind == termConst {
		// These are the two widths modeled by evalBinaryExtra's rotate.
		k := right.value % uint64(t.width)
		if k == 0 {
			return left
		}
		return binaryTerm("or", binaryTerm("shr", left, constTerm(k, t.width)),
			binaryTerm("shl", left, constTerm(uint64(t.width)-k, t.width)))
	}
	if t.op != "shr" || t.width <= 1 || t.width > 64 || right.kind != termConst || right.value == 0 || right.value >= uint64(t.width) || left.kind != termBinary || left.op != "or" {
		return nil
	}
	k := int(right.value)
	for _, pair := range [][2]*term{{left.left, left.right}, {left.right, left.left}} {
		lo, shifted := pair[0], pair[1]
		if lo == nil || shifted == nil || lo.width != t.width || shifted.width != t.width || shifted.kind != termBinary || shifted.op != "shl" || shifted.left == nil || shifted.right == nil || shifted.left.width != t.width || shifted.right.width != t.width || shifted.right.kind != termConst || shifted.right.value != right.value {
			continue
		}
		if significantBits(lo) > k {
			continue // an overlapping low operand contributes to the result
		}
		// ((lo | (hi << k)) >> k) = hi & mask(w-k), when lo < 2^k.
		if significantBits(shifted.left) <= t.width-k {
			return shifted.left // the mask preserves every significant bit
		}
		// Keep the explicit mask even for a parameter: narrowing and then
		// widening a parameter can recover its original declared width.
		return binaryTerm("and", shifted.left, constTerm(mask(t.width-k), t.width))
	}
	return nil
}
