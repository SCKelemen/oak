package asm

// unsignedSuccessorPremiseLimit bounds the extra guard walk. Repeated nodes
// (including cycles) are refused; missing this shortcut keeps the old decider.
const unsignedSuccessorPremiseLimit = 128

// impliesUnsignedSuccessor recognizes only the ordinary unsigned law
//     k < bound => k + 1 <= bound
// with one fixed width and an unchanged bound. The strict guard excludes wrap.
// Oak.UnsignedSuccessor proves the arithmetic and one-bit conjunction law.
//
// This intentionally uses pointer identity, a sufficient form of structural
// equality, for both k and bound. It never equates parameters or memories by
// name. It runs before canonicalization can copy those shared terms. As with
// the surrounding implication decider, operands are immutable, well-formed
// internal term DAGs; this is not an arbitrary serialized-term validator.
func impliesUnsignedSuccessor(premise, a, b *term) bool {
	if premise == nil || a == nil || b == nil || a.kind != termCmp || a.op != "ls" ||
		a.left == nil || a.right == nil || !unsignedSuccessorBare(a) ||
		b.kind != termConst || b.width != 1 || b.value != 1 || !unsignedSuccessorLeaf(b) {
		return false
	}
	step, bound := a.left, a.right
	if step.kind != termBinary || step.op != "add" || step.left == nil || step.right == nil ||
		!unsignedSuccessorBare(step) {
		return false
	}
	k, one, width := step.left, step.right, step.width
	if width < 1 || width > 64 || k.kind != termParam || k.width != width ||
		k.name == "" || k.op != "" || k.value != 0 || !unsignedSuccessorLeaf(k) ||
		(k.declared != 0 && k.declared != width) || bound.width != width ||
		(a.width != 1 && a.width != width) || one.kind != termConst ||
		one.width != width || one.value != 1 || !unsignedSuccessorLeaf(one) {
		return false
	}
	// A nonzero one-bit AND entails each of its operands. Never descend OR,
	// wider bitwise operations, comparisons, or an arbitrary branch condition.
	pending := []*term{premise}
	seen := map[*term]bool{}
	found := false
	for len(pending) != 0 {
		n := pending[len(pending)-1]
		pending = pending[:len(pending)-1]
		if n == nil || n.width != 1 || seen[n] || len(seen) == unsignedSuccessorPremiseLimit {
			return false
		}
		seen[n] = true
		if n.kind == termBinary && n.op == "and" {
			if n.left == nil || n.right == nil || !unsignedSuccessorBare(n) {
				return false
			}
			pending = append(pending, n.left, n.right)
			continue
		}
		if n.kind == termCmp && n.op == "lo" && n.left == k && n.right == bound &&
			unsignedSuccessorBare(n) {
			found = true
		}
	}
	return found
}

// Unused shape fields cannot smuggle a second interpretation into the
// recognized parameter/constant/add/compare/AND spine.
func unsignedSuccessorBare(t *term) bool {
	return t.cond == nil && len(t.args) == 0 && t.declared == 0 && t.name == "" && t.value == 0
}

func unsignedSuccessorLeaf(t *term) bool {
	return t.left == nil && t.right == nil && t.cond == nil && len(t.args) == 0 &&
		(t.kind == termParam || (t.declared == 0 && t.name == "" && t.op == ""))
}
