package asm

// equalTermsAtDeclaredWidths proves structural equality while allowing
// different views of a parameter that retain the same declared bits.
// Unlike changing the terms' widths, this leaves each enclosing operation's
// modulus and interpretation intact. Each pair of shared nodes is visited
// once; no diagram or expanded expression tree is needed.
func equalTermsAtDeclaredWidths(a, b *term, widthOf func(string) int) bool {
	memo := map[[2]*term]bool{}
	sameWidth := func(x, y *term) bool {
		if x == nil || y == nil {
			return x == y
		}
		return x.width == y.width
	}
	var equal func(*term, *term) bool
	equal = func(a, b *term) bool {
		if a == b {
			return true
		}
		if a == nil || b == nil || a.kind != b.kind || a.name != b.name || a.op != b.op || a.value != b.value {
			return false
		}
		if a.kind == termParam {
			if a.width == b.width {
				return true
			}
			if widthOf == nil || a.width <= 0 || a.width > 64 || b.width <= 0 || b.width > 64 {
				return false
			}
			declared := widthOf(a.name)
			return declared > 0 && declared <= 64 && min(a.width, declared) == min(b.width, declared)
		}
		if a.width != b.width {
			return false
		}
		key := [2]*term{a, b}
		if known, seen := memo[key]; seen {
			return known
		}
		memo[key] = false
		switch a.kind {
		case termQuant:
			// A bound name may shadow a parameter with a different width.
			// The external declaration cannot justify equality in its body.
			memo[key] = equalTerms(a, b)
			return memo[key]
		case termCmp, termFloat:
			// Signed flags and float conversions interpret operand widths,
			// unlike integer binary operations at their own result width.
			if !sameWidth(a.left, b.left) || !sameWidth(a.right, b.right) || !sameWidth(a.cond, b.cond) {
				return false
			}
		}
		result := equal(a.cond, b.cond) && equal(a.left, b.left) && equal(a.right, b.right)
		memo[key] = result
		return result
	}
	return equal(a, b)
}
