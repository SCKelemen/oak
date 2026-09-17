package nativegen

import "github.com/SCKelemen/oak/ast"

// arrayDeclarationStorage extends the existing named-record result slot
// to aligned integer arrays. returnSlotLocal has already required a unique
// top-level local, returned by name, whose address never escapes. The ABI's
// result area is therefore the local's storage, as for records; callers
// retain the existing by-value argument and assignment snapshot rules.
// Other arrays keep their ordinary frame allocation.
func (g *generator) arrayDeclarationStorage(name string, elem scalar, length int64) *arrayLocal {
	if !g.rvLane && name != "" && name == g.returnSlot && g.resultIndirect && g.resultRecord != nil && length > 0 {
		switch elem.name {
		case "u32", "u64", "i32", "i64":
			layout := g.arrayLayout(elem, length)
			// Whole eight-byte units make zero initialization exact even
			// at the result area's end: no frame padding is written there.
			// Stay within the existing direct-frame lowering's extent;
			// oversized arrays do not acquire new result-offset paths.
			if layout == g.resultRecord && layout.size > 16 && layout.size <= 4080 && layout.size%8 == 0 && !g.arrayResultReassigned(name) {
				return &arrayLocal{elem: elem, length: length, inReg: true, reg: g.resultAreaReg}
			}
		}
	}
	return g.allocArray(elem, length)
}

// arrayResultReassigned keeps whole-array replacements in frame storage.
// In particular, selfPermutation's cycle lowering currently requires a
// frame array; selecting the result area must not disable that optimization.
// Element stores do not replace the array and remain eligible.
func (g *generator) arrayResultReassigned(name string) bool {
	if g.fn == nil || g.fn.Body == nil {
		return true
	}
	assigned := false
	walk(g.fn.Body, func(n ast.Node) {
		if assignment, ok := n.(*ast.AssignmentStatement); ok && assignment.Name != nil && assignment.Name.Value == name {
			assigned = true
		}
	})
	return assigned
}
