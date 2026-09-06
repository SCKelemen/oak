package borrowchecker

// This file holds the pure region decision procedures. Each function is
// maintained as a line-for-line transliteration of its Lean counterpart in
// spec/lean/Oak/ReborrowRefinement.lean, which proves the procedures decide
// exactly the abstract laws of Oak.BorrowRegions and Oak.Reborrow.Split on
// the compiler's representable inputs, failing closed everywhere else.

const maxRegionInt64 = int64(^uint64(0) >> 1)

// regionEnd validates a known region and returns its exclusive end. Malformed
// or overflowing regions are never trusted by alias analysis.
func regionEnd(region *Region) (int64, bool) {
	if region == nil || region.Offset < 0 || region.Length < 0 {
		return 0, false
	}
	if region.Length > maxRegionInt64-region.Offset {
		return 0, false
	}
	return region.Offset + region.Length, true
}

// deriveRegion converts a region relative to parent into an exact absolute
// owner region. It fails closed when either input is unknown, malformed,
// outside the parent, or offset addition would overflow int64.
func deriveRegion(parent, relative *Region) (*Region, bool) {
	if parent == nil || relative == nil {
		return nil, false
	}
	if _, ok := regionEnd(parent); !ok {
		return nil, false
	}
	if relative.Offset < 0 || relative.Length < 0 || relative.Offset > parent.Length {
		return nil, false
	}
	if relative.Length > parent.Length-relative.Offset {
		return nil, false
	}
	if relative.Offset > maxRegionInt64-parent.Offset {
		return nil, false
	}

	derived := &Region{Offset: parent.Offset + relative.Offset, Length: relative.Length}
	if _, ok := regionEnd(derived); !ok {
		return nil, false
	}
	return derived, true
}

// regionsOverlap reports whether two regions may overlap. Unknown (nil) and
// malformed or overflowing regions conservatively overlap everything;
// zero-length regions overlap nothing. Transliteration of
// Oak.ReborrowRefinement.regionsOverlap, which proves the result is false
// exactly when Oak.BorrowRegions.Disjoint holds for validated known regions.
func regionsOverlap(r1, r2 *Region) bool {
	if r1 == nil || r2 == nil {
		return true
	}
	if r1.Offset < 0 || r1.Length < 0 || r2.Offset < 0 || r2.Length < 0 {
		return true
	}
	if r1.Length == 0 || r2.Length == 0 {
		return false
	}
	end1, ok1 := regionEnd(r1)
	end2, ok2 := regionEnd(r2)
	if !ok1 || !ok2 {
		return true
	}
	return r1.Offset < end2 && r2.Offset < end1
}

// admitReborrow decides whether a new writable child with region newRegion
// may join the live sibling reborrows of one parent span, returning the index
// of the first conflicting sibling and false when it may not. Transliteration
// of Oak.ReborrowRefinement.admitReborrow, proven equivalent to the abstract
// admission law Oak.Reborrow.Split.admits on known validated regions and
// fail-closed when the candidate or any live sibling region is unknown.
func admitReborrow(siblingRegions []*Region, newRegion *Region) (int, bool) {
	for i, sibling := range siblingRegions {
		if regionsOverlap(newRegion, sibling) {
			return i, false
		}
	}
	return -1, true
}
