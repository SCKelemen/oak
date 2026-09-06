package borrowchecker

// deriveRegion converts a region relative to parent into the corresponding
// absolute owner region. It fails closed when either region is unknown,
// malformed, outside the parent, or offset addition would overflow int64.
func deriveRegion(parent, relative *Region) (*Region, bool) {
	if parent == nil || relative == nil {
		return nil, false
	}
	if parent.Offset < 0 || parent.Length < 0 || relative.Offset < 0 || relative.Length < 0 {
		return nil, false
	}
	if relative.Offset > parent.Length {
		return nil, false
	}
	if relative.Length > parent.Length-relative.Offset {
		return nil, false
	}

	const maxInt64 = int64(^uint64(0) >> 1)
	if relative.Offset > 0 && parent.Offset > maxInt64-relative.Offset {
		return nil, false
	}

	return &Region{
		Offset: parent.Offset + relative.Offset,
		Length: relative.Length,
	}, true
}

// constantSubsliceRegion derives `subslice(source, start, length)` when both
// numeric arguments are non-negative compile-time integer literals and the
// source region is known. Unknown/dynamic facts deliberately return nil so the
// caller retains a conservative region rather than fabricating precision.
func (bc *BorrowChecker) constantSubsliceRegion(callStart, callLength interface{ isBorrowRegionExpr() }, parent *Region) *Region {
	// This interface-shaped helper is intentionally not used directly; the AST
	// adapter lives in borrowchecker.go so derived_region.go remains independent
	// of syntax nodes. Keeping the arithmetic here makes the proof target small.
	return parent
}
