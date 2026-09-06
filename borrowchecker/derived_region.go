package borrowchecker

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
