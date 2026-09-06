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
