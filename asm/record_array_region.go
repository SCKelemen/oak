package asm

// recordArrayField describes one exact, direct u64 array declaration inside a
// nominal record. It carries field bounds, not private-memory authority.
type recordArrayField struct {
	recordName string
	fieldName  string
	recordSize int64
	offset     int64
	size       int64
	length     int64
}

// recordU64ArrayFieldOf resolves the exact field at a proven record-relative
// address. Malformed, ambiguous, overlapping, or variant layouts supply no
// field fact. All arithmetic is checked before multiplication/addition.
func recordU64ArrayFieldOf(composites map[string]Composite, extent region) (recordArrayField, bool) {
	comp, known := composites[extent.record]
	if !known || extent.record == "" || comp.Size <= 0 || comp.Variants != nil ||
		extent.recordOffset < 0 || extent.recordOffset > comp.Size ||
		extent.size != comp.Size-extent.recordOffset {
		return recordArrayField{}, false
	}
	selected := -1
	names := make(map[string]bool, len(comp.Fields))
	for i, field := range comp.Fields {
		if field.Name == "" || names[field.Name] || field.Offset < 0 ||
			field.Offset > comp.Size || field.Size <= 0 || field.Size > comp.Size-field.Offset {
			return recordArrayField{}, false
		}
		names[field.Name] = true
		if field.Offset == extent.recordOffset {
			if selected >= 0 {
				return recordArrayField{}, false
			}
			selected = i
		}
	}
	if selected < 0 {
		return recordArrayField{}, false
	}
	field := comp.Fields[selected]
	if field.Elem != "u64" || field.Scalar != "" || field.Type != "" || field.ElemType != "" {
		return recordArrayField{}, false
	}
	for i, sibling := range comp.Fields {
		// The first pass established both endpoints are inside comp.Size, so
		// these additions cannot overflow int64.
		if i != selected && sibling.Offset < field.Offset+field.Size && field.Offset < sibling.Offset+sibling.Size {
			return recordArrayField{}, false
		}
	}
	out := recordArrayField{recordName: extent.record, fieldName: field.Name,
		recordSize: comp.Size, offset: field.Offset, size: field.Size, length: field.Length}
	if !recordArrayFieldValid(recordPlace{name: extent.record, offset: extent.recordOffset}, extent, out) {
		return recordArrayField{}, false
	}
	return out, true
}

// recordArrayFieldValid is the geometry projection proved by
// Oak.RecordArrayRegion.validField. The declared-field lookup above separately
// establishes direct-u64 shape, unique name/offset, and absence of overlap.
func recordArrayFieldValid(place recordPlace, extent region, field recordArrayField) bool {
	if place.name == "" || field.recordName != place.name || field.fieldName == "" ||
		field.recordSize <= 0 || place.offset < 0 || place.offset > field.recordSize ||
		extent.size != field.recordSize-place.offset || field.offset != place.offset ||
		field.offset%8 != 0 || field.length <= 0 || field.length > 1<<32 {
		return false
	}
	// The length limit makes the product at most 2^35, safely in int64.
	return field.size == 8*field.length && field.size <= extent.size
}

// recordArrayQuadAdmits is the prospective four-cell bound, kept separate from
// the ordinary byte region. No instruction handler uses this fact as access
// permission. Composition with recordArrayFieldValid proves four adjacent
// cells remain in the selected field and their 32-bit indices do not wrap.
func recordArrayQuadAdmits(field recordArrayField, bound idxFact, stride int64) bool {
	return stride == 8 && bound.boundReg < 0 && !bound.slack && bound.bound > 0 &&
		field.length >= 4 && bound.bound <= field.length-3
}

// narrowRecordArrayRegion only reduces the existing byte extent. Unknown or
// unsupported field layouts retain the checker's original generic behavior;
// they cannot supply an exact field fact or the four-cell proof above.
func narrowRecordArrayRegion(composites map[string]Composite, extent region) region {
	if field, ok := recordU64ArrayFieldOf(composites, extent); ok {
		extent.size = field.size
		// This is now a field extent, not the exact tail of its parent.
		extent.record, extent.recordOffset = "", 0
	}
	return extent
}
