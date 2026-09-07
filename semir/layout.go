package semir

import "fmt"

// RecordFieldRepresentation is the representation information required to lay
// out one already-typed record field. Semantic field order is authoritative;
// this function does not reorder fields to reduce padding.
type RecordFieldRepresentation struct {
	Name      string
	Size      uint32
	Alignment uint32
}

// NaturalRecordLayout computes the target-independent natural ordered layout
// used when a backend has selected ordinary non-packed struct representation.
//
// Rules:
//   - fields remain in semantic/source order;
//   - every field begins at an address divisible by its alignment;
//   - fields do not overlap;
//   - record alignment is the maximum field alignment (1 for an empty record);
//   - record size is rounded up to record alignment;
//   - all arithmetic is checked before narrowing into Semantic IR's uint32
//     representation fields.
//
// This is a representation primitive, not an ABI claim. A target ABI may choose
// a different explicit representation policy before calling backend lowering.
//
// The checked placement loop and final-size check are maintained as
// transliterations of Oak.RecordLayoutRefinement
// (spec/lean/Oak/RecordLayoutRefinement.lean), which proves that whenever
// they succeed they compute exactly the abstract placement of
// Oak.RecordLayout — so order/identity preservation, per-field alignment,
// non-overlap, and aligned final size transfer verbatim — and that every
// accepted offset, end, and size fits uint32 (narrowing is lossless;
// overflow can only fail, never truncate).
func NaturalRecordLayout(fields []RecordFieldRepresentation) (Representation, error) {
	representation := Representation{
		Kind:      RepresentationRecord,
		Policy:    RepresentationPolicyNaturalOrdered,
		Resolved:  true,
		Alignment: 1,
		Fields:    make([]FieldLayout, 0, len(fields)),
	}

	seen := make(map[string]struct{}, len(fields))
	cursor := uint64(0)
	maxAlignment := uint32(1)
	const maxUint32 = uint64(^uint32(0))

	for _, field := range fields {
		if field.Name == "" {
			return Representation{}, fmt.Errorf("record layout field has empty name")
		}
		if _, exists := seen[field.Name]; exists {
			return Representation{}, fmt.Errorf("record layout has duplicate field %q", field.Name)
		}
		seen[field.Name] = struct{}{}

		if field.Alignment == 0 || !isPowerOfTwo(field.Alignment) {
			return Representation{}, fmt.Errorf(
				"record field %q alignment %d is not a non-zero power of two",
				field.Name,
				field.Alignment,
			)
		}
		if field.Alignment > maxAlignment {
			maxAlignment = field.Alignment
		}

		offset := alignUp64(cursor, uint64(field.Alignment))
		if offset > maxUint32 {
			return Representation{}, fmt.Errorf("record field %q offset overflows uint32", field.Name)
		}
		end := offset + uint64(field.Size)
		if end > maxUint32 {
			return Representation{}, fmt.Errorf("record field %q end offset overflows uint32", field.Name)
		}

		representation.Fields = append(representation.Fields, FieldLayout{
			Name:   field.Name,
			Offset: uint32(offset),
			Size:   field.Size,
		})
		cursor = end
	}

	finalSize := alignUp64(cursor, uint64(maxAlignment))
	if finalSize > maxUint32 {
		return Representation{}, fmt.Errorf("record size overflows uint32")
	}
	representation.Size = uint32(finalSize)
	representation.Alignment = maxAlignment
	return representation, nil
}

// RecordLayoutSpec is the source-declared layout discipline of one record:
// Packed places fields densely (no inter-field or tail padding beyond the
// explicit alignment), and Align raises the record's alignment above its
// natural alignment. Align == 0 means natural. Under-alignment of a
// non-packed record is rejected: lowering alignment without removing
// padding has no coherent meaning — packing is the way down.
type RecordLayoutSpec struct {
	Packed bool
	Align  uint32
}

// Natural reports the default spec: ordered fields, natural padding.
func (s RecordLayoutSpec) Natural() bool {
	return !s.Packed && s.Align == 0
}

// RecordLayoutWithSpec computes the ordered layout under an explicit layout
// spec. The packed placement loop and the alignment-raising step are
// maintained as transliterations of Oak.LayoutSpec
// (spec/lean/Oak/LayoutSpec.lean): packed placement is dense (each offset is
// the sum of the preceding sizes, hence non-overlapping and order-preserving),
// and raising the record alignment leaves every field offset unchanged while
// keeping the final size divisible by the raised alignment. All arithmetic is
// checked in uint64 before narrowing to uint32 — overflow can only fail,
// never truncate.
func RecordLayoutWithSpec(fields []RecordFieldRepresentation, spec RecordLayoutSpec) (Representation, error) {
	if spec.Align != 0 && !isPowerOfTwo(spec.Align) {
		return Representation{}, fmt.Errorf("record alignment %d is not a power of two", spec.Align)
	}
	if spec.Natural() {
		return NaturalRecordLayout(fields)
	}
	const maxUint32 = uint64(^uint32(0))

	if !spec.Packed {
		// Natural placement with raised alignment: offsets are the natural
		// offsets; only record alignment and tail padding change.
		layout, err := NaturalRecordLayout(fields)
		if err != nil {
			return Representation{}, err
		}
		if spec.Align < layout.Alignment {
			return Representation{}, fmt.Errorf(
				"record alignment %d is below the natural alignment %d; packing, not under-alignment, removes padding",
				spec.Align, layout.Alignment,
			)
		}
		finalSize := alignUp64(uint64(layout.Size), uint64(spec.Align))
		if finalSize > maxUint32 {
			return Representation{}, fmt.Errorf("aligned record size overflows uint32")
		}
		layout.Size = uint32(finalSize)
		layout.Alignment = spec.Align
		return layout, nil
	}

	// Packed placement: every offset is the running sum of field sizes.
	representation := Representation{
		Kind:      RepresentationRecord,
		Policy:    RepresentationPolicyNaturalOrdered,
		Resolved:  true,
		Alignment: 1,
		Fields:    make([]FieldLayout, 0, len(fields)),
	}
	seen := make(map[string]struct{}, len(fields))
	cursor := uint64(0)
	for _, field := range fields {
		if field.Name == "" {
			return Representation{}, fmt.Errorf("record layout field has empty name")
		}
		if _, exists := seen[field.Name]; exists {
			return Representation{}, fmt.Errorf("record layout has duplicate field %q", field.Name)
		}
		seen[field.Name] = struct{}{}
		end := cursor + uint64(field.Size)
		if end > maxUint32 {
			return Representation{}, fmt.Errorf("record field %q end offset overflows uint32", field.Name)
		}
		representation.Fields = append(representation.Fields, FieldLayout{
			Name:   field.Name,
			Offset: uint32(cursor),
			Size:   field.Size,
		})
		cursor = end
	}
	alignment := uint64(1)
	if spec.Align != 0 {
		alignment = uint64(spec.Align)
	}
	finalSize := alignUp64(cursor, alignment)
	if finalSize > maxUint32 {
		return Representation{}, fmt.Errorf("packed record size overflows uint32")
	}
	representation.Size = uint32(finalSize)
	representation.Alignment = uint32(alignment)
	return representation, nil
}

// alignUp64 rounds value upward to a power-of-two alignment. Callers validate
// the alignment before use. Values entering record layout are uint32-bounded,
// so uint64 intermediates leave enough headroom for the addition.
func alignUp64(value, alignment uint64) uint64 {
	mask := alignment - 1
	return (value + mask) &^ mask
}
