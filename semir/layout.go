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

// alignUp64 rounds value upward to a power-of-two alignment. Callers validate
// the alignment before use. Values entering record layout are uint32-bounded,
// so uint64 intermediates leave enough headroom for the addition.
func alignUp64(value, alignment uint64) uint64 {
	mask := alignment - 1
	return (value + mask) &^ mask
}
