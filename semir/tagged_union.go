package semir

import "fmt"

// TaggedUnionTagSize is the width of a tagged union's discriminant in the
// emitted C: a fixed-width u32 holding the variant's declaration index
// (docs/spec/92-ffi.md section 2.6). Fixing the width is what gives the
// union one meaning on both sides of the C boundary; a C enum's width is
// implementation-defined.
const TaggedUnionTagSize uint32 = 4

// TaggedUnionLayout computes the representation of a tagged union as the C
// backend emits it: the u32 tag, then a union of every payload.
//
// The union's alignment is the largest payload alignment and its size the
// largest payload size rounded up to that alignment (C11 6.7.2.1: every
// member starts at offset 0; the union is large enough for its largest
// member and aligned for its strictest). The struct around tag and union is
// the natural ordered record layout of those two fields, so every guarantee
// of NaturalRecordLayout (Oak.RecordLayoutRefinement) carries over; a
// tagged union without payloads is the tag alone. The result's Fields are
// "tag" and, when payloads exist, "payload".
func TaggedUnionLayout(payloads []RecordFieldRepresentation) (Representation, error) {
	fields := []RecordFieldRepresentation{{Name: "tag", Size: TaggedUnionTagSize, Alignment: TaggedUnionTagSize}}
	if len(payloads) > 0 {
		union, err := unionRepresentation(payloads)
		if err != nil {
			return Representation{}, err
		}
		fields = append(fields, RecordFieldRepresentation{Name: "payload", Size: union.Size, Alignment: union.Alignment})
	}
	layout, err := NaturalRecordLayout(fields)
	if err != nil {
		return Representation{}, err
	}
	layout.Kind = RepresentationTaggedUnion
	layout.Tag = &TagLayout{Bits: uint16(TaggedUnionTagSize * 8), Offset: 0}
	return layout, nil
}

// unionRepresentation is the size and alignment of a C union over the
// members: the strictest alignment, and the largest size rounded up to it.
func unionRepresentation(members []RecordFieldRepresentation) (Representation, error) {
	const maxUint32 = uint64(^uint32(0))
	alignment := uint32(1)
	size := uint64(0)
	for _, member := range members {
		if member.Alignment == 0 || !isPowerOfTwo(member.Alignment) {
			return Representation{}, fmt.Errorf("union member %q has invalid alignment %d", member.Name, member.Alignment)
		}
		if member.Alignment > alignment {
			alignment = member.Alignment
		}
		if uint64(member.Size) > size {
			size = uint64(member.Size)
		}
	}
	size = alignUp64(size, uint64(alignment))
	if size > maxUint32 {
		return Representation{}, fmt.Errorf("union size %d exceeds uint32", size)
	}
	return Representation{Kind: RepresentationOpaque, Resolved: true, Size: uint32(size), Alignment: alignment}, nil
}
