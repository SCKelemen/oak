package semir

import "testing"

// The tagged-union layout is the u32 tag followed by the widest, strictest
// payload: the shape a C caller reading `e.tag` and `e.payload.X` relies on
// (docs/spec/92-ffi.md section 2.6).
func TestTaggedUnionLayout(t *testing.T) {
	cases := []struct {
		name          string
		payloads      []RecordFieldRepresentation
		size, align   uint32
		payloadOffset uint32
	}{
		{"no payload", nil, 4, 4, 0},
		{"u32 and u8", []RecordFieldRepresentation{{Name: "Send", Size: 4, Alignment: 4}, {Name: "Yield", Size: 1, Alignment: 1}}, 8, 4, 4},
		{"u64 and u8", []RecordFieldRepresentation{{Name: "A", Size: 8, Alignment: 8}, {Name: "B", Size: 1, Alignment: 1}}, 16, 8, 8},
		{"three bytes", []RecordFieldRepresentation{{Name: "Bytes", Size: 3, Alignment: 1}}, 8, 4, 4},
		{"u16 pair", []RecordFieldRepresentation{{Name: "Lo", Size: 2, Alignment: 2}, {Name: "Hi", Size: 2, Alignment: 2}}, 8, 4, 4},
	}
	for _, c := range cases {
		layout, err := TaggedUnionLayout(c.payloads)
		if err != nil {
			t.Fatalf("%s: %v", c.name, err)
		}
		if layout.Kind != RepresentationTaggedUnion || layout.Size != c.size || layout.Alignment != c.align {
			t.Fatalf("%s: got kind=%s size=%d align=%d, want size=%d align=%d", c.name, layout.Kind, layout.Size, layout.Alignment, c.size, c.align)
		}
		if layout.Tag == nil || layout.Tag.Bits != 32 || layout.Tag.Offset != 0 {
			t.Fatalf("%s: tag layout %+v, want 32 bits at offset 0", c.name, layout.Tag)
		}
		if len(c.payloads) == 0 {
			if len(layout.Fields) != 1 {
				t.Fatalf("%s: fields %+v, want the tag alone", c.name, layout.Fields)
			}
			continue
		}
		if len(layout.Fields) != 2 || layout.Fields[1].Name != "payload" || layout.Fields[1].Offset != c.payloadOffset {
			t.Fatalf("%s: fields %+v, want payload at %d", c.name, layout.Fields, c.payloadOffset)
		}
	}
}

func TestTaggedUnionLayoutRejectsInvalidAlignment(t *testing.T) {
	if _, err := TaggedUnionLayout([]RecordFieldRepresentation{{Name: "X", Size: 4, Alignment: 3}}); err == nil {
		t.Fatal("non power-of-two payload alignment must be rejected")
	}
}
