package semir

import "testing"

// Every placement in the shared table is a legal field of the natural
// layout: a non-zero power-of-two alignment that divides the size, and the
// vectors are the 16-byte lane arrays at their lane's alignment.
func TestFieldRepresentationsAreWellFormed(t *testing.T) {
	for name, rep := range FieldRepresentations {
		if rep.Alignment == 0 || !isPowerOfTwo(rep.Alignment) {
			t.Errorf("%s: alignment %d is not a non-zero power of two", name, rep.Alignment)
		}
		if rep.Size == 0 || rep.Size%rep.Alignment != 0 {
			t.Errorf("%s: size %d is not a positive multiple of alignment %d", name, rep.Size, rep.Alignment)
		}
		if rep.Name != "" {
			t.Errorf("%s: the table entry carries a field name %q", name, rep.Name)
		}
	}
	for vector, lane := range map[string]string{"simd.U8x16": "u8", "simd.U16x8": "u16", "simd.U32x4": "u32", "simd.U64x2": "u64", "simd.F32x4": "f32", "simd.F64x2": "f64"} {
		rep, ok := FieldRepresentations[vector]
		if !ok || rep.Size != 16 || rep.Alignment != FieldRepresentations[lane].Alignment {
			t.Errorf("%s: want 16 bytes at %s's alignment, got %+v", vector, lane, rep)
		}
	}
	if rep, ok := FieldRepresentationOf("count", "u32"); !ok || rep.Name != "count" || rep.Size != 4 {
		t.Errorf("FieldRepresentationOf(count, u32) = %+v, %v", rep, ok)
	}
	if _, ok := FieldRepresentationOf("s", "string"); ok {
		t.Errorf("a string has no field placement")
	}
	// A record over every primitive places under the natural layout.
	fields := make([]RecordFieldRepresentation, 0, len(FieldRepresentations))
	for name := range FieldRepresentations {
		rep, _ := FieldRepresentationOf(name, name)
		fields = append(fields, rep)
	}
	if _, err := NaturalRecordLayout(fields); err != nil {
		t.Fatalf("natural layout over the table: %v", err)
	}
}
