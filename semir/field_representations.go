package semir

// FieldRepresentations is the size and alignment of every primitive a record
// field may hold, on the recorded LP64 target model — the one authority
// both backends read when they place a record: the C emitter
// (codegen/records.go), whose emitted sizeof/offsetof/_Alignof assertions
// make the C compiler ratify each number, and the native lane
// (nativegen), which must lay the same record out the same way to address
// the C emitter's structs. A primitive missing here has no placement and a
// record holding it fails closed. The table is a representation fact, not
// a property of any record type: the placement policy a record selects
// (docs/spec/40-records.md sections 4, 6, 6a) consumes it.
//
//   - Fixed-width integers (docs/spec/20-types.md section 11) at their
//     width; `u128` is unsigned __int128 on every LP64 ABI Oak targets,
//     16 bytes at 16.
//   - `byte` and `rune` are their integer carriers.
//   - `Bool` lowers to a C enum, int-sized on the recorded ILP32/LP64
//     target model (docs/spec/92-ffi.md section 2.4).
//   - Floating point (section 11.3.1): IEEE binary32 and binary64 at their
//     natural alignment; the f16/bf16 storage formats in uint16_t
//     carriers and the f8 formats in uint8_t (section 11.3.8).
//   - The fixed 128-bit vectors (docs/spec/93-simd.md sections 1.1, 1.2a)
//     are their lane arrays — the `struct { T lanes[N]; }` the C backend
//     emits for every realization — 16 bytes at the lane's alignment.
var FieldRepresentations = map[string]RecordFieldRepresentation{
	"u8": {Size: 1, Alignment: 1}, "i8": {Size: 1, Alignment: 1},
	"u16": {Size: 2, Alignment: 2}, "i16": {Size: 2, Alignment: 2},
	"u32": {Size: 4, Alignment: 4}, "i32": {Size: 4, Alignment: 4},
	"u64": {Size: 8, Alignment: 8}, "i64": {Size: 8, Alignment: 8},
	"u128": {Size: 16, Alignment: 16},
	"byte": {Size: 1, Alignment: 1}, "rune": {Size: 4, Alignment: 4},
	"Bool": {Size: 4, Alignment: 4},
	"f32":  {Size: 4, Alignment: 4}, "f64": {Size: 8, Alignment: 8},
	"f16": {Size: 2, Alignment: 2}, "bf16": {Size: 2, Alignment: 2},
	"f8e4m3": {Size: 1, Alignment: 1}, "f8e5m2": {Size: 1, Alignment: 1},
	"simd.U8x16": {Size: 16, Alignment: 1}, "simd.U16x8": {Size: 16, Alignment: 2},
	"simd.U32x4": {Size: 16, Alignment: 4}, "simd.U64x2": {Size: 16, Alignment: 8},
	"simd.F32x4": {Size: 16, Alignment: 4}, "simd.F64x2": {Size: 16, Alignment: 8},
}

// FieldRepresentationOf is the placement of a primitive field type by name,
// with the field's name filled in; ok is false for a type with no placement.
func FieldRepresentationOf(field, typeName string) (rep RecordFieldRepresentation, ok bool) {
	rep, ok = FieldRepresentations[typeName]
	if !ok {
		return RecordFieldRepresentation{}, false
	}
	rep.Name = field
	return rep, true
}
