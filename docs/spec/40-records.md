# Records and Structs

Oak deliberately separates **semantic record/product meaning** from **runtime struct representation**.

This distinction is foundational: a type should be usable for checking, constraints, proofs, schemas and tooling without accidentally committing to byte layout, while systems code must still be able to state and verify exact storage representation when needed.

## 1. Records are semantic products

A record describes a finite named product:

```oak
XY: type = {
  x: f32
  y: f32
}
```

A value satisfying this record meaning has an `x` value of type `f32` and a `y` value of type `f32`.

The abstract semantic shape is about **member identity and member types**. It does not imply byte offsets, padding, packing, total size, ABI classification, or field alignment.

Named record declarations are nominal in ordinary value positions. Two named records do not become interchangeable merely because they have the same semantic members.

## 2. Source order is preserved, but is not shape identity

The compiler preserves declaration order exactly:

```oak
HeaderShape: type = {
  kind: u8
  len:  u16
  flags: u8
}
```

Preserved source order is useful to:

- formatting and source fidelity;
- generated documentation;
- debugger/UI display;
- schema projections;
- deterministic representation derivation when a representation policy chooses declaration order.

However, source order is **not itself structural shape compatibility**. A field-shape constraint asks whether the required named members/types exist, not whether another type happened to spell them in the same order.

The compiler may never reconstruct source order from an unordered map.

## 3. Record shapes can describe compile-time interfaces

A semantic record can be used as a structural field requirement in a constraint position once shape constraints are implemented:

```oak
XY: type = {
  x: f32
  y: f32
}

fn length2[T: XY](value: T): f32
  value.x * value.x + value.y * value.y
```

This means that `T` must provide fields compatible with `x: f32` and `y: f32`.

It does **not** mean:

- `T` has the same runtime offsets as `XY`;
- a `T` value is boxed into an `XY` object;
- a vtable exists;
- all record types participate in global width subtyping.

Shape satisfaction belongs to the constraint/type axis and should be erased by specialization just like ordinary static interface constraints.

Method constraints and field-shape constraints should share one compile-time constraint framework where possible; Oak should not invent a separate runtime object model merely to express interfaces.

## 4. Structs select concrete storage representation

`struct` is the representation-bearing product form:

```oak
Point: type = struct {
  x: f32
  y: f32
}
```

`Point` has record/product semantics **plus** a selected runtime representation policy.

Plain `struct` selects Oak's **natural ordered** representation profile:

- declaration order is layout-significant;
- each field is placed at an aligned non-overlapping offset;
- field storage uses the field's already-established machine size/alignment;
- record alignment is the maximum field alignment (1 for an empty struct);
- total size is tail-padded to record alignment.

Selecting `struct` does not mean all numeric layout facts are immediately known. Primitive/field representations may still depend on the target. The compiler therefore distinguishes:

```text
semantic record known
representation policy selected
representation fully resolved
```

These are three different states.

## 5. Record and struct are not synonyms

These declarations intentionally mean different things:

```oak
Shape: type = {
  x: u8
  y: u32
}

Stored: type = struct {
  x: u8
  y: u32
}
```

`Shape` states semantic members only.

`Stored` additionally states that runtime storage follows the ordinary struct representation policy.

Both can have the same semantic member set. That does not collapse their nominal identities, and it does not make the representation choice part of `Shape`.

This is the earlier Oak distinction between the **type layer** and the **layout layer**, made explicit in the modern Semantic IR.

## 6. Natural ordered representation

Oak defines a target-independent natural ordered record-layout primitive for a representation policy that has already selected ordinary non-packed struct storage.

Its inputs are:

- the authoritative ordered field sequence;
- an already-established machine size for each field;
- a non-zero power-of-two alignment for each field.

The following is **specification pseudocode, not Oak source syntax**. It does not introduce `for`, `place`, `align_up`, or mutable assignment as Oak language constructs.

```text
cursor = 0
record_alignment = 1

for field in source_order:
    offset = align_up(cursor, field.alignment)
    place field at offset
    cursor = offset + field.size
    record_alignment = max(record_alignment, field.alignment)

record_size = align_up(cursor, record_alignment)
```

Required laws:

- field order is unchanged;
- each field offset is divisible by that field's alignment;
- ordinary fields do not overlap;
- zero-sized fields consume no bytes but may still carry alignment;
- record alignment is the maximum field alignment, or 1 for an empty struct;
- final size is rounded up to record alignment;
- narrowing into fixed-width representation metadata is checked for overflow.

This algorithm is not a claim that every target ABI uses this layout. Packed records, explicit offsets, overlays/unions, vector ABI rules, platform-specific aggregate classification, wire layouts, and FFI layouts are separate representation policies.

The Semantic IR implementation is `NaturalRecordLayout` in `semir/layout.go`.

## 7. Explicit representation variants

Future representation forms should extend the representation axis rather than changing record semantics.

Examples of policies we may need:

```text
natural struct
packed struct
extern/C struct
explicit offsets
bit fields
wire/network layout
persistent/on-disk layout
vector/SIMD layout
```

Exact surface syntax for those policies is intentionally not frozen yet. The important semantic rule is that a representation choice is explicit and independently checkable.

A future separate representation declaration may allow one semantic type to be related to a specialized physical form. Such a feature must define and verify the conversion/refinement relation rather than assuming semantic fields and physical fields are identical.

## 8. Construction

Named construction uses the semantic type:

```oak
p := Point { x: 1, y: 2 }
```

Construction braces do not choose layout. The type's representation policy does.

Field order in a literal need not match declaration order if every field is named and the compiler proves an unambiguous mapping. Runtime storage follows the resolved representation of `Point`, not literal spelling order.

Duplicate fields are errors. Missing required fields are errors unless a separately specified construction-default rule supplies them.

## 9. Defaults

A field default, if supported, means only a construction default:

```oak
Config: type = {
  retries: u8 = 3
}
```

It does not affect field offset, wire encoding, database schema, or UI metadata unless a separate projection explicitly consumes it.

The same rule applies to struct-backed types: default construction semantics and representation semantics are separate axes.

## 10. Record composition

Definition-time composition forms a new semantic record from existing components:

```oak
Point3: type = Point2 & { z: i32 }
```

This means “compose these semantic members into the definition of `Point3`.”

It does not imply:

```text
Point3 <= Point2
```

and does not introduce general width subtyping.

Duplicate field names are accepted only if their semantic types and correctness-critical semantic attributes agree exactly. Otherwise composition fails.

Representation does not automatically compose with semantic record composition. If the resulting type needs concrete storage, its representation must be selected/resolved independently.

## 11. Empty records, empty structs, and Unit

An empty semantic record has one value and zero members. It has the same semantic cardinality as Unit, but named types remain nominally distinct.

An empty natural struct has zero data bytes and alignment 1 in the natural representation profile.

The canonical procedure-like return spelling is `()`.

Named empty marker types are useful as phantom tags even when a selected runtime representation is zero-sized.

## 12. Metadata

Field metadata is not part of the runtime record/struct value unless a projection explicitly requests it.

A field may carry compile-time attributes such as serializer field numbers, DB names, units, debugger labels, or documentation, but those facts live in the metadata axis.

Correctness-critical representation properties must use typed representation constructs rather than arbitrary string-valued tags.

## 13. Borrowing and fields

Borrowing a field preserves ownership/aliasing facts about the containing storage.

A view/span of a field or subrange cannot manufacture an independent owner. Derived borrows retain provenance to the owning object/region.

For a semantic shape constraint, field access is resolved against the concrete specialized type before executable lowering; the constraint itself does not contain runtime storage.

The exact borrow rules are specified in `50-borrowing.md`.

## 14. Formal verification targets

Semantic-record proof targets:

- field-name uniqueness;
- structural shape satisfaction depends on required names/types, not layout offsets;
- record composition is deterministic;
- incompatible duplicate fields are rejected;
- field lookup returns the member associated with that name.

Struct-representation proof targets:

- selected natural representation preserves declaration order;
- every placed field satisfies its alignment;
- ordinary placed fields do not overlap;
- final size satisfies struct alignment;
- overflow is rejected rather than wrapped;
- a resolved representation corresponds to the selected representation policy.

`spec/lean/Oak/RecordLayout.lean` models the unbounded arithmetic core of natural ordered struct layout. Fixed-width overflow checks remain executable implementation obligations until an explicit refinement connects Go representation widths to the Lean model.

The semantic record proof must not assume a specific ABI. ABI-specific theorems belong to representation/backend models.
