# Records

Records are Oak's product types.

## 1. Product semantics

```oak
Point: type = {
  x: i32
  y: i32
}
```

A `Point` value contains one `i32` value for `x` and one for `y`.

Named record declarations are nominal types. Two records with the same fields are not interchangeable merely because their shapes match.

## 2. Field order

Source field order is preserved as semantic input.

```oak
Header: type = {
  kind: u8
  len:  u16
  flags: u8
}
```

The compiler may not reconstruct this order from an unordered map.

Preserved order may be consumed by:

- an ABI/layout projection;
- serialization schemas;
- debugger/UI display;
- documentation;
- reflection/metadata tooling.

Preserved order does not itself determine byte offsets.

## 3. Representation is separate

Record meaning and record ABI are separate axes.

A target representation pass determines:

- field offsets;
- field alignment;
- record alignment;
- padding;
- total size;
- packing/ABI rules.

A type-level record may therefore be known before its exact machine layout is known.

The compiler must fail closed when a backend requires a representation fact that has not been established.

### 3.1 Natural ordered representation

Oak defines a small target-independent **natural ordered** record-layout primitive for backends or ABI profiles that select ordinary non-packed product representation.

Its inputs are the authoritative ordered field sequence plus an already-established machine size and non-zero power-of-two alignment for each field. It does not infer field machine representation.

For fields `f[0..n)`:

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
- record alignment is the maximum field alignment, or 1 for an empty record;
- final size is rounded up to record alignment;
- narrowing into fixed-width representation metadata must be checked for overflow.

This algorithm is not a claim that every target ABI uses this layout. Packed records, explicit offsets, overlays/unions, vector ABI rules, or platform-specific aggregate classification are separate representation policies. A backend must select an applicable policy explicitly rather than silently changing this primitive.

The Semantic IR implementation is `NaturalRecordLayout` in `semir/layout.go`.

## 4. Construction

Canonical named construction:

```oak
p := Point { x: 1, y: 2 }
```

Field order in a literal need not be the same as declaration order if every field is named and the language can prove the mapping unambiguously. The resulting runtime layout follows the type's representation, not literal spelling order.

Duplicate fields are errors. Missing required fields are errors unless a separately specified field-default rule supplies them.

## 5. Defaults

A field default, if supported, means only a construction default:

```oak
Config: type = {
  retries: u8 = 3
}
```

It does not affect field offset, wire encoding, database schema, or UI metadata unless a separate projection explicitly uses it.

## 6. Record composition

Definition-time composition may form a new nominal record from existing record components:

```oak
Point3: type = Point2 & { z: i32 }
```

This means “compose these fields into the definition of `Point3`.”

It does not imply:

```text
Point3 <= Point2
```

and does not introduce general width subtyping.

Composition flattens the field sequence in component order.

Duplicate field names are accepted only if their semantic type and correctness-critical attributes agree exactly. Otherwise composition fails.

## 7. Shape constraints

General structural record subtyping is not core Oak.

If a future API needs “has at least these fields,” that should be expressed as an explicit shape/interface constraint feature rather than silently making all records structurally subtype one another.

This preserves nominal identity and predictable layout while still leaving room for local structural constraints.

## 8. Empty records and Unit

An empty record has one value and zero fields. It may share the same semantic cardinality/representation as Unit.

The canonical language spelling for procedure-like return values is `()`.

Named empty marker types remain nominally useful as phantom tags even if their runtime representation is zero-sized.

## 9. Metadata

Field metadata is not part of the runtime record value unless a projection explicitly requests it.

A field may carry compile-time attributes such as serializer field numbers, DB names, units, debugger labels, or documentation, but those facts live in the metadata axis.

Correctness-critical representation properties should use typed representation constructs rather than arbitrary string-valued tags.

## 10. Borrowing and fields

Borrowing a field must preserve ownership/aliasing facts about the containing storage.

A view/span of a field or subrange cannot manufacture an independent owner. Derived borrows retain provenance to the owning object/region.

The exact borrow rules are specified in `50-borrowing.md`.

## 11. Formal verification targets

Initial proof targets:

- field-name uniqueness after composition;
- composition preserves declared source order;
- compatible composition is deterministic;
- incompatible duplicate fields are rejected;
- field lookup returns the field associated with that name;
- natural ordered layout preserves field identity/order;
- natural ordered layout gives non-overlapping ordinary fields;
- every natural-layout field offset satisfies its alignment;
- final natural-layout size satisfies record alignment and covers the final field cursor.

`spec/lean/Oak/RecordLayout.lean` models the unbounded arithmetic core of the natural ordered layout. Fixed-width overflow checks remain executable implementation obligations until an explicit refinement connects the Go representation widths to the Lean model.

The semantic record proof should not assume that all targets use the natural profile. ABI-specific layout theorems belong to their representation/backend models.
