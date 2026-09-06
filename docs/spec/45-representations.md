# Representation Polymorphism

Oak separates **what a value means** from **how one concrete realization stores
that value**.

This document is normative for representation selection and for allowing one
semantic type to admit multiple checked runtime representations.

## 1. Semantic type identity is primary

A semantic record such as:

```oak
Position: type = {
  x: i32
  y: i32
}
```

states named product semantics. It does not choose offsets, padding, field order
in memory, size, alignment, packing, ABI classification, or endianness.

Representation is a separate relation over that semantic type.

## 2. A semantic type may have many representations

A semantic type may have:

- no runtime representation, when it is used only as a compile-time shape,
  proposition, constraint, or other erased concept;
- one representation;
- several named representation choices.

Conceptually:

```text
Position
  ├─ natural-native
  ├─ reversed-explicit
  ├─ packed-wire
  └─ another proved representation
```

The representation names above are specification examples, not Oak surface
syntax.

Two representation choices may have different field order, offsets, padding,
size, alignment, or encoding while preserving the same semantic type identity.

## 3. Selection is explicit and deterministic

A concrete stored value has one selected representation contract at a time.

For a fixed:

```text
semantic type
+ representation choice
+ target facts
```

resolved layout must be deterministic.

The compiler must not arbitrarily choose a different representation because it
looks smaller or faster unless an explicit optimization/representation policy
permits that transformation and its semantic preservation is established.

## 4. `struct` selects a representation

The ordinary form:

```oak
Point: type = struct {
  x: i32
  y: i32
}
```

has record semantics and selects Oak's natural ordered struct representation.

This is equivalent in architecture to:

```text
semantic type: { x: i32, y: i32 }
selected representation policy: natural-ordered
```

The latter block is specification notation, not Oak syntax.

Selection and resolution remain distinct: target-dependent primitive facts may
still be required before final offsets and size are known.

## 5. Representation selection cannot change shape satisfaction

If two concrete realizations share the same semantic record, then any
representation-blind record-shape constraint must give the same result for both.

Formally, if:

```text
semantic(a) = semantic(b)
```

then for every semantic record constraint `S`:

```text
a satisfies S  iff  b satisfies S
```

regardless of their layouts.

This is a load-bearing rule: representation never participates in generic
record-shape satisfaction.

## 6. Ordinary record representations must cover semantic fields

For the ordinary resolved `record` representation kind, every semantic field
must be represented exactly once by semantic name.

A resolved ordinary record representation must not silently:

- omit a semantic field;
- invent a semantic field;
- duplicate a semantic field.

Different order and offsets are allowed when the selected representation policy
allows them.

More exotic encodings may intentionally transform the storage model, but they
must use an explicit representation kind/policy and establish a semantic mapping
rather than masquerading as an ordinary record layout.

## 7. Optimized/compressed representations require proof obligations

Representations such as:

- structure-of-arrays;
- niche/tag elision;
- bit packing;
- compressed handles;
- wire encodings;
- platform-specific vector layouts;
- explicit union-like overlap;

may not satisfy the ordinary one-field/one-storage-field rule.

They require a representation-specific abstraction relation explaining how
concrete bits denote the semantic value. Optimizations are legal only when that
relation is preserved.

This lets Oak support aggressive systems representations without weakening the
semantic type system.

## 8. Representation and ABI visibility

A private representation may change without changing the semantic module API,
provided no exported ABI depends on it.

When representation is part of a public FFI/ABI/wire/MMIO contract, that
representation choice is itself part of the exported contract and must be
explicit and stable according to that boundary's rules.

Thus Oak can expose:

```text
public semantic contract
```

without necessarily exposing:

```text
private machine layout
```

unless callers genuinely need the latter.

## 9. Semantic IR model

Semantic IR represents this separation with named `RepresentationBinding`
entries in a `RepresentationRegistry`.

A binding contains:

```text
semantic type name
representation name
representation facts/policy
```

Multiple bindings may name the same semantic type. Selecting a binding copies
the semantic definition unchanged and rebinds only its representation axis.

This registry is deliberately separate from `Type` so representation alternatives
cannot accidentally become part of type identity.

## 10. Formal obligations

The representation layer must establish at least:

1. selecting a representation preserves semantic identity;
2. rebinding representation preserves semantic identity;
3. record-shape satisfaction is representation-independent;
4. distinct layouts may realize one semantic type;
5. ordinary resolved record layouts cover all semantic fields exactly once;
6. a fixed selected policy plus target facts resolves deterministically;
7. representation-specific optimizations preserve their abstraction relation.

The initial Lean `Oak.RepresentationPolymorphism` model proves the first four
abstract laws. Concrete layout/refinement proofs remain separate obligations.
