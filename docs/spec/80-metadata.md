# Phantom Types and Compile-Time Metadata

Oak distinguishes semantic type identity from descriptive/tooling metadata.

## 1. Phantom types

A phantom parameter changes static meaning without changing runtime representation.

```oak
Id[T]: type = u64
```

allows:

```oak
UserId: type = Id[User]
OrderId: type = Id[Order]
```

with identical machine representation but distinct static types.

Phantom parameters belong to the **type axis** and may participate in proofs, overload resolution, capability distinctions, and schema generation.

They must not silently add storage.

## 2. Metadata

Metadata is compile-time information attached to semantic declarations or members for use by projections/tooling.

Examples:

```text
serializer field number
database column name
UI label / unit
debugger display hint
documentation category
protocol documentation text
```

Metadata does not change runtime representation unless a specific projection explicitly interprets it to generate runtime data.

## 3. Typed vs untyped metadata

Correctness-critical metadata must not be an arbitrary string dictionary.

Oak should distinguish:

1. **language semantics** — ownership, effects, representation, refinements;
2. **typed attributes** — extensible but schema-checked metadata;
3. **free annotations** — descriptive data with no correctness authority.

A typed attribute definition must specify:

- valid attachment targets;
- field/value schema;
- uniqueness/repeatability;
- whether it affects any projection;
- whether conflicting attributes are an error.

## 4. Legacy backtick tags

Older Oak documents use syntax such as:

```oak
id: u64 `{ db_column: "user_id", primary_key: 1 }`
```

and similar tags on ADT variants.

The semantic concept is retained, but this surface syntax is **not yet normative**. We should select the final attribute syntax only after the type/schema model is clear.

The parser may temporarily accept legacy tags for migration.

## 5. Payload/defaults are not metadata

ADT payload defaults and record field defaults are semantic construction facts.

They are not the same as:

```text
wire code
JSON field number
documentation label
database column
```

Those belong to metadata or representation.

This prevents historical ambiguity such as interpreting:

```oak
| NotFound: u16 = 404
```

as both a payload default and an enum/wire discriminant.

## 6. Representation attributes

Attributes that constrain memory/wire representation require stronger typing and validation than ordinary metadata.

Examples might include:

```text
repr integer width
alignment
packing
endianness
wire field number
```

These should project into the representation axis, where consistency and layout laws are checked. They must not remain opaque strings by the time code generation relies on them.

## 7. Reflection

Compile-time tooling may inspect types and metadata.

Runtime reflection is not implied. If metadata must exist at runtime, the projection must explicitly emit a table/object and its storage cost must be visible.

This preserves Oak's no-hidden-work rule.

## 8. Metadata-driven generation

One declaration may drive multiple artifacts:

```text
Oak type
  -> C ABI declaration
  -> serializer schema
  -> debugger schema
  -> protocol docs
  -> UI forms
  -> database schema
```

Each projection consumes the same checked type + metadata model rather than reparsing source tags independently.

## 9. Formal verification targets

Initial proof/checking targets:

- phantom parameters do not alter declared machine representation;
- metadata attachment does not alter runtime value semantics unless explicitly projected;
- typed attributes satisfy their declared schemas;
- duplicate/conflicting singleton attributes are rejected;
- representation-affecting attributes produce a consistent representation or fail;
- generated schema field identities are unique where the target format requires uniqueness.
