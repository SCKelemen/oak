# Package API snapshots and automatic SemVer

Status: normative for package publication; snapshot production is a compiler
pipeline boundary.

## 1. Checked public API

A published Oak package carries a deterministic API snapshot produced after
parsing, type checking, generic-constraint normalization, effect checking, and
layout resolution. Each public export records:

- its kind;
- canonical semantic type, including parameters, results, row/shape constraints,
  generic constraints, ownership, and effects;
- canonical public ABI when representation is observable, including calling
  convention, size, alignment, field order and offsets, tags, and carriers.

Bodies, private declarations, source order without semantic meaning,
documentation, and compiler-generated symbol names are excluded.

## 2. Change classification

| Change | Required release |
|---|---|
| No checked public API change | patch |
| Add a public export | minor |
| Remove or rename a public export | major |
| Change an export kind or semantic type | major |
| Strengthen an input constraint or effect requirement | major |
| Weaken a promised result, shape, or effect | major |
| Change an exposed struct/ABI layout | major |
| Change only an unexposed semantic-record implementation layout | patch |

The highest-severity individual change determines the package release.

Before `1.0.0`, both additive and breaking public changes advance the minor
component. Patch-only changes advance patch. At and after `1.0.0`, ordinary
SemVer major/minor/patch rules apply.

## 3. Enforcement

Publishing compares the last published snapshot with the candidate snapshot.
The declared candidate version must equal the exact next version implied by the
table. A lower bump is unsafe; a larger bump is rejected as non-reproducible
versioning. Package identity must not change between the two snapshots.

Oak source text is UTF-8. Package versions nevertheless use SemVer's lexical
grammar: each `MAJOR`, `MINOR`, and `PATCH` component consists only of the ASCII
digits `0` through `9`, without a leading zero unless the component is `0`.

The reference checker is:

```sh
go run ./cmd/oak-semver previous-api.json current-api.json
```

It exits nonzero for an invalid version and lists the public changes that caused
the classification. Repositories can run this command in their publication CI
using the last release snapshot and the compiler-produced candidate snapshot.

## 4. Records and representation

Adding a required field to an exported closed record shape or extensible-record
constraint is major because callers may no longer satisfy it. Removing a
required input field can be compatible only when the canonical function type
proves the accepted domain widened; the initial conservative classifier treats
any canonical type change as major.

A concrete exported `struct` exposes ABI whenever foreign code, persisted data,
or separately compiled Oak code can observe its representation. Reordering,
packing, alignment, or carrier changes are then major. Choosing AoS, SoA, or
AoSoA behind a semantic-record abstraction does not change the package API and
is patch-compatible.

## 5. Compiler snapshot production

`Compilation.APISnapshot(version)` is the authoritative snapshot boundary. It
runs the complete semantic safety gates, preserves the package's source-level
declaration surface, and excludes imported standard-library declarations and
compiler-generated generic or extensible-record specializations.

Publication CI can produce the candidate snapshot directly from Oak source:

```sh
go run ./cmd/oak-api example/net 1.3.0 src/net.oak > current-api.json
go run ./cmd/oak-semver previous-api.json current-api.json
```

Record fields are sorted only in canonical semantic identity, because record
meaning is structural and order-free. Struct fields remain in declaration order
in the ABI identity, together with computed size, alignment, offsets, packing,
and declared alignment. Consequently, two structs can satisfy the same record
type while retaining different public layouts.

For a generic struct, no single numeric size exists before instantiation. Its
public ABI therefore records the ordered symbolic field types, packing policy,
declared record alignment, and per-field alignment. Each concrete instantiation
is still resolved and verified by ordinary lowering.

Until Oak gains an explicit visibility modifier, every named package-level type,
interface, function, receiver method, and value declaration is public. Receiver
methods use a receiver-qualified export name and include the receiver in their
canonical signature. Literal/default ADT variants retain their checked literal
in type identity. A future visibility feature must change this projection and is
itself a language-version decision; the compiler must never infer visibility
from capitalization or spelling.
