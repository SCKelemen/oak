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
