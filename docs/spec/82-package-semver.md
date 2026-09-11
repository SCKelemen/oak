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
| Change the representation of a `pub(opaque)` type | patch |

The highest-severity individual change determines the package release.

A `pub(opaque)` type (`83-modules.md` section 6.2) exports a name and nothing
else: its snapshot entry has kind `opaque type`, no definition, and no ABI,
and every signature that mentions a declared record or struct spells it by
name rather than by shape. Changing the fields behind an opaque name is
therefore invisible to the classifier, exactly as it is invisible to clients.
Changing a *transparent* declared record's shape still changes that export's
definition and is classified by the rows above.

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

The classification and the exact-bump rule are modeled in
`spec/lean/Oak/Semver.lean`: the level of a change set is the maximum over
its members and never decreases when changes are added (`classify_ge`,
`classify_le_bound`, `classify_mono`, `classify_patch_iff`); an export is
unchanged exactly when kind, semantic type, and ABI are unchanged
(`exportChange_none_iff`, `exportChange_cases`); the required version is
strictly greater than the previous (`next_gt`), unique (`enforce_unique`),
recoverable to its level at or after 1.0.0 (`next_injective_level`,
`next_resets`), and before 1.0.0 breaking and additive changes coincide
(`next_pre1_major_eq_minor`). `packageapi/semver_laws_test.go` checks the Go
procedures against the same laws over randomized snapshots.

The reference checker is:

```sh
go run ./cmd/oak-semver previous-api.json current-api.json
```

It exits nonzero for an invalid version and lists the public changes that caused
the classification. Repositories can run this command in their publication CI
using the last release snapshot and the compiler-produced candidate snapshot.
At module granularity the same rule is `oak mod bump` (section 6).

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
compiler-generated generic or extensible-record specializations. Only `pub`
declarations are projected (`83-modules.md` section 6). Function and value
types are spelled canonically as `fn(a,b)->r`; a declared record, struct,
ADT, or interface appearing inside a type is spelled by its name, so the shape
of a named type is recorded once, in its own export, and never at all for an
opaque type.

## 6. Module snapshots

Versions attach to modules, not packages: a `require` line names a module and
a version, so the unit whose API the version promises is the module. A
**module snapshot** is the snapshot of every package in an `oak.mod` tree,
keyed by import path:

```json
{ "module": "example.com/lib", "version": "1.1.0",
  "packages": { "example.com/lib/geometry": { "package": "...", "version": "1.1.0", "exports": { ... } } } }
```

`oak.mod` may declare the module's version with a `version` directive:

```text
module example.com/lib
oak 0.1.0
version 1.1.0
```

The directive is the module's claim; the tooling checks it. Classification of
a module change is the maximum over its packages, where an added package is
minor and a removed package is major, and the required version of the module
is that of the highest-severity package change (`Oak.Modules.Semver.moduleLevel`;
`moduleLevel_ge`, `moduleLevel_patch_iff`, `moduleLevel_removed`). Package identity within the
module is the import path; a package may not change import path between two
snapshots without counting as removed and added.

Every input of the module tooling is a local file. The compiler never fetches,
and `oak mod` never contacts a registry:

| Command | Meaning |
|---|---|
| `oak mod api [dir]` | Print the module snapshot at the `version` directive (or `0.0.0` when absent). |
| `oak mod diff previous.json [dir]` | List the public changes since `previous.json`, their levels, and the required version. |
| `oak mod bump previous.json [dir]` | As `diff`, then enforce: the `version` directive must equal the exact required version. Without a directive the command fails and names the version to add. |
| `oak mod compat dep-api.json [dir]` | Check this module's sealed imports against a dependency's snapshot (section 8). |
| `oak mod pack [-o out.tar.gz] [-previous prev.json] [-url location] [dir]` | Build the archive `oak mod download` consumes, carrying `api.json`; with `-previous`, enforce the exact bump first (section 7). |
| `oak mod upgrade [-dir dir] dep-api.json...` | Among candidate snapshots of one dependency, pick the highest version that satisfies the module's sealed imports (section 8). |
| `oak mod try path candidate-dir [-dir dir]` | Build every package of the module with `path` replaced by the local candidate, deciding unsealed imports (section 8). |
| `oak mod tidy [-w] [dir]` | Reconcile `require` directives with the packages' imports; `-w` rewrites `oak.mod` (`83-modules.md` section 4.5). |

Both `diff` and `bump` snapshot the module through the ordinary package build,
so a module that does not type check has no API and is rejected before any
comparison. Nested modules (`83-modules.md` section 3.5) are packages
of the module: each is snapshotted under its own path from its elaborated
declarations, with every name spelled as a directory package would spell it
(its own types bare, other packages' types by path), so a nested module's
API changes classify exactly like a directory's. Only `oak-api`, the
single-package tool, refuses a package that declares nested modules. The compiler snapshot boundary is `compiler.ModuleAPISnapshot`.

## 7. Archive-carried snapshots

A module archive fetched by `oak mod download` (`83-modules.md` section 4.4)
may carry its snapshot as `api.json` at the module root. When present it is
checked after the digest and module-path checks and before the module is
installed in the cache: the carried snapshot must name the required version
and be identical to the snapshot the archive's own source produces at that
version. A mismatch rejects the archive; the module never enters the cache.

This makes a published API claim **honest by construction**: a module cannot
ship one `api.json` and different source, so a client that decided on a
version from the snapshot (section 8) builds against the API it inspected.
An archive without `api.json` is accepted — the digest already pins its bytes
— it simply makes no separately checkable API claim. `api.json` is bounded at
64 MiB and decoded before any of it is trusted; a malformed file rejects the
archive.

`oak mod pack` is the producer. It requires a `version` directive, snapshots
the module at that version, optionally enforces the exact bump against a
previous snapshot (`-previous`), and writes a gzip-compressed tar holding the
module's files under one `<last-path-segment>-<version>/` wrapper directory
plus `api.json`. The packer admits exactly what the extractor admits: regular
files and directories on relative slash paths; hidden entries, `vendor`,
`testdata`, symbolic links, and every other file kind are left out. Headers
are written deterministically (fixed modes, no timestamps, sorted members), so
the same tree yields the same archive and the same digest, and the command
prints the `require path version location sha256:<hex>` line a client pastes
into its manifest. The author-to-consumer loop is therefore closed by local
files only: pack, publish the archive anywhere reachable over HTTPS, and the
consumer's download verifies both the bytes and the API claim.

## 8. Sealed-signature compatibility

A client that seals an import (`83-modules.md` section 6.3) depends on
exactly the members its signature lists, with exactly the kinds and types it
wrote. Whether a version of the dependency is safe for that client is
therefore decidable from the dependency's module snapshot alone, without the
dependency's source and without building it:

- every sealed package must be present in the snapshot;
- every `Name: type` member must be exported as a type (record, struct,
  alias, sum, opaque type, or interface);
- every value member must be exported as a function or value whose canonical
  type equals the signature's, where the signature's type is spelled with the
  dependency's own names (`Key` for the package's `Key`).

`oak mod compat dep-api.json [dir]` performs this check for every package of
the module at `dir` against the snapshot in `dep-api.json`, and lists each
member the snapshot fails to provide as `importer: alias.member (package
path): reason`. `oak mod upgrade dep-api-1.json dep-api-2.json ...` runs the same
check against several candidate snapshots of one dependency and reports the
highest version that satisfies every sealed import as a `require` line, with
every candidate's verdict; it fails when no candidate does. This is the
consumer side of Elm's rule: an upgrade decision made from published API
artifacts alone, before any source is fetched or built. The check is exact in the same sense as `OAK-M0113`: no
widening, no narrowing. A member the client did not seal may change or vanish
freely — which is the point of sealing. Unsealed imports (`geo := import(...)`)
are not covered; they depend on whatever they reference, and only a build
against the new version decides them. The compiler entry point is
`compiler.CheckSealedCompatibility`.

Unsealed imports (`geo := import(...)`) depend on whatever they reference,
so no snapshot decides them; a build does. `oak mod try path candidate-dir
[-dir module]` builds every package of the module with the dependency `path`
replaced by the local `candidate-dir` — an in-memory `replace` laid over the
manifest, which is never rewritten — and reports each package as compatible
or not with the first diagnostics. The candidate must be a module whose
`oak.mod` declares `path`; nothing is fetched. Together with `oak mod
upgrade` this covers both halves: sealed imports are decided from the
published snapshot, unsealed ones from a local build of the candidate.

Elm's package manager derives the required bump from the API diff and refuses
to publish otherwise; Oak does the same at module granularity (`oak mod
bump`), and additionally lets the *client* decide upgrades from the same
artifact (`oak mod compat`) and refuses to install an archive whose API claim
its source does not honor (section 7).

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
