# Modules and Packages

Status: normative; implemented (`compiler/modules.go`, `compiler/derive.go`,
`modules/`), Lean model and proofs in `spec/lean/Oak/Modules.lean`. The
bootstrap standard library keeps its prelude-style `import(std)` /
`import(testing)` splice and is importable as qualified views (section 9)
until it is re-cut into packages.

Oak takes the **unit structure of Go** — a package is a directory, a module is
a versioned tree of packages with one manifest, imports are explicit and
acyclic, unused imports are errors — and the **abstraction discipline of ML
module systems** — visibility is declared, types can be exported without their
definitions, and an import can be sealed to a signature that says exactly what
the client may see. **A package is a namespace with a checked interface; a
module is the unit of versioning; neither adds runtime work.**

## 1. Design position

- **Packages, not textual inclusion.** Importing a package brings its exported
  names into scope under a qualifier. Nothing is spliced unqualified into the
  importer (the bootstrap `std` is the one grandfathered exception, section 9).
- **Explicit visibility.** A declaration is private unless marked `pub`. The
  compiler never infers visibility from capitalization or spelling
  (`82-package-semver.md` section 5). This is a language-version decision.
- **Abstract types are ordinary declarations.** `pub(opaque)` exports a type's
  name and hides its definition. There is no separate signature language for
  types: the representation axis stays private by default
  (`45-representations.md` section 8).
- **Signatures are record shapes.** An import may be sealed to a semantic
  record shape whose members are values or abstract types
  (`{ Key: type, hash: (Key) -> u64 }`). One construct — the record shape of
  `40-records.md` — serves as the module interface (one fact, many
  projections).
- **Functors are generic packages, monomorphized at import.**
  `package pair[T, N: u32]` is instantiated by `import("...")[u8, 3]`; each
  argument list is a distinct concrete package (section 6.7). There is no
  runtime module object.
- **Names come from somewhere visible.** Members are qualified
  (`alias.member`) or imported by name (`{ f, g } := import(...)`); there is
  no whole-package `open`, so readers always see where a name comes from.
- **Whole-program, one translation unit.** The compiler resolves every package
  of the build into one flat program before type checking. Encapsulation is a
  static rule enforced by the elaborator, not a link-time property; the C
  backend sees only injectively renamed declarations (section 7).
- **Fail closed everywhere.** An import that cannot be resolved, a member that
  is not exported, a package name that disagrees with its directory, an import
  cycle, a missing module — each is a hard error with a stable code (section
  8). The loader never guesses a directory, a version, or a visibility.
- **No hidden work.** Module loading is a compile-time activity over local
  files. The compiler performs no network access; dependency modules are
  provided through `replace` directives or a module cache directory
  (section 4.3).

## 2. Packages

A **package** is a directory of `.oak` files. Every file begins with a package
clause naming the package:

```oak
package geometry
```

Rules (diagnostic `OAK-M0103`):

- every file of the directory carries the same package name; a file of the
  **root** package (the directory being built) may omit the clause and is then
  `package main` — the single-file rule — while files of imported packages
  must declare it;
- the name is a lowercase ASCII identifier without `__`;
- an importable package is named after the last segment of its import path
  (`example.com/hello/geometry` is `package geometry`) — there is no Go-style
  gap between directory name and package name;
- `package main` cannot be imported; it is the root of an executable build.

Files are a storage spelling of a package, not a semantic boundary (the
constitution's syntax-equivalence rule applied to file boundaries). All
package-level declarations of all files share one package scope, exported or
not, and imports are package-scoped (section 3.3). `*_test.oak` files belong to
the package only when the build is a test build (`110-testing.md`).

## 3. Imports

### 3.1 Import paths

An import path is a `/`-separated sequence of segments. Each segment is a
non-empty run of ASCII lowercase letters, digits, `.`, `_`, and `-`, starting
with a letter or digit; `.` and `..` are not segments; no segment contains
`__`; the whole path is at most 256 bytes (`OAK-M0101`).

A path whose first segment contains no dot names a **standard library**
package (`std`, `testing`, and future `strings`, `encoding/utf8`). A path whose
first segment contains a dot (`example.com/hello`) belongs to a module (section
4). The grammar is what makes the directory mapping containment-safe: a valid
path can only name a directory below a module root, never `..` out of it.

### 3.2 Import forms

```oak
import("example.com/hello/geometry")            // binds geometry
geo := import("example.com/hello/geometry")     // binds geo
h: { Key: type, hash: (Key) -> u64 } = import("example.com/hello/fnv")  // sealed
import(std)                                     // bootstrap, unqualified (section 9)
```

- The **statement form** binds the last path segment.
- The **binding form** `name := import(path)` chooses the alias.
- The **sealed form** `name: Sig = import(path)` chooses the alias and seals
  the import to the signature `Sig` (section 6.3).
- The **selective form** `{ f, g } := import(path)` binds the named exported
  members unqualified; each name is resolved by the visibility rule of
  section 6 and follows the alias rules (no collision with declarations or
  other imports, unused names are errors). A selective import cannot be
  sealed.
- The **instantiating form** `import(path)[u8, 8]` (in any of the above)
  instantiates a generic package (section 6.7).
- A bare identifier path (`import(std)`) is sugar for a single-segment path.

`import(...)` is legal only as a top-level import statement or as the entire
initializer of a top-level binding; anywhere else it is rejected
(`OAK-M0111`). Imports precede declarations in a file (`OAK-M0111`). One path
per import statement.

### 3.3 Aliases

An import alias is a **package-scoped name**: every file of the package sees
it, two files may repeat the same import under the same alias, and it is an
error (`OAK-M0107`) when

- two imports bind one alias to different paths, or one path to a sealed and
  an unsealed binding;
- an alias collides with a package-level declaration or with a compiler-known
  library name (`c`, `arm64`, `simd`);
- an alias is used as a value or redeclared anywhere in the package — a
  package is not a value and aliases are never shadowed;
- an import is unused.

### 3.4 Qualified references

A package member is referenced as `alias.member` in expression position and in
type position. All of the following resolve through one rule (section 6):

```oak
geo.make(1, 2)                  // exported function
p: geo.Point = geo.origin()     // exported type
r: ring.Ring[u8, 8]             // exported generic type with arguments
geo.Point { x: 1, y: 2 }        // typed record literal (transparent types only)
s: geo.Shape = .Line(3)         // variant construction with expected type
```

`alias.Type.Variant(payload)` and `alias.Type.Variant` construct variants of
an imported ADT exactly like the unqualified `Type.Variant(payload)` form:
after elaboration a pass rewrites both into variant expressions
(`compiler/variants.go`), so the checker, lowering, and backend see one
construction form.

## 4. Modules

### 4.1 The manifest

A **module** is a directory tree rooted at a file named `oak.mod`. Its module
path is the import-path prefix of every package in the tree: the package in
directory `<root>/a/b` has import path `<module path>/a/b`.

```text
module example.com/hello
oak 0.1.0
require example.com/dep 1.2.0
replace example.com/dep => ../dep
// comments start with //
```

- `module <path>` — required, exactly once; the path must have a dotted first
  segment (standard library paths are reserved).
- `oak <version>` — the language version the module is written for
  (informational in v1).
- `require <path> <version>` — a dependency module at a minimum version;
  SemVer with the lexical grammar of `82-package-semver.md` section 3.
- `replace <path> => <dir>` — provide a required module from a local
  directory, relative to the manifest's directory unless absolute. Only the
  root module's replace directives apply.

Unknown directives, duplicates, malformed lines, replaces without a matching
require, and manifests over 1 MiB fail closed (`OAK-M0112`).

A package outside any module (no `oak.mod` above it) may import only the
bootstrap standard library; every other import is unresolvable (`OAK-M0102`).

### 4.2 Version selection

The build collects the `require` lines of the root manifest and of every
manifest it reaches. For each module path the selected version is the
**maximum version any manifest requires** — minimal version selection: the
least version satisfying every requirement (`Oak.Modules.Versions`:
`select_satisfies`, `select_minimal`, `select_mem`). Selection is a function of
the manifests alone; there is no lock file and no network. A dependency
manifest that disagrees with the path it was required under fails closed.

### 4.3 Locating modules

A required module at its selected version is located, in order, through the
root manifest's `replace` directive, else in the module cache directory
(`$OAKMODCACHE`, or `Compilation.WithModuleCache`) at
`<cache>/<path>@v<version>/`. Both must contain the module's `oak.mod`. No
other source exists in v1; fetching into the cache is external tooling
(`OAK-M0112` when absent).

### 4.4 Fetching pinned dependencies

A `require` line may pin the archive that provides the module:

```text
require example.com/dep 1.2.0 https://example.com/dep-1.2.0.tar.gz sha256:<64 hex digits>
```

`oak mod download [dir]` populates the module cache from such lines. The
compiler never fetches. The tool downloads over HTTPS only (redirects may not
leave HTTPS; locations carry no credentials), bounds the archive at 256 MiB,
computes the SHA-256 of the whole archive and compares it with the pinned
digest **before** extracting anything, extracts the gzip-compressed tar into
a staging directory admitting only regular files and directories (no
symlinks, hard links, or devices; no absolute or `..` paths; at most 100 000
members and 1 GiB decompressed), verifies that the extracted `oak.mod`
declares the required module path, checks an archive-carried `api.json`
against the API the extracted source actually exposes at the required
version (`82-package-semver.md` section 7), and only then renames the staging
directory into `<cache>/<path>@v<version>`. A single top-level wrapper
directory carrying the manifest is stripped. Identity is the module path, the
URL is a location hint, the digest is the trust anchor: the manifests alone
reproduce a build, as with Zig's pinned dependencies, without Go's proxy
protocol or version-control execution.

An import path is mapped to a directory by the longest module path that is a
segment-wise prefix of it. The resulting directory must exist, contain at least
one `.oak` file, and lie within the module root after symlink resolution;
otherwise the import is unresolvable (`OAK-M0102`).

## 5. Compile order and cycles

The packages of a build form a directed graph whose edges are imports. The
graph must be acyclic (`OAK-M0104`, naming one concrete cycle). Packages are
elaborated in dependency order — every package after every package it imports —
computed by Kahn's algorithm with deterministic tie-breaking
(`modules.Order`). `Oak.Modules.Order` proves that every placed package
follows its imports (`order_ordered`), that placed and stuck packages together
are a permutation of the input (`order_perm`), and that in a closed graph every
stuck package imports a stuck package (`order_stuck_cycle`) — the stuck set is
a cycle witness, never a lost package.

## 6. Visibility, opacity, and sealing

### 6.1 `pub`

A package-level declaration — function, method, value, type, interface, or tag
schema — is **exported** when prefixed with `pub`; otherwise it is private to
its package. A qualified reference to a private member is rejected
(`OAK-M0106`); to a non-existent member, `OAK-M0105`.

```oak
pub make: (x: i32, y: i32): Point = Point { x: x, y: y }
abs: (v: i32): i32 = v < 0 ? 0 - v | v        // private helper
```

`pub` is accepted in `package main` (it affects only the API snapshot, section
10). Encapsulation is decided at elaboration: `Oak.Modules.Visibility.lookup_never_private`
proves a qualified reference never resolves to a private declaration, and
`lookup_exported_resolves` that every exported one is reachable.

### 6.2 `pub(opaque)`

`pub(opaque)` on a type declaration exports the **name** and hides the
**definition**. Outside the declaring package a value of the type can be
named, held, passed, returned, and compared only through the package's
exported functions; constructing a literal, reading a field, naming or
matching a variant is rejected (`OAK-M0110`,
`Oak.Modules.Visibility.opaque_projection_local`). Inside the package the type
is ordinary. Generic opaque types hide the definition of every instantiation.

```oak
pub(opaque) Point: type = struct { x: i32, y: i32 }
pub make: (x: i32, y: i32): Point = Point { x: x, y: y }   // the only constructor
```

An opaque type's representation is not public ABI: changing it is a patch
change (`82-package-semver.md` section 2), and signatures mentioning the type
spell it by name, so the representation never leaks into the snapshot. `pub(opaque)` applies to
type declarations only; on a value or function it is a parse error.

### 6.3 Signatures and sealing

A **signature** is an inline record shape whose members are value members
(`name: Type`) or abstract type members (`Name: type`). Sealing an import to a
signature does three things:

1. **Narrows**: through the sealed alias only signature members are visible
   (`OAK-M0109` for anything else; `lookup_sealed_subset`).
2. **Checks membership and kind**: the package must export every member, type
   members as types and value members as values (`modules.Conforms`,
   `OAK-M0109`).
3. **Checks types exactly**: each value member's declaration must have exactly
   the signature's type, where a sibling type member denotes the package's
   type of that name (`OAK-M0113`, checked by the type checker after the
   program). No widening, no narrowing — the explicit-contract rule of
   `25-type-inference.md` section 4.

Because a sealed client depends on exactly its signature, whether a new
version of the dependency still satisfies it is decidable from the
dependency's API snapshot alone: `oak mod compat dep-api.json` checks every
sealed import of a module against a snapshot (`82-package-semver.md` section
8). The loader records each sealed import's members and canonical types for
this purpose (`ModuleInfo.Sealed`).

```oak
h: { Key: type, key: (u64) -> Key, hash: (Key) -> u64 } = import("example.com/hello/fnv")
k: h.Key = h.key(2)
```

Sealing never widens: whatever resolves through a sealed import resolves to
the same declaration through the unsealed import (`lookup_sealed_narrows`).

A signature may be written inline, declared in the importing package
(`Hasher: type = { Key: type, hash: (Key) -> u64 }`), or exported by another
package and named as `alias.Hasher`. Signature shapes are compile-time
interfaces: they are never emitted as runtime records.

**Abstract type members are fresh types.** A `Name: type` member is ML's
opaque ascription: each sealed binding gets a *fresh nominal type*
`h.Name`, distinct from the package's own type and from every other sealed
binding's (`h.Key` and `g.Key` of two seals of one package do not unify).
Values acquire and shed the fresh type only at the sealed boundary: the
elaborator rewrites `h.f(args)` so that arguments in abstract positions of
`f`'s signature are unwrapped and an abstract result is wrapped by
compiler-only coercions (`__abstract_<fresh>`, `__concrete_<fresh>`) that the
checker admits exactly between the fresh type and its underlying type
(`OAK-M0113` otherwise) and the backend emits as identities over a typedef
alias. Function-valued members with abstract types must be called directly.
Inside the importer the fresh type is opaque (`OAK-M0110`): its definition is
unreachable. Only declared records and ADTs can be sealed abstract.

**Sharing.** `Name: type = T` shares a type member: it stays transparent and
the package's type must be exactly `T` (`OAK-M0113`) — the `with type`
constraint. Signature types are monomorphic in v1.

### 6.4 What privacy means

Privacy is a **static** rule. The whole program is compiled into one C
translation unit, so a private function is present in the emitted C; it is
unreachable from Oak source outside its package because the elaborator refuses
to resolve it, and unspellable because its internal name is reserved (section
7). Privacy is encapsulation for correctness and evolution, not secrecy.

### 6.5 Methods stay with their type

A method (`fn (r: T) m()`) may be declared only in the package that declares
its receiver type (`OAK-M0114`). Oak's interfaces are implicit, so there are
no instances to collide, but two packages attaching same-named methods to one
imported type would make method lookup depend on which package is compiled —
Go's rule, adopted for the same reason.

### 6.6 Derived declarations

A declaration-form function whose definition is `derive.<kind>` receives a
compiler-synthesized body computed from its parameter type's declaration, the
pattern of `c.extern("symbol")` (a typed interface whose body the compiler
supplies):

```oak
Point: type = struct { x: i32, y: i32 }
point_eq: (a: Point, b: Point): Bool = derive.equal
point_hash: (v: Point): u64 = derive.hash
```

- `derive.equal` requires `(a: T, b: T): Bool` and compares field by field
  (records) or variant by variant with payloads (ADTs).
- `derive.hash` requires `(v: T): u64` and mixes fields, or the variant index
  and payload, with shift-xor steps that never overflow-trap.
- `derive.compare` requires `(a: T, b: T): Ordering` with
  `Ordering: type = Less | Equal | Greater` in scope, and orders records
  lexicographically by field and ADTs by variant index then payload.
- `derive.format` requires `(v: T, dst: [*]u8): Result[u32, TextError]`
  (the strings library's `TextError`) and renders `Point { x: -3, y: 42 }`
  or `Line(3)` into the caller's span through the library's text builder —
  bounds-checked writes, no allocation, decimal integers, `true`/`false`.
- `derive.test_generate`, `derive.test_encode`, and `derive.test_decode`
  derive a test-command sum type's tape generator, `TestCommand` packing, and
  range-checked decoder (`110-testing.md`, "Typed commands"); the type is the
  return type, the parameter, or `Option`'s argument respectively, and they
  require `import(testing)` (and `import(std)` for `Option`).
- Members may be fixed-width integers, `Bool`, declared records or ADTs, and
  concrete instantiations of generic ones (`Pair[u8]`, `Wrap[u16]`),
  recursively; helpers are generated once per type or instantiation, the
  instantiation's shape obtained through the same substitution authority the
  type checker uses (`typechecker.SubstituteTypeAST`). Anything else is
  rejected (`OAK-M0203`); a generic template itself is not derivable over,
  only its instantiations.
- Derivation is admitted only in the package declaring the type
  (`OAK-M0204`): it reads the definition, so `pub(opaque)` types derive their
  operations at home and export them as ordinary `pub` functions.
- Unknown kinds (`OAK-M0201`) and mismatched signatures (`OAK-M0202`) are
  rejected. `derive` is a reserved qualifier, never an import alias.

The body is generated as Oak source from the declaration's field order and
variant list — one fact, one generator — parsed by the ordinary parser, and
checked by every gate like handwritten code. This is the same mechanism as
tag-driven codec derivation (`71-codecs.md`), generalized: Haskell's
`deriving` and Rust's `#[derive]` without a new syntax axis. Generated helper
names carry the reserved `__`, so they cannot collide with user identifiers.
### 6.7 Generic packages

A package may declare parameters after its name and is then a template that
every import instantiates:

```oak
package pair[T, N: u32]

pub Pair: type = struct { first: T, second: T }
pub capacity: (): u32 = N
```

```oak
bytes := import("example.com/hello/pair")[u8, 3]
words := import("example.com/hello/pair")[u32, 10]
```

Each distinct argument list is a distinct package (identity
`path@atom,atom`, section 7): its declarations are substituted copies, its
imports resolve normally, and its exports are looked up like any other
package's. Arguments are primitive types, integer constants, the importer's
own declared types, or imported types, resolved as the importer would resolve
them (`OAK-M0302` otherwise); the import must supply exactly the declared
arity, a non-generic package takes none, and a generic package cannot be the
root of a build (`OAK-M0301`). A declared parameter contract
(`package pair[T: Keyed]`, naming a record shape or interface of the package)
is checked **at the import site**: the argument must satisfy it
(`OAK-M0303`), the same predicate generic functions use, before the instance
body is checked as concrete code.
This is Oak's functor: monomorphized at import, with the package as the unit
of parameterization and no runtime object.


### 6.8 Tag schemas are package members

A tag schema (`json: tag = { name: string }`, `40-records.md` §12) is an
ordinary package-level declaration: private unless `pub`, renamed to its
internal name like any other, and named from another package as
`alias.schema` in a field's tag list (`x(wire.json: "px"): u32`). Two
packages may each declare a `json` schema without colliding. Codec
derivation recognizes the json schema under any package's spelling.

## 7. Elaboration and naming

The elaborator (`compiler/modules.go`) is the single resolution authority for
package members. For each imported package, in dependency order, it renames
every package-level declaration to its **internal name** and rewrites every
qualified reference in importers to that name; the root package keeps its
source names. The type checker, borrow checker, discipline analysis, lowering,
and backend never see an import.

The internal name of declaration `name` in package `path` is

```text
escape(path) ++ "__" ++ escape(name)
```

where `escape` keeps ASCII letters and digits, maps `_ / . -` to `_u _s _d _h`,
and any other code point to `_x` plus six hex digits. Escaped text never
contains two adjacent underscores, so `__` occurs exactly once and the name
decodes uniquely (`Oak.Modules.Mangle`: `unescape_escape`, `escape_noDouble`,
`decode_mangle`, `mangle_injective`). The backend adds its usual `oak_`
prefix: `oak_example_dcom_shello_sgeometry__make`. Diagnostics demangle
internal names back to `path.name`.

**Reserved identifiers.** User identifiers may not contain `__`
(`OAK-M0108`). Every internal name does (`mangle_reserved`), so user code can
never spell — or capture — an internal name. This is the capture-freedom
argument for the whole-program elaboration.

**Methods** are looked up by label through their receiver type and are not
renamed themselves (the receiver type is). Everything else a package declares
— functions, values, types, interfaces, tag schemas — is renamed; field tag
namespaces are strings on record fields and are rewritten through the same
lookup. Renaming is consistent across a package — binders and uses alike — so
shadowing inside function bodies is preserved.

Every token of every package is stamped with `package#file` in its
`SemanticContext`, keeping position-keyed resolution records distinct across
packages (the mechanism the stdlib and generic instantiation already use),
telling the type checker which package a projection comes from, and letting
every diagnostic name the file and position of its primary cause.

A generic package instance has identity `path@atom,atom` (arguments resolved
to primitive names, constants, or internal type names). Import paths contain
no `@` and atoms no `,`, so the identity decodes uniquely and mangles
injectively like any package path. A sealed binding's fresh abstract type
`h.Key` has internal name `mangle(importer@h, Key)`.

## 8. Diagnostics

Family `M` (`15-diagnostics.md`). Structural tests assert each code.

| Code | Meaning |
| --- | --- |
| `OAK-M0101` | import path outside the grammar of section 3.1 |
| `OAK-M0102` | import cannot be resolved to a package (no module, missing or empty directory, unavailable standard library package) |
| `OAK-M0103` | package clause missing, disagreeing between files, invalid, or not matching the directory segment; `package main` imported; duplicate type/interface declaration |
| `OAK-M0104` | import cycle (one cycle named) |
| `OAK-M0105` | `alias.name`: no such member |
| `OAK-M0106` | `alias.name`: member not `pub` |
| `OAK-M0107` | alias misuse: used as a value or redeclared, bound twice inconsistently, colliding with a declaration or compiler-known library, unused import |
| `OAK-M0108` | identifier or alias contains the reserved sequence `__` |
| `OAK-M0109` | sealed import: member outside the signature, or the package lacks a signature member with the demanded kind |
| `OAK-M0110` | projection of a `pub(opaque)` type outside its package |
| `OAK-M0111` | `import(...)` in an illegal position; imports after declarations; bootstrap import bound or sealed |
| `OAK-M0112` | manifest error: malformed `oak.mod`, dependency module not locatable, module path disagreement |
| `OAK-M0113` | sealed import: member type differs from the signature |
| `OAK-M0114` | method declared outside the package of its receiver type |
| `OAK-M0201` | `derive.<kind>`: unknown kind |
| `OAK-M0202` | derived declaration: signature does not match the kind |
| `OAK-M0203` | derivation over an unsupported type or member |
| `OAK-M0204` | derivation outside the type's declaring package |
| `OAK-M0301` | generic package arity: arguments missing, unexpected, or wrong in number; generic package as build root |
| `OAK-M0302` | generic package argument not resolvable to a type or constant |
| `OAK-M0303` | generic package argument does not satisfy the parameter's declared contract |

Module diagnostics carry the file path in their title; multi-file source
mapping of every downstream diagnostic remains the recorded debt of
`110-testing.md`.

## 9. The bootstrap standard library

`import(std)` and `import(testing)` remain **prelude-style bootstrap imports**:
they splice the embedded library into the program unqualified, exactly as
before this chapter, and are accepted from any package of a build (loaded once).
They cannot be bound or sealed (`OAK-M0111`). Their names are not `pub` and
are not renamed; a user declaration colliding with a bootstrap export is
rejected as before.

**Standard library packages.** The library files are real packages:
`strings`, `unicode`, `json`, `filters`, `hash_table`, `bitset_algebra`, and
`causal_frontier` each carry a package clause, import the library packages
they use (`strings` imports `unicode`, `json` imports `strings`, `hash_table`
imports `filters`), qualify their cross-references, and mark their exports
`pub`. `import("json")` loads json, strings, unicode, and the **core prelude**
(`std.oak`: Option, Result, Overflow, byte and ring helpers), which every
library package builds on unqualified — and nothing else. The legacy flat
prelude of `import(std)` is *derived* from the same sources at build time:
clauses and imports dropped, cross-references de-qualified, concatenated in
dependency order. One source, two spellings; the flat one cannot drift from
the packages. A program may use both: the core types are shared, so a value
from `strings.utf8_decode` and one from the flat `utf8_decode` have the same
`Result` type.

**Library sugar on package spellings.** Derived JSON codecs
(`encode[T, Json]`, `from[T](v).to[Json](dst)`), typed text literals
(`text_literal("...")`), fluent builder calls (`b.append_text(dst, s)`), and
derived formatting generate calls to library functions by their flat names.
The sugar runs after module elaboration and derivation and resolves those
names to the imported packages' internal names; a name belonging to a
library package the program did not import fails closed with a diagnostic
naming the import to add (`encode` needs `import("json")`, text needs
`import("strings")`). The flat prelude keeps the flat names.

## 10. Interaction with other chapters

- **API snapshots (`82-package-semver.md`).** The public API of a package is
  exactly its `pub` declarations; `Compilation.APISnapshot` projects only
  those. `pub(opaque)` types contribute their name but no definition or ABI,
  and named types are spelled by name inside every signature.
  `oak-api` accepts a package directory as well as a single file. Versions
  attach to modules: `oak.mod` may declare `version`, `oak mod api` snapshots
  every package of the module, `oak mod diff`/`oak mod bump` classify the
  change and enforce the exact bump, `oak mod download` refuses an archive
  whose carried `api.json` its source does not honor, and `oak mod compat`
  decides from a dependency snapshot alone whether the module's sealed
  imports still hold.
- **Testing (`110-testing.md`).** `oak test` compiles each test directory
  through the package loader with `*_test.oak` files included, so test
  packages import other packages of their module and diagnostics name real
  files. `oak run [dir]` builds a package, compiles the C with the system
  compiler into a temporary directory, runs it, and propagates its exit
  status — a development convenience over trusted local source.
  Trust-by-import for the testing reporter is unaffected: the reporter
  declarations still enter only through `import(testing)`.
- **REPL.** A REPL session is an in-memory root package compiled through the
  loader (`Compilation.WithSessionSources`): imports resolve through the
  module enclosing the working directory, every input passes the type,
  borrow, and discipline gates, and expressions are evaluated by the
  tree-walking evaluator over the elaborated program. `pub`, sealed imports,
  fresh abstract types, generic packages, and derived declarations behave as
  in a build; the only session-specific rule is that an import may be
  submitted before it is used. `:obligations` lists the recorded assumptions
  the pipeline left standing for the session program — unsafe admissions,
  unbounded loops, unlowered tail cycles, runtime-initialized globals — the
  exact inputs a proof step would take; `:strict` judges declarations under
  the strict profile, where those assumptions reject; `:lean` names, for each
  listed assumption, the Lean module and law that govern it and what
  discharges it (`OAK-D0103` → `Oak.BoundedLoop`, `OAK-B0110` → `Oak.Unsafe`,
  ...). The REPL is not a proof assistant: proofs live in Lean (`spec/lean`);
  it records assumptions and points at the law, it does not prove them.
- **FFI/SIMD (`92-ffi.md`, `93-simd.md`).** `c`, `arm64`, and `simd` remain
  compiler-known libraries, not packages; an import alias may not reuse their
  names.
- **Diagnostics (`15-diagnostics.md`).** Internal names never reach the
  programmer: rendered diagnostics demangle them to `path.name`.

## 11. Direction (not part of v1)

- **Unqualified `open` of a whole package** and **nested modules** (selective
  imports of named members exist, section 3.2).
- **A lock file** (the manifests alone already make selection
  reproducible) and **generating Lean theorem statements from a session's
  listed obligations** (section 10) — the compiler cannot state an Oak
  program's termination or disjointness in Lean's terms without an Oak
  semantics in Lean, which is the larger direction.

## 12. Required laws

- `escape` is injective and never yields adjacent underscores; `mangle`
  decodes to exactly its package path and declaration name; every internal
  name is reserved.
- Kahn ordering places every package after its imports; placed and stuck
  packages partition the input; in a closed graph every stuck package imports
  a stuck package.
- A qualified reference never resolves to a private declaration; a sealed
  import exposes only signature members and never widens the unsealed import;
  every exported declaration is reachable unsealed.
- Opaque projection is admitted exactly inside the declaring package.
- Version selection satisfies every requirement, is the least such version,
  and is one of the requirements.

These laws are mechanically checked in Lean (`spec/lean/Oak/Modules.lean`).
`spec/lean/Oak/ModulesRefinement.lean` states the correspondence in
refinement form: `lookup` resolves exactly the abstractly reachable members
(`lookup_iff_reachable`), a complete Kahn run is a valid compile order and a
stuck set is a cycle witness (`order_complete_refines`,
`order_stuck_refines`), decoding is a left inverse of mangling and user
identifiers are never internal names (`naming_refines`,
`user_identifier_not_internal`), and `select` yields exactly the abstract
minimal version (`select_iff_minimal`). The Go procedures (`modules/`) are
maintained as line-for-line transliterations of the Lean definitions and
tested against the same laws, including a randomized injectivity witness.
**R is scoped to these pure decision procedures**, not to the loader's
filesystem traversal, syntax rewriting, or diagnostics.
