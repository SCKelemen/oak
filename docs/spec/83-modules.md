# Modules and Packages

Status: normative; implemented for user packages (`compiler/modules.go`,
`modules/`), Lean model and proofs in `spec/lean/Oak/Modules.lean`. The
bootstrap standard library keeps its prelude-style `import(std)` /
`import(testing)` splice (section 9) until it is re-cut into packages.

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
- **No functors, no `open`, no nested modules in v1.** Parameterized
  abstraction is expressed with Oak's monomorphized generics and constraints;
  package-level type parameters (generic packages) are a recorded direction
  (section 11). Unqualified import of another package's names is not
  provided: readers always see where a name comes from.
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

- every file of the directory carries the same package name;
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

`alias.Type.Variant(payload)` in call position is not yet lowered (a recorded
gap shared with unqualified `Type.Variant(payload)`); bare `.Variant` with an
expected type is the working spelling.

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
change (`82-package-semver.md` section 2, last row). `pub(opaque)` applies to
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

```oak
h: { Key: type, key: (u64) -> Key, hash: (Key) -> u64 } = import("example.com/hello/fnv")
k: h.Key = h.key(2)
```

Sealing never widens: whatever resolves through a sealed import resolves to
the same declaration through the unsealed import (`lookup_sealed_narrows`). In
v1 a type member is satisfied by any exported type and is transparent unless
the package declared it `pub(opaque)`; generating a fresh abstract type per
sealed binding (ML's opaque ascription) is a recorded direction (section 11).
Signature types are monomorphic in v1.

### 6.4 What privacy means

Privacy is a **static** rule. The whole program is compiled into one C
translation unit, so a private function is present in the emitted C; it is
unreachable from Oak source outside its package because the elaborator refuses
to resolve it, and unspellable because its internal name is reserved (section
7). Privacy is encapsulation for correctness and evolution, not secrecy.

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

Two kinds of declarations are looked up by label rather than by name and are
therefore not renamed: **methods** (`fn (r: T) m()` is selected through the
receiver type, which is renamed) and **tag schemas** (field tags name their
schema as a string; tag namespaces are consequently program-wide, a recorded
limitation). Renaming is consistent across a package — binders and uses alike
— so shadowing inside function bodies is preserved.

Every token of an imported package is stamped with the package path in its
`SemanticContext`, keeping position-keyed resolution records distinct across
packages (the mechanism the stdlib and generic instantiation already use) and
telling the type checker which package a projection comes from.

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

Re-cutting the standard library into importable packages (`strings`,
`encoding/utf8`, ...) under the rules of this chapter — with `pub` exports and
qualified access — is the recorded migration; `docs/notes/standard-library-design.md`
section 4 sketches the module graph. Until then a non-bootstrap standard
library path is unresolvable (`OAK-M0102`).

## 10. Interaction with other chapters

- **API snapshots (`82-package-semver.md`).** The public API of a package is
  exactly its `pub` declarations; `Compilation.APISnapshot` projects only
  those. `pub(opaque)` types contribute their semantic identity but no ABI.
  `oak-api` accepts a package directory as well as a single file.
- **Testing (`110-testing.md`).** `oak test` still concatenates the files of
  one directory into a bootstrap package; routing the runner through the
  package loader so test packages can import other packages is a recorded next
  step. Trust-by-import for the testing reporter is unaffected: the reporter
  declarations still enter only through `import(testing)`.
- **FFI/SIMD (`92-ffi.md`, `93-simd.md`).** `c`, `arm64`, and `simd` remain
  compiler-known libraries, not packages; an import alias may not reuse their
  names.
- **Diagnostics (`15-diagnostics.md`).** Internal names never reach the
  programmer: rendered diagnostics demangle them to `path.name`.

## 11. Direction (not part of v1)

- **Generic packages / functors**: `package ring[T, N: u32]` instantiated at
  import; today parameterized code is written with generic declarations inside
  ordinary packages.
- **Opaque ascription**: a sealed import's `Name: type` member becoming a
  fresh abstract type per binding, and `with type` sharing constraints.
- **Named signatures**: `Hasher: type = { ... }` declarations reusable across
  sealed imports (blocked on function types in record-literal expressions).
- **Selective and unqualified imports**, **nested modules**.
- **Package-qualified variant construction in call position**
  (`geo.Shape.Line(3)`), shared with the unqualified gap.
- **Codegen type inference for `x := call()` returning a record**: annotate
  the binding today; a pre-existing backend limitation the module tests expose.
- **Standard library packages** (section 9), **`oak test` through the loader**
  (section 10), **source-mapped multi-file diagnostics**, **network fetch and
  a lock file** (the manifests alone already make selection reproducible),
  **evaluator support** (the interpreter still ignores imports).

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
The Go procedures (`modules/`) are maintained as line-for-line transliterations
of the Lean definitions and tested against the same laws, including a
randomized injectivity witness; an explicit refinement theorem relating the Go
representation to the model is pending, so the STATUS matrix records M and P
but not R.
