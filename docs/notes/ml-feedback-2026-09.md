# Note: feedback from the ml tensor-compiler pilot, and its disposition

**Status: record of decisions.** 2026-09-09. Baseline: `specification` at
`d047334`. Source: the ml project's `docs/notes/oak-asks.md`,
`docs/notes/oak-findings.md`, and `docs/notes/oak-capability-survey.md`
(SCKelemen/ml), written against Oak `ed496d9` after training a 784-128-10
MLP to 97.5 percent on MNIST through a runtime whose kernels Oak emits.

The ml project used Oak as a tensor *compiler* — flat IR in static arenas,
index algebra, byte emission, property and simulation testing — and kept
floats, files, and buffers on the C side of the boundary because Oak has
none of them. Its asks are ordered by leverage. This note records what each
ask became: a change in this branch, a normative section awaiting
implementation, or a recorded direction.

## Tier 0 — fixes

| # | Ask | Disposition |
| --- | --- | --- |
| 0.1 | Commit the identifier-mangling fix (F11) | Already on `specification` since `2750864` (compiler temporaries in the reserved namespace). ml should advance its pin. |
| 0.2 | Source locations on discipline diagnostics (F8) | **Done.** `OAK-D0103` names the enclosing function, its primary label says which part of the canonical shape is missing, and the renderer prints `file:line:col` — or `line:col` when no file is known — instead of dropping the position. The spliced prelude is now stamped `stdlib.oak`, so prelude loops report `stdlib.oak:348:7: loop in bytes_move_within ...`. `85-discipline.md` §3. |
| 0.3 | Accept `T(literal)` as a loop step (F6) | **Done.** An integer-type constructor over one literal is an integer constant in the step and in the bound. `85-discipline.md` §3; `discipline/loops.go`. |
| 0.4 | `-profile` on the CLI | **Done.** `oak build`, `oak run`, `oak test` accept `-profile default\|strict`; anything else is a usage error. `85-discipline.md` §1. |
| 0.5 | Maybe-uninitialized `combined` in `bitset_combine` (F4) | **Done, in the backend rather than the library.** A guarded ADT/literal match with no fallback arm now ends in `else { __builtin_trap(); }`: exhaustiveness is proven upstream, the branch is unreachable, and the C data flow is total, so `-Wall` is clean for every match-valued binding, not just this one. Golden `generic_adt` regenerated (one added line). |
| 0.6 | `text_literal` escape semantics (F1) | **Decided: escapes are processed, by the scanner, once.** `\n \t \r \0 \\ \" \xHH`; anything else is a parse error. No `.oak` source in the repository contained a backslash inside a literal, so nothing changed meaning. `10-syntax.md` §2a, `70-strings.md` §12. |

## Tier 1 — modularity

| # | Ask | Disposition |
| --- | --- | --- |
| 1.1 | Scope the no-shadowing rule per package (F5) | **Done, by scoping the check rather than by mangling the root.** The typechecker records the declaring package of every package-level declaration and checks a local, parameter, or receiver against the *declaring package's* scope: a root `pub rank` no longer forbids `rank` as a local in `view` or in the prelude. Root-package code keeps the whole rule, since prelude exports are unqualified there. Mangling the root (`main__name`) was rejected because ml links against root functions by their C names. `83-modules.md` §7 and law 6. Not modeled in Lean; recorded gap. |
| 1.2 | Make the strict profile usable with the prelude (F7) | **Done, by scoping profiles per module.** 0.3 cut `import(std)` under strict from 106 `OAK-D0103` warnings to 85; the rest are genuinely non-canonical (`while i < n` with an early exit, a non-constant step, a bound reassigned in the body). Profiles are now per module: `profile <default\|strict>` in `oak.mod`, the flag overriding it for the root module only, dependencies judged under their own declaration, and the spliced prelude under `default`. A strict root that imports the prelude compiles, and its own warnings still reject (`85-discipline.md` §1, `83-modules.md` §4.1, `compiler/e2e_module_profiles_test.go`). Making the prelude itself strict-clean (85 loops) remains the standard library's own obligation. |
| 1.3 | A discard form (F3) | **Done.** `_ = expr` is an expression statement marked discard; discarding unit is rejected. The unused-result rule (`OAK-D0104`) is specified as planned and now has something to point at. `85-discipline.md` §6, `10-syntax.md` §2b. |

## Tier 2 — floating point

**`f32`/`f64` implemented and tested; the rest specified.** `20-types.md`
§11.3 is the normative section the ask proposed, taken nearly as written and
tightened where the survey's evidence demanded it. The first increment lands
literals, operators, comparisons, every conversion row, the full intrinsic
set, the C lowering with `FP_CONTRACT OFF` and exact hexadecimal literal
constants, and the Go `float32`/`float64` interpreter as first witness; a
35-check program agrees bit for bit between the two (`compiler/e2e_floats_test.go`,
golden `floats`). The second increment added the `f16`/`bf16` storage
formats (bit-exact round-to-nearest-even into the formats and exact widening,
in C and in the interpreter, fuzzed through random round trips), hexadecimal
float literals, and the `f32 <-> c.Float` / `f64 <-> c.Double` rows (tested
against libm's `sqrtf`). The third increment added the float vectors
`simd.F32x4`/`simd.F64x2` with `fma`, the 2019 `min`/`max`, lane access, and
the pairwise `reduce_add` (`93-simd.md` §1.2a), agreeing across NEON, the
portable lane loop, and the interpreter — this closes revisit criterion O5.
The fourth, fifth, and sixth increments added the `math` package
(`import("math")`): `exp exp2 expm1 log log2 log1p sin cos tan asin acos
atan atan2 sinh cosh tanh asinh acosh atanh pow` and their `_f32` forms written in Oak over the correctly rounded
primitives, so every implementation computes identical bits — the answer to
ml's `exp2f` finding is that the library is the one implementation — with
documented bounds (1 ulp; 2 for `tanh`, `atan2`, and the hyperbolics)
checked by an arbitrary-precision fourth witness
(`compiler/e2e_math_test.go`), and placed float fields in records with
`size_of` over float types. Not yet: the Lean model. The design:

- `f32`/`f64` arithmetic; `f16`/`bf16` storage-only with exactly four
  operations; contextual literals with `f64` as the no-context default;
  `x: f32 = 1` is an error, spelled `1.0`.
- Semantics fixed in every backend and profile: round to nearest even,
  subnormals preserved, no reassociation or contraction ever, IEEE default
  results instead of traps, quiet NaNs with unspecified payload. Two
  conforming implementations produce bit-identical results for the core
  set; only the transcendental library may differ, and it says by how much.
- Conversions in the `{target}_{op}_{source}` scheme: `round` (including
  from every integer type — the `f32(x: i32)` constructor is deliberately
  absent because it would be exact for some widths and rounding for others),
  `bits`, and trapping/saturating/checked integer conversions.
- Intrinsics restricted to correctly rounded operations, because only those
  admit three equal witnesses; `min`/`max` take the IEEE 754-2019 semantics
  with `min_num`/`max_num` for the 2008 ones; `derive.equal/hash/compare`
  are not derivable over float fields.
- Transcendentals in a `math` package under a **fourth witness**: each
  implementation is compared to a correctly rounded reference within a
  documented ulp bound, never to each other bit for bit. This is the
  language-level form of ml's runtime finding that two `exp2f`
  implementations in one process differed by one ulp.
- `F32x4`/`F64x2` with `reduce_add` as a specified pairwise tree
  (`55-parallelism.md` §4, fourth option), `#pragma STDC FP_CONTRACT OFF`
  and `-ffp-contract=off` in the C backend (`90-backend.md` §7a), Go
  `float32`/`float64` as the interpreter witness.

Implementation order when it starts: scanner (fraction and exponent in
`readNumber`), literal typing, primitive tables, operators, conversions,
interpreter, C lowering, intrinsics, then the Lean lattice model. Every
phase must land together for the STATUS row to gain I.

## Tier 3 — spans across the FFI

**Implemented** for every element type the design admits: fixed-width
integers, `Bool`, `f32`/`f64` and the `f16`/`bf16` storage formats, boundary
tagged unions, and declared `struct` types whose fields are recursively
those, executed end to end against libc `write`, `getcwd`, and `puts`
(`compiler/e2e_ffi_spans_test.go`, `e2e_ffi_float_spans_test.go`, golden
`c_ffi_spans`). A `[]f32` weight buffer or a `[]Point` of float fields
crosses to a C kernel as pointer and count with its layout asserted at C
compile time. This closes revisit criterion O2. The
design, `92-ffi.md` §2.5: `c.span_of(v: []T)` and
`c.span_mut_of(s: [*]T)` occupy a `c.Ptr, c.Size` parameter pair of an
extern binding for the duration of that call and nowhere else; the borrow
checker treats the call as a read or write use of the owner, so the
existing exclusivity rule keeps C from receiving two writable aliases, and
the form has no type, so the pointer cannot escape. `c.String` is
constructible from a literal only. The reverse direction stays opaque. This
retires byte-at-a-time emission and lets Oak read results back once
implemented; the `Buffer[CpuOwned]` typestate of `50-borrowing.md` §11
remains the stronger later form.

## Tier 4 — storage

Recorded, not changed here. Views and spans inside records and as return
values (`OAK-B0109`) need field-sensitive provenance, which is the
authority-contracts roadmap (`roadmap-authority-resources.md`). A
runtime-sized arena with `Memory.Allocate[arena]` as its effect belongs to
the allocation-phase partition of `85-discipline.md` §4 and
`60-effects-allocation.md` §6, both still planned.

## Tier 5 — the experience

Recorded, not changed here, in the order the ask proposed and this note
endorses:

1. The pipeline operator and field accessors of `10-syntax.md` §12 are
   **already implemented** on this branch: `p |> .x |> double |> add(u32(1))`
   compiles under the strict profile and runs. The survey's "not
   implemented" was stale; ml can use them now.
2. **Done.** Uniform call syntax (`10-syntax.md` §13): `x.matmul(w).relu()`
   is `relu(matmul(x, w))` when the receiver has no method or field of that
   name — a function visible at the call site or an exported function of
   the package declaring the receiver's type. The checker rewrites the call
   in place; nothing is dispatched. Closes revisit criterion O6.
3. Operator definitions bound only to functions marked `operator` in the
   receiver's package. The constitution's "no hidden work" rule is the bar
   the proposal must clear; an explicit marker that makes every `+` on a
   tensor name one findable function is the defensible middle, and the
   decision is open.
4. **Done.** Array literals take their shape from context (`10-syntax.md`
   §2c): `[3]u32 = [1, 2, 3]`, `sum3([4, 5, 6])`, and `dims([28, 28])`
   where `dims` takes a `[]u32` (the literal form of the variadic view;
   previously such a literal typechecked in argument position but emitted
   invalid C). `pub OP_ADD: u32 = 2` was already exported as a value readable
   as `ops.OP_ADD` and is now locked in by `compiler/e2e_module_constants_test.go`;
   const parameters on functions are 7.1 below.

## Tier 6 — verification and debugging

`#line` directives in generated C are **done** (`oak build -lines`,
`90-backend.md` §10: every function and statement maps to its Oak line).
Per-module profiles (tier 1.2) and a trace schema for FFI calls so
`oak test -sim` can replay a kernel launch sequence remain recorded.

## Tier 7 — the numeric-runtime asks (2026-09-10)

Four asks arrived after the float and const-generic increments landed. Their
disposition, in the order to work them:

| # | Ask | Disposition |
| --- | --- | --- |
| 7.1 | Size-indexed function parameters: `matmul[m, n, k]: (a: [m*k]f32, b: [k*n]f32): [m*n]f32` | **Done.** Const-generic functions (`20-types.md` §11.0) infer the const from an argument's static length or take it explicitly and monomorphize per instantiation; arrays return by value (`90-backend.md` §10); and lengths may be arithmetic over const parameters (`[M*K]f32`, `[N+1]T`), folded to literals at instantiation so the backend never sees a symbolic extent. A product does not determine its factors, so `matmul` takes its dimensions explicitly or from a plain `[N]T` position. |
| 7.2 | Consuming parameters (uniqueness types) for buffers handed to a kernel | **Specified, not frozen.** `50-borrowing.md` §9 defines consumption semantically — use after consume is `OAK-B0111`, call-local alias exclusivity over marked arguments is `OAK-B0112` and is implemented for resource callables — and leaves the parameter spelling open (`consume File` is the working form). Implementing it for ordinary owned buffers means giving `[N]T` and records an opt-in resource protocol; that is the authority-contracts roadmap (`roadmap-authority-resources.md`), not a local change. |
| 7.3 | Declared operator properties: associative, commutative, neutral | **Direction.** A property declaration on a function (`add: (a: f32, b: f32): f32 with associative, commutative, neutral(0.0)`) would be a *claim* the compiler may use for reassociation and a *proof obligation* the test runner may discharge by property tests over the choice tape (`110-testing.md`). Floats make the associative claim false in general, which is exactly why the runner, not the compiler, should own it; the compiler would consume only claims the profile allows. Needs a normative section before implementation, alongside the operator-definition question of tier 5 (3). |
| 7.4 | Data-driven `oak test` blocks for numeric conformance | **Done.** `110-testing.md` "Table targets": a `Table` function `(row: []u8): ()` runs once per file of `testdata/oak/<Test>/rows/` in name order; results and artifacts name the failing row, rows are never minimized, a missing table is an error. `import(testing)` gained little-endian row readers (`test_row_f64` and friends) and float comparison by ULP distance or exact bits (`test_ulp_distance_*`, `test_check_ulps_*`, `test_check_bits_*`), never by `==`. Rows are byte records decoded by offset; decoding through derived codecs (`71-codecs.md`) is the later refinement once those are derivable for float fields. `testrunner/runner_test.go` (`TestTableRows`). |

## Revisit criteria (from the ml survey), current state

| Item | Criterion | State |
| --- | --- | --- |
| O1 | `f32`/`f64` with literals, arithmetic, core intrinsics, `f32 ↔ c.Float` | **implemented**, `c.Float`/`c.Double` rows included (`20-types.md` §11.3); the complete v1 `math` package implemented bit-exactly |
| O2 | `c.Ptr` plus length constructible from `[*]T`/`[]T`, checked at the boundary | **implemented** (`92-ffi.md` §2.5; integer, float, `Bool`, tagged-union, and proven-layout struct elements) |
| O3 | Any runtime-sized allocation surface | direction |
| O4 | Views or spans in records or as return values | roadmap |
| O5 | `F32x4` with `mul` and `fma` | **implemented** (`93-simd.md` §1.2a; NEON and portable lowerings agree with the interpreter) |
| O6 | A frontend surface for `x.matmul(w).relu()` | **implemented**: uniform call syntax (`10-syntax.md` §13) and the pipeline operator (`x \|> matmul(w) \|> relu`); operator definitions remain direction |
