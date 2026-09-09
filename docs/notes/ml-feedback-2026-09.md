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

**Specified, not implemented.** `20-types.md` §11.3 is the normative section
the ask proposed, taken nearly as written and tightened where the survey's
evidence demanded it:

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

**Specified, not implemented.** `92-ffi.md` §2.5: `c.span_of(v: []T)` and
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

1. Implement the pipeline operator and field accessors already specified in
   `10-syntax.md` §12. Largest win for no new semantics.
2. Uniform call syntax `x.matmul(w).relu()` as sugar for `relu(matmul(x, w))`
   when the receiver's package exports the function; no dispatch, no
   vtables. Needs a normative section before implementation.
3. Operator definitions bound only to functions marked `operator` in the
   receiver's package. The constitution's "no hidden work" rule is the bar
   the proposal must clear; an explicit marker that makes every `+` on a
   tensor name one findable function is the defensible middle, and the
   decision is open.
4. Array literals and a variadic literal form; `pub` constants exported as
   values; const parameters on functions.

## Tier 6 — verification and debugging

`#line` directives in generated C (`90-backend.md` §10 already asks for
them), per-module profiles (tier 1.2), and a trace schema for FFI calls so
`oak test -sim` can replay a kernel launch sequence. All recorded, none
changed here.

## Revisit criteria (from the ml survey), current state

| Item | Criterion | State |
| --- | --- | --- |
| O1 | `f32`/`f64` with literals, arithmetic, core intrinsics, `f32 ↔ c.Float` | specified (`20-types.md` §11.3) |
| O2 | `c.Ptr` plus length constructible from `[*]T`/`[]T`, checked at the boundary | specified (`92-ffi.md` §2.5) |
| O3 | Any runtime-sized allocation surface | direction |
| O4 | Views or spans in records or as return values | roadmap |
| O5 | `F32x4` with `mul` and `fma` | specified (`20-types.md` §11.3.7) |
| O6 | A frontend surface for `x.matmul(w).relu()` | direction; pipeline operator already specified |
