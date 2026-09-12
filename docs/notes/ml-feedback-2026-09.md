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
`size_of` over float types; `Oak.Floats` models the evaluation discipline in
Lean and proves the reproducibility theorem, exact widening, commutativity,
and the reassociation and contraction counterexamples. The design:

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
3. **Done.** Operator definitions (`10-syntax.md` §14): `operator(+) add:
   (a: Vec, b: Vec): Vec` binds `+` for a left operand of `Vec`, declared
   only in `Vec`'s package, one binding per type and symbol; `a + b` is
   exactly `add(a, b)`, rewritten into the plain call after type checking so
   nothing is dispatched or hidden. The constitution's bar is met by the
   marker and the home-package rule: every `+` on a tensor names one
   function a reader can find. Declared operator properties (7.3) remain
   the follow-on.
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
| O6 | A frontend surface for `x.matmul(w).relu()` | **implemented**: uniform call syntax (`10-syntax.md` §13), operator definitions (§14), and the pipeline operator (`x \|> matmul(w) \|> relu`) |

## Tier 8 — the second numeric-runtime list (2026-09-11)

The list arrived as six items; most were already on the branch. Their state
against the current tree, with what changed today:

| # | Ask | Disposition |
| --- | --- | --- |
| 1 | Floats (tier 2) | **Already done**: `f32`/`f64` with fixed IEEE semantics, `FP_CONTRACT OFF` and `-ffp-contract=off`, `f16`/`bf16` storage, the `bits` and `round` rows, correctly rounded intrinsics, the `math` package under a fourth witness (`20-types.md` §11.3, STATUS row). Not yet: the Lean lattice model. |
| 2 | Spans across the FFI (tier 3) | **Already done** for integers, floats, storage formats, tagged unions, and proven-layout structs (`92-ffi.md` §2.5). **New today**: structs by value in extern signatures (§2.3) — Metal's struct-by-value calls and libc's `div_t` return without a pointer. |
| 3 | F13 declarations before use | **Already done**: annotated top-level bindings are predeclared (STATUS "Order-independent package scope"). |
| 3 | F14 assertions without locations | **Already done**: `assert` traps name file and line in hosted builds (STATUS "Located assertion traps"). |
| 3 | F16 `\|` inside a `?` arm | **Fixed today** (`10-syntax.md` §3b): a third bare `\|` after a Bool conditional's two arms is a parse error naming the fix; it used to parse as a bitwise or over the whole conditional. Inside a bare arm `\|` stays the separator; `(a \| b)` or a braced arm spells the operator. |
| 3 | F18 a line starting with `(` continues the expression | **Fixed today** (`10-syntax.md` §4a): a call or index never continues across a line break; a line beginning with `(` or `[` begins a new statement. |
| 3 | F19 a float conversion as a global initializer fails inside clang | **Fixed today** (`60-effects-allocation.md` §10a): conversions and float constructors over constants are compile-time constants, folded through the interpreter and emitted as literals (`HALF: f16 = f16_round_f32(0.5)`, a `[4]bf16` table, nested and inside record/array literals); anything still non-constant fails C emission with `OAK-T0501` as an Oak error naming the global and its position, never a clang error against the marker macro. |
| 4 | Pipeline operator, shape literals, `pub` constants, size-indexed parameters | **Already done** (tier 5 items 1 and 4, tier 7.1). |
| 4 | Match on integer constants | **Already done**: `x ? \| 1 => a \| 2 => b \| _ => c` typechecks and runs; the nine-deep `?` chain can be one match today. |
| 4 | `break` in bounded loops | **Done today** (`85-discipline.md` §3a): `break` leaves the innermost `while`; a certified bounded loop stays certified; executed both ways. |
| 5 | `f8` and packed 4-bit with block scales as storage types | **Done today** (`20-types.md` §11.3.1, §11.3.1a; STATUS rows). `f8e4m3` and `f8e5m2` are storage types on the `f16`/`bf16` pattern: exact widening, `round` with each format's own overflow rule (E4M3 to NaN, E5M2 to infinity), a `saturating` narrowing that clamps to the largest finite value, `bits` with `u8`, one-byte layout, `uint8_t` at the boundary; C helpers and interpreter swept against a Go reference over every pattern. Packed 4-bit is a library package, not a type: `import("mx")` gives the OCP MXFP4 block (32 E2M1 elements, one E8M0 scale, 17 proven bytes) with quantize, dequantize, and element access, written in Oak. |
| 6 | `#line` directives | **Already done** (`oak build -lines`). |
| 6 | Per-package discipline profiles | **Already done**: `profile <default\|strict>` in `oak.mod`, judged per module (`85-discipline.md` §1). |
| 6 | A trace schema so `oak test -sim` can replay a launch sequence | **Dropped, by decision.** A launch-sequence replay would need every FFI call and its arguments recorded as a trace event, and recording at the boundary adds latency to the path the project tunes for throughput; the project values that performance over the replay. `testing_trace` stays as it is (semantic events only, `110-testing.md`), and a replay design would have to find its events somewhere other than the boundary. |

## Tier 9 — the third list (2026-09-11, evening)

Six items, of which three were requests for design and three could be
answered against the tree today:

| # | Ask | Disposition |
| --- | --- | --- |
| 1 | Inbound buffers: a borrowed view over a `c.Ptr` plus length under a stated trust contract, or the `Buffer[CpuOwned]` typestate | **First increment done today** (`92-ffi.md` §2.7): inside an `unsafe` block, `v: []f32 = c.borrow[f32](p, n)` views `n` elements of runtime-owned memory and `s: [*]f32 = c.borrow_mut[f32](p, n)` writes them, for the block's extent, under the stated foreign buffer contract (the pointer addresses `n` elements with Oak's layout, stays mapped, is unaliased for writes). The borrow cannot leave the block, indexing is bounds-checked against `n`, the element types are the boundary types of §2.5.1, and each borrow is recorded as an `OAK-B0110` assumption. Readback, host-side conversion, and test comparison can move into Oak on this; uploads write through `c.borrow_mut`. The `Buffer[CpuOwned]` record that owns a foreign allocation across calls is the increment after runtime-sized arenas (§2.7.5). |
| 2 | Runtime-sized allocation and views inside records | **Done today, first increment** (`92-ffi.md` §2.8, `60-effects-allocation.md` §6): `weights: Buffer[f32] = c.own[f32](p, count)` inside `unsafe` owns a runtime allocation of any size until `free(c.disown(weights))`; `view(&weights)`/`span(&weights)` borrow it like a fixed array, so `tensor_of(view(&weights), rows, cols)` builds a `Tensor[R]` region record over it and `subslice` carves ranges; `import("arena")` reserves aligned element ranges as offsets. The `Tensor` record holding a view already worked through the region records of `50-borrowing.md` §8c — both `Tensor { data: v, rows, cols }` locally and `tensor_of(v, rows, cols)` across calls — and is now executed over a buffer. Outside this increment: a buffer inside a record or global (the custody typestate) and several writable ranges live at once (§6 disjointness or an `unsafe` assumption). |
| 3 | F19 float conversion as a global initializer | **Fixed today** (Tier 8 table above, `60-effects-allocation.md` §10a): folded, or an Oak error. |
| 4 | `pub` constants, match on integer constants, the pipeline operator | **Already done**, verified today: `pub MX_BLOCK: u32 = u32(32)` is exported and read as `mx.MX_BLOCK` (`83-modules.md` §5 example `geo.MAX_POINTS`); `op ? \| 0 => a \| 1 => b \| _ => c` typechecks, runs, and now extracts to Lean; the pipeline operator is `10-syntax.md` §12. If the packages still export `op_add(): u32` functions, that is a port left over from before exported constants landed. |
| 5 | Lean extraction reaching the ml subset | **Extended today** (`95-extraction.md` §2): integer-constant matches (the scheduler's op dispatch) extract as if-chains in value and statement position; the integer conversion rows extract (`trunc`/`bits` as Lean's wrapping conversions, `saturating` as a clamp); Oak's implicit same-signedness widening is made explicit. An ml-shaped sample — a `Shape` record of `u64`s, view algebra over a `[16]u64`, a lane reduction with a `while` loop and `%`, a window `subslice`, an op dispatch on constants — extracts, compiles under Lean 4.33.1, and `main` evaluates to the compiled program's exit code. Still outside: floats, records with more than one level of field assignment, `checked` conversions, matches over records. |
| 6 | A strict-clean prelude, or `json` under strict | **Verified clean today**: a strict-profile module importing `json`, `strings`, `hash`, or `mx`, and a strict-profile program using the derived JSON encoder, all compile without a strict diagnostic (probed against `WithProfile("strict")` and `profile strict` in `oak.mod`). If a root module still has to default, the trigger is in the module's own code; send the diagnostic and it gets a row here. |

## Follow-up asks from the authority work (2026-09-11)

Gaps the authority roadmap (milestones 1–4, `roadmap-authority-resources.md`)
ran into while landing callee-entry authority, callable boundaries,
provenance, and result contracts. The first group blocks using the features
from Oak source; the second is fixture friction that keeps recurring.

Two constraints govern every proposal here: **syntax stays lightweight** —
reuse the words and positions Oak already has, add no punctuation-heavy
clauses and at most one contextual word — and **no allocation is
introduced** (00-constitution: no hidden work). Every authority fact is
checked at compile time and erased; none of the features below adds a
runtime representation, a copy, or an allocation. Where the checker today
*forces* a copy (items 4 and 8), that is the allocation to remove.

Prerequisites for adopting the authority features:

1. **Source spelling for result identities and callable contracts.** Fresh,
   alias-of-argument, borrow-of-arguments, and mutable reborrow exist only
   as protocol declarations and SemIR effects (`return-fresh`,
   `return-alias`, `return-borrow`, `return-borrow-mut`); contracts on
   function-typed parameters (`callable-*`) likewise. `via f(consumed h)`
   covers parameter modes only. Proposal, reusing the mode words and the
   `:` result position of the `via` line, with elision like section 8c's
   region returns:

   ```oak
   via open(): fresh                         // fresh result
   via same(consumed h): h                   // alias: the result is h
   via cursor_of(borrowed a): borrowed       // borrow of every borrowed parameter (elided)
   via merge(borrowed a, borrowed b): borrowed a   // explicit origin subset
   via mut_cursor(borrowed-mut a): borrowed-mut    // mutable reborrow
   via apply(consumed h, f(consumed))        // callable contract: f's modes, positional
   ```

   `fresh` is the only new (contextual) word; a bare parameter name is the
   alias form; `borrowed`/`borrowed-mut` in result position borrow every
   parameter of that mode unless origins are named. No result clause keeps
   today's meaning (unknown, fail closed).
2. **A trusted boundary for resource primitives.** Definition-less
   declarations require an asm unit and `c.extern` requires C types, so a
   primitive such as a cursor over an arena cannot state a borrow honestly;
   today a provenance-free body is accepted for a borrow claim because a
   borrow is the most conservative claim. Proposal: no new keyword — a
   definition-less declaration that a `via` line gives a result clause is
   the trusted boundary, and the compilation requires the body from an asm
   unit or an extern as it does today.
3. **Method calls on ADT receivers do not lower to C.** Receiver contracts
   typecheck and round-trip through SemIR but cannot be executed compiled.
4. **Record-typed parameters and results carrying resource fields are not
   governed at calls.** A record with resource fields passed by value to an
   unmarked function is not checked; records holding borrowed fields
   therefore fail closed (cannot be passed or returned), which forces the
   caller to copy the borrowed value out — the one place the current rules
   cost an allocation-shaped copy. Proposal: the `via` parameter list
   accepts field paths (`via take(borrowed h.c)`), and a record result
   clause names the field (`: borrowed h.c`); no record-level mode word.

Fixture and ergonomics friction:

5. No bare block statement: scoping requires `flag ? { } | { }`, which
   matters more now that dependencies and suspension are lexical. A bare
   `{ ... }` statement is the lightest fix and allocates nothing. (`defer`
   landed 2026-09-12, `10-syntax.md` §4b, so the most common reason to
   want an inner scope — closing at a known point — no longer needs one.)
6. Statement lines cannot start with `(`, `-`, or `!`.
7. Closure literals cannot take typed parameters.
8. One protocol per resource type; array elements never carry provenance,
   so a borrowed result cannot sit in an array without copying.
9. `20-types.md` §11.3.8 should cite bf16 as the bfloat16 convention
   (Google Brain, vendor ISA documents) rather than IEEE 754, which does
   not define it.

## Roadmap disposition (2026-09-11, night)

ml's `docs/notes/oak-roadmap.md` (stages A–E) against the Oak tree, after the
Stage B branch `sam/roadmap-stage-b`:

| Item | Ask | Disposition |
| --- | --- | --- |
| A1 (F22) | a strict module may borrow runtime memory (`OAK-B0110` as an assumption severity or an `oak.mod` admission) | **Fixed** (`feat(modules): admit recorded assumptions in oak.mod so strict modules can borrow runtime memory`): the manifest directive `admit OAK-B0110` (`83-modules.md` §4.1, `85-discipline.md` §7). The admitted assumption stays recorded — `oak vet` and `:obligations` list it marked "admitted by oak.mod", `:lean` still states it — but no longer rejects that module's packages under strict; the zero-warning rule is otherwise unchanged. Admissible codes are exactly the recorded assumptions (`OAK-B0110`, `OAK-D0102`, `OAK-D0103`); an error code fails the manifest (`OAK-M0112`). Per module, like profiles: a dependency's manifest speaks for its own packages; `-profile strict` on the command line grants nothing. Tests: `compiler/e2e_strict_admit_test.go`, `modules.TestManifestAdmit`, the CLI vet case. The admission shape was chosen over an assumption severity because it keeps strict's rule intact and makes the accepted contract a reviewable line in the module. |
| B1 (F21) | assertion traps name the file, not the root directory | **Fixed** (`fix(codegen): attribute assertion traps to the token's source file`): `oak_assert` and `#line` take the file from the token's `package#file` stamp, relative to the package directory (`fuzz/fuzz.oak:4`). |
| B2 (F20, oak #149) | a slice of an inline view compiles | **Fixed** (`fix(codegen): slice inline views and spans through the checked helpers`): `view(&x)[lo:hi]` and `span(&x)[lo:hi]` classify as the view/span of `x` and lower through `oak_view_slice_T`/`oak_span_slice_T`, bounds-checked; `len(view(&x))` folds the same way. |
| B3 (F9, F10) | string literals usable directly as arguments | **Fixed** (`fix(borrow): string view conversions as call-argument temporaries`): `f(str_bytes("x"))` and `f(str_bytes(name))` borrow for the call's extent and are dropped after it (`50-borrowing.md` §12); a `string` parameter takes any tracked string (`count(who)` with `who: string = "oak"`), and the `path` package is callable with spelled text (`path_clean(dst, str_bytes("a/./b"))`). |
| B4 (F15) | shape arity | As the roadmap says: eased by list literals in argument position; closable with a note once const generics cover the `[]u32` shape parameter. |
| D1 | `c.String` from Oak bytes | **Fixed** (`feat(ffi): c.cstr hands C a NUL-terminated view for one call (D1)`): `c.cstr(v)` in an extern call stands for a `c.String` parameter and passes the base pointer of a named `[]u8` view whose last byte is NUL (checked at the call, trapping with the source position) or of a NUL-terminated literal (checked at compile time); `OAK-F0110`; a read use of the owner for the call's extent (`92-ffi.md` §2.5.3). |
| D2 | inbound C strings | **Fixed** (`feat(ffi): c.borrow_string views a NUL-terminated C string inside unsafe (D2)`): `c.borrow_string(p)` yields a `[]u8` view of the bytes before the terminator, length scanned at runtime, NULL the empty view, under `c.borrow`'s placement rule and `OAK-B0110` contract, so `getenv` results are read by Oak (`92-ffi.md` §2.7.1). |
| D3 | calls through a pointer (a `c.Ptr` from `dlsym` invoked with a declared signature) | **Fixed** (`feat(ffi): calls through a pointer with a declared signature (D3)`): `f: c.Fn[(c.Ptr, c.UInt32) -> c.Int32] = c.fn_at(p)` inside `unsafe` names the function at `p` with the annotated boundary signature; `f(args)` is checked exactly as an extern call (every argument form of §2.5), lowered to a cast-and-call, fails closed under `forbids` (`OAK-E0103`), and records the trust contract as `OAK-B0122` (strict modules `admit OAK-B0122`); `c.fn_at` of NULL traps at the conversion; `c.Fn` anywhere but that binding is `OAK-F0113` (`92-ffi.md` §2.10, `compiler/e2e_ffi_fnptr_test.go` calls `strlen` and `time` resolved through `dlsym`). |
| D4 | process spawning | **Fixed** (`feat(ffi): argument vectors, out-parameters, and the null pointer for process spawning (D4)`): `c.argv_of(bytes, slots)` forms a NUL-terminated `char *const argv[]` at the call over Oak-owned strings and `[*]c.Ptr` slots, checked for the terminator and the slot count at the call; `c.out(x)` passes the address of a local `c.*` scalar or boundary struct for one call; `c.null()` spells the optional pointers. `posix_spawn` of `/bin/echo` and `/usr/bin/false` with `waitpid` reading the status is executed (`compiler/e2e_ffi_spawn_test.go`; `92-ffi.md` §2.5.6–2.5.7). `posix_spawn`/`waitpid`/`execve` are plain externs now. |
| D6 | a clock | **Fixed** (`feat(ffi): target constants, and the native clock in pure Oak`, `92-ffi.md` §2.11, closes oak #211 and #179): `c.const("CLOCK_MONOTONIC", "<time.h>")` binds the header's constant per target, and `stdlib/timenative.oak` reads `CLOCK_REALTIME`/`CLOCK_MONOTONIC` through `clock_gettime` and `c.out` with nothing linked but the C library — the host-symbol shim is gone, so `rt.now_ns` can retire as a runtime row. History: PR #178 adds `TimeSource` (fixed, simulated, native) to `time`, `timesim` fault injection from the choice tape, and `timenative` host symbols with a POSIX shim; the FFI gap (library externs bind every importer; no out-pointer form for `clock_gettime`) is oak #179. The out-pointer half is closed by `c.out` (D4 row): a boundary-struct `timespec` can be filled in place, `gettimeofday(c.out(tv), c.null())` is executed; what remains is `CLOCK_MONOTONIC`'s host-dependent value (1 on Linux, 6 on Darwin), which needs a target-constant facility or the IO port before `time_source_native()` can leave the shim. |
| D7 | float formatting for text output | **Landed** as the `float` package (#161): shortest and correctly rounded `f64`/`f32` text, Go's `strconv` slow path in Oak, differential-tested against `strconv`; integer text via `append_u64`/`append_i64`/`text_parse_i64` (#151). |
| E1 | C ABI exports from any package | **Fixed** (`feat(ffi): C ABI exports from any package (E1)`): `export("symbol") pub name: (...)` in any package defines the function under that C symbol and lists it in the header with its package (`92-ffi.md` §2.9); symbols are C identifiers, program-unique against every other export and the root's implicit `oak_<name>` (`OAK-F0108`), and only pub non-generic free functions qualify (`OAK-F0109`). The root's implicit exports are unchanged; a dependency's plain `pub` functions no longer leak into the header under internal names. ml can split `tensor/tensor.oak` into `ops/`, `gpt2/`, `mnist/`, `checks/`, `bench/` packages that keep their own exports. |
| E2 | `oak test` linking a native runtime | **Fixed** (`feat(modules): link native libraries and frameworks from oak.mod (E2)`): `link runtime/libmlrt.a` and `framework Metal` in `oak.mod` (`83-modules.md` §4.6) name the module's native inputs; `oak build`, `oak run`, `oak install`, and `oak test` pass them to the C compiler as argv entries in link order (root first, then dependencies by module path), with the objects' bytes in the build-cache identity and the test replay fingerprint. ml's tests can be Oak tests with `Table` targets against `libmlrt.a`, and the Metal tests link on a machine with Metal (`framework Metal` is skipped with a note elsewhere). The `-adapter` manifest stays the pinned determinism assertion for `Sim` targets and composes with `link`. |
| E3 | assertions with values (`expect_eq(got, want)` naming both values) | **Fixed** (`feat(testing): assertions that name both values (E3)`): `assert_eq`/`assert_ne` builtins for fixed-width integers, `f32`/`f64`, and `Bool` print `got <a>, want <b>` at `file:line` before the trap (`85-discipline.md` §5, `OAK-T0601` on mismatched operands); `test_check_eq_*`/`test_check_ne_*` in the testing prelude carry both values into `oak test` output and JSON (`110-testing.md`). Floats print with round-trip precision; the `float` package (D7) remains the shortest-form spelling for text output. |
| E4 | Lean extraction of float code | **First increment (2026-09-11, night)**: `f32`/`f64` extract to Lean's `Float32`/`Float` — literals by bit pattern, `+ - * /`, negation, comparisons, the `round`/`bits`/`saturating`/`trunc` rows, `sqrt`/`abs`/`floor`/`ceil`/`round`/`is_nan`/`is_finite`/`is_infinite` — and `spec/lean/Oak/Stdlib/FloatKernelsExtracted.lean` commits the ml shape (`dot_f32`, `sum_f32`/`sum_f64`, `axpy_f32`, `max_abs_f32`, `widen_mean`, `quantize_u8`) with a drift test (`95-extraction.md` §2–§5). Lean's `Float` is opaque to the kernel, so theorems about extracted float code are stated against `Oak.Floats`; `fma`, `copysign`, `min`/`max`, `round_even`, `total_order`, the `checked` float rows, and `f16`/`bf16`/`f8` fail closed. |
10. Codegen: a span index inside a ternary that is a record literal's field
    value (`error: slot >= ring[0].files ? { a } | { b }`) emits raw
    `ring[0]` in C instead of the span accessor; binding the value to a
    local first avoids it (met in `stdlib/ionative.oak`, 2026-09-12, and
    again as a span read inside a call argument in a record literal field,
    `Instant { nanos: f(x, source[0].wall) }`, in `stdlib/timesim.oak`).
    The interpreter is unaffected; only the runner's and the e2e tests'
    C builds catch it, which argues for a codegen test that emits every
    stdlib package once.
11. Codegen: a `?` match with a block arm that itself contains a match
    (`r ? | .Ok(i) => false | .Err(e) => { e ? | .Overflowed => true | _ =>
    false }`) emits an empty `/* match expression */` placeholder in C when
    it is a binding's initializer; the same match as a function's tail
    lowers fine, so a small helper function avoids it (met in
    `compiler/e2e_time_interval_test.go`, 2026-09-12). The interpreter
    handles both positions.

