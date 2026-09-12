# Note: algebraic structures as Oak's internal semantic models

**Status: proposal / direction.** 2026-09-12, `specification` branch.
Sources: C#'s query pattern (any type with structurally matching
`Select`/`SelectMany`/`Where` participates in LINQ; the compiler desugars
query syntax to those calls; the monad laws are what make a query provider's
rewriting sound) and its `Task`/`await` machinery (a monad with `await` as
bind, `Task.WhenAll` as the applicative); Wadler's "Monads for functional
programming"; Gibbons and Oliveira, "The essence of the iterator pattern"
(applicative traversals); Atkey's indexed monads; Katsumata's graded monads;
Uustalu and Vene on comonadic streams; Rutten's universal coalgebra; the
fold/build short-cut fusion literature (Gill, Launchbury, Peyton Jones);
Bernardy et al. on linear types and comonoids. Against: `00-constitution.md`,
`05-ergonomics-and-cost.md`, `10-syntax.md` §14a, `30-adts-patterns.md`,
`50-borrowing.md` §9, `55-parallelism.md` §4/§6/§7, `56-kernels.md` §6,
`60-effects-allocation.md` §2a, `71-codecs.md` §1–§4a/§11, `110-testing.md`,
`112-protocols.md`, `120-io.md`, `125-verification.md`, `stdlib/reduce.oak`,
`spec/lean/Oak/Reduce.lean`.

## 1. The principle

Oak already has one law consumer end to end: `laws { associative }` on an
operator definition (`10-syntax.md` §14a) is the *only* permission a backend
has to regroup; `:lean` states the law as `law_add_associative` over the
extracted operator; `Oak.Reduce.tree_eq_chainFold` is the theorem the type
checker's rewrite of `reduce.tree` to `reduce.chain` rests on, and
`LawLowerings` lists every site it fired on. That is the whole method, and
this note proposes to apply it deliberately to the structures the language
already contains without naming them.

The stance is structural, not nominal — LINQ's query pattern and Go's
interfaces, not Haskell's type classes. A type *participates* in a model
because it has operations of the right shape; a type *licenses* rewrites
because its author declared laws, and each law is a theorem over the
extraction that can be proved rather than trusted. There is no `Monad`
interface, no higher-kinded type, no `Functor` keyword in the surface, and
nothing is assumed: undeclared is unlicensed, as an undeclared effect fails
a `forbids` (`60-effects-allocation.md` §2). The structures live in three
places only — the spec's semantic prose, the Lean models, and the compiler's
rewrite rules — and the user writes records, matches, and loops.

## 2. Oak construct → model → what it buys

| Oak construct (today) | Model | What the model licenses or explains |
| --- | --- | --- |
| `Result[T, E]`, `Option[T]`; `r ? \| .Ok(v) => … \| .Err(e) => .Err(e)` (`stdlib/encoding.oak` `hex_encode`) | monad; `Result` also a `MonadError` over `E` | a propagation form (§5) lowering to the tag test and early return, no allocation; left identity, right identity, and associativity license flattening nested matches and the checker's dead-arm elimination; the codecs' precedence rule (`InvalidEncoding` over every other error, `71-codecs.md` §13) is a lawful `catch` that the root wrapper applies once |
| `laws { associative, commutative }`; `reduce.tree`/`left`/`chain`/`fold`/`tree_map` (`stdlib/reduce.oak`); `simd.reduce_add` (`93-simd.md` §1.2a); `encoded_size` sums (`71-codecs.md` §4a) | monoid / semigroup (the law set is the structure; the `zero` argument is the identity when `laws { identity(zero) }` is declared) | regrouping and parallel reduction (`55-parallelism.md` §4); `tree_eq_chainFold` today, `fold_eq_tree_map`; horizontal SIMD sums; an `identity` law lets the empty-view case and the tail merge fold away |
| pipelines `\|>`; `map`/`filter`/fold combinators (`05-ergonomics-and-cost.md` "Iterators and functional combinators"); codec fusion (`71-codecs.md` §4a, §11); ml's boundary fusion (`docs/notes/codec-fusion-lessons-2026-09.md`) | functor; fold/build (short-cut) fusion | `map f ∘ map g = map (f ∘ g)` and `fold k z (build g) = g k z` are the license theorems for fusing a pipeline into one loop with no intermediate storage — the same shape as ml's "inlining non-boundaries equals the graph value" |
| `simd.U8x16` lane-wise ops; `par.map`/`par.for` (`55-parallelism.md` §1–§2); kernel launch grids (`56-kernels.md` §6, `Oak.Kernel.run_perm`) | applicative (fixed-shape for vectors; the independence condition of §2 is exactly "applicative, not monadic": no lane or thread depends on another's result) | vectorize or parallelize when independence is proven; `run_perm` is the applicative's commutation law stated over threads; a `par.map` whose body's effects are `{ }` is a traversal in the identity applicative |
| derived codecs (`71-codecs.md` §12–§15); `derive.equal` (`10-syntax.md` §14) | traversable / foldable over the record's field list | encode is a traversal with a writer, decode a traversal with a parser state, equality a fold with `&&`; one traversal of the field list per record, instantiated per consumer, replaces per-operation generators in `compiler/codecs.go` |
| choice tapes (`110-testing.md`; `test_byte`, `test_range`, `test_bool` over `TestChoices`); the IO port with `replace io => iosim \| ionative` (`120-io.md`) | free monad over a `Choice` (resp. IO-op) functor, interpreted several ways | one generator program, three interpreters: fresh randomness, exact replay from a tape, shrinking by shortening the tape — replay and shrinking become theorems about interpretations, not runner behavior; the IO consumer text is one program, `iosim` and `ionative` are two interpreters of one operation set |
| protocol declarations (`112-protocols.md` §1); their projection (§2), shift-DFA lowering (§2a), DST actions (§3), TLA+ module (§4), `-conform` (§4a), `oak prove` over reachable states | coalgebra `S → F S` (an unfold); conformance is bisimulation | every consumer reads the one coalgebra; `conform_reachable_equal` is a bisimulation check by another name; a coalgebraic statement makes "the DFA lowering is the declaration" a theorem about the same structure |
| the block scan with `simd.prev_u8x16` and carried `prev_input`/`prev_incomplete` (`stdlib/utf8.oak`); tiled kernels | stream comonad (current block with the context of the blocks before it) | honest verdict: it names the shape — `extract` is the current block, `extend` applies the classifier to every position with its context — and it is the right *specification* form for the stream proof (`Oak.Utf8Blocks`); in code it is state threaded through a loop, and should stay that |
| effect rows `effects { … }`/`forbids { … }` (`60-effects-allocation.md` §2a); typestate `Segment[S]` with `via` (`112-protocols.md` §5a); regions `View[u8, R]` (`50-borrowing.md` §8c) | graded monad (grade = effect set, union as the monoid) for effects; Atkey-style indexed state monad for typestate (the index changes across a bind: `Segment[Fresh] → Segment[Published]`); region-indexed for borrows | `perform_subset_bound`/`forbids_sound` are the graded-monad laws; the typestate soundness theorem (`Oak.Typestate`: static index equals machine state) is the indexed-monad coherence; stating them so lets one Lean development serve three checkers |
| codec producers and consumers (`71-codecs.md` §1); refinements and predicates | covariant functor (producer, `map`), contravariant functor (consumer, `contramap`: pre-compose an encoding onto a writer), a profunctor for the codec pair (weePickle's `From`/`To`) | `contramap` is what makes a consumer over `T` a consumer over any `U` with a known `U → T` — a policy phantom (`71-codecs.md` §2) composed onto a writer without a new derivation |
| copyable values vs consumed resources (`50-borrowing.md` §9) | a copyable type carries a comonoid (`dup`, `drop`); a resource does not | the consume checker is the absence of a comonoid; brief, but it is the fact behind "a consumed binding is invalid" and why resources cannot be captured twice |
| record field paths in extent facts (`t.block[t.filled]`, `50-borrowing.md`) | lenses / optics | does not earn a place yet: the paths are read-only facts about storage, and a lens law (`get ∘ set = id`) buys nothing the kill-on-write rule does not already say. Revisit if `derive` gains field-wise transformations |

## 3. Where it pays: verification

Every law becomes a theorem over the extracted function, exactly as
`law_add_associative` is today. The additions:

- **Law vocabulary.** `laws { associative, commutative }` grows to
  `identity(zero)` (making a declared monoid), `idempotent`, and, for
  unary functions, `involutive`. Each name has one Lean statement shape;
  `:lean` emits `law_<name>_<law>` with `sorry`, `oak prove` decides it over
  small domains (`125-verification.md` §3: `u8`, `u16`, payload-free sums,
  records of those), Lean proves the rest.
- **Structure laws stated once over stdlib definitions.** `Result` and
  `Option`'s monad laws, `reduce.fold`'s relation to `reduce.tree` under a
  monoid (`fold_eq_tree_map` is one of them already), `map_compose` for the
  combinators when they exist — proved in `spec/lean/Oak/` over the
  definitions the stdlib extraction produces, so they are facts about the
  shipped code, not about a model beside it.
- **Licensed rewrites cite the law.** `LawLowerings` already records the
  operator and the site; extend the record with the theorem name, so
  `oak vet` lists `reduce.tree → reduce.chain by Oak.Reduce.tree_eq_chainFold`
  next to the assumptions, and a rewrite without a proved theorem behind it
  is visibly an assumption.
- **Declared but unproved is an obligation.** A `laws { … }` whose theorem
  is `sorry` stays in `:obligations` and is an `admit`-able warning under the
  strict profile, like `OAK-D0103` — the author's claim is auditable, never
  silent (`85-discipline.md` §7).

Example: a user declares a merge for a histogram type and a reduction over a
view of histograms.

```oak
operator(+) merge: (a: Hist, b: Hist): Hist laws { associative, commutative, identity(hist_zero()) } = ...
total: Hist = reduce.tree(views, hist_zero(), merge)
```

`:lean` states `law_merge_associative`, `law_merge_commutative`,
`law_merge_identity_left`, `law_merge_identity_right`; `oak prove` refutes
any of them over a small `Hist` domain with a counterexample or leaves them
to Lean; the checker lowers the `tree` to a `chain` by `tree_eq_chainFold`
and, with `identity`, drops the empty-view special case. Nothing about
floats changes: `f32` `+` declares nothing and keeps its tree (F2/F3).

## 4. Where it pays: compilation

| Rewrite | License | Legality rule it lives under |
| --- | --- | --- |
| `reduce.tree` → `reduce.chain`; parallel or SIMD regrouping of a reduction | declared `associative` (+ `commutative` for reordering, + `identity` to drop the zero case) — `Oak.Reduce.tree_eq_chainFold` | `55-parallelism.md` §4, `10-syntax.md` §14a (done for the first) |
| fusing `map f` after `map g` into one pass; fusing a fold with the producer of its input | functor law `map_compose`; fold/build law — both provable over the combinator definitions | `05-ergonomics-and-cost.md` "Optimization is constrained by semantics", `55-parallelism.md` §6; the codec-fusion discipline: the unfused form stays as the oracle and a counter asserts the fusion fired |
| lowering `Result`/`Option` propagation to a tag test and early return; flattening nested `?` matches; deleting arms the monad laws make unreachable | the monad laws for `Result`/`Option` stated in Lean over the stdlib types | `05-ergonomics-and-cost.md` "Expressions do not imply allocation" (a bind is a tag test; nothing is boxed) |
| vectorizing or parallelizing a `par.map`/kernel body; reordering thread execution | applicative independence: `Oak.Kernel.run_perm`, `55-parallelism.md` §2's independence facts | `55-parallelism.md` §2, §6; `56-kernels.md` §6 |
| choosing an interpreter for a program over an operation set — `iosim` or `ionative`, fresh randomness or a replay tape | the program is the same free-monad term; the interpreter is selected by the manifest's `replace` or the runner's mode | `120-io.md` §1, `110-testing.md` (replay identity) |
| specializing a codec consumer through `contramap` instead of deriving a second writer | the contravariant functor law (`contramap (f ∘ g) = contramap g ∘ contramap f`) | `71-codecs.md` §4 "Zero cost, defined": no visitor object, monomorphized composition |

Every entry keeps the constitution's rule: a transformation is legal only when
it preserves values, machine numerics, borrow and resource flow, effect
ordering, observable traps, synchronization, and ABI obligations. The law is
the *additional* fact that makes a value-changing reordering value-preserving.

## 5. Where it pays: tooling

- **One desugaring shape.** The constitution asks that sugar normalize to a
  smaller core. The query-pattern move gives several surfaces one target:
  a `Result`/`Option` propagation form, `\|>` pipelines, `par.*`, the fluent
  codec `from[Json](x).to[T]()`, and test generators all desugar to calls on
  operations of a known shape, and the same rewrite engine (the type
  checker's law lowering today) applies the laws. No new special forms.
- **Propagation.** Today `Result` chaining is spelled by hand
  (`size ? \| .Err(reason) => .Err(reason) \| .Ok(needed) => …`,
  `stdlib/encoding.oak`). A propagation form — spelling to be chosen so it
  does not collide with the `?` match (a postfix `?` is taken; `try e` or
  `e!` are candidates) — lowers to exactly that match with the `Err` arm
  re-raising, so it is sugar for what the library already writes and costs
  what a match costs. The `MonadError` view says what the re-raise may do:
  nothing but pass the error, or apply the declared precedence.
- **Explaining a lowering.** Because each rewrite cites a theorem, the LSP
  and `oak vet` can say *why* a program's `reduce.tree` became a chain or
  why two maps became one loop, and a user who reads `LawLowerings` sees the
  law, not folklore (`05-ergonomics-and-cost.md` "Performance transparency").
- **Derive by traversal.** `compiler/codecs.go` and `compiler/codec_decode.go`
  each walk the field list with their own generator. A traversal of the
  record's fields instantiated per consumer (writer, parser, equality, hash,
  size) is one walk with several algebras, and adding a format (dbs's
  binary codec, `docs/notes/dbs-feedback-2026-09.md` ask 9) becomes a new
  algebra rather than a new walker.
- **Tests as programs.** Stating the choice tape as an interpretation makes
  "a shorter tape is a run with fewer faults" and "replay is exact" theorems
  about one interpreter pair rather than properties the runner is trusted to
  have (`110-testing.md` "Choice tapes and property testing").

## 6. What not to do

- No type classes, no higher-kinded types, no `Monad`/`Functor`/`Applicative`
  in the surface. A user never writes an instance; a type participates by
  shape and licenses by declared laws.
- No hidden allocation to make a bind uniform. A `Result` bind is a tag test
  and a branch; an `Option` bind is a tag test; a traversal over a record is
  the unrolled field sequence. If a structure cannot be realized without
  boxing or a closure environment, it is not admitted (`05-ergonomics-and-cost.md`
  "Function values and closures").
- No assumed laws. Undeclared means unlicensed; a rewrite that needs a law
  the author did not state is not performed, and a declared law that is not
  proved is an obligation, never a silent fact.
- No reordering of floating-point reductions without the declared law.
  `f32` `+` is not associative and declares nothing; the grouping a program
  names is the grouping computed (`55-parallelism.md` §4, F2/F3).
- Comonads, free monads, and coalgebras are models in the spec and in Lean.
  They explain the block scan, the choice tape, and the protocol machine, and
  they are the form in which the theorems are stated; the code stays loops,
  records, and switch tables, in the strict profile.
- No lens vocabulary until it earns a theorem the field-path rules lack.

## 7. Order of work

Each increment lands with tests under both lowerings and a Lean statement,
in the codec-fusion note's discipline (oracle kept, counter asserts the
rewrite fired):

1. **Law vocabulary.** `identity(e)`, `idempotent`, `involutive` beside
   `associative`/`commutative` in `10-syntax.md` §14a; `:lean` shapes for
   each; `oak prove` deciding small instances; `LawLowerings` carrying the
   theorem name into `oak vet`. *Status (2026-09-12): `identity(e)` and
   `idempotent` landed — parser, checker (element typed against the
   operand), `:lean` shapes, and `oak prove` deciding or refuting
   `law_<fn>_<law>` over record operands of small scalars
   (`prove/laws.go`). `involutive` waits for unary operators; the
   `identity`-drops-the-empty-case lowering and the vet theorem name are
   the next consumer.* Then the monad laws for `Result`/`Option`
   and `fold_eq_tree_map`'s siblings stated over the stdlib extraction in
   `spec/lean/Oak/` — most are provable today.
2. **Propagation form for `Result`/`Option`.** Check first that nothing
   exists beyond the `?` match; choose a spelling that does not collide with
   it; lower to the tag-test match the stdlib already writes; rewrite one
   stdlib module (`encoding.oak`) as the differential witness; state the
   lowering's identity theorem.
3. **Map fusion in the combinator lowering.** When `map`/`filter` over views
   land (`05-ergonomics-and-cost.md` names them; `stdlib/reduce.oak` has the
   folds), fuse `map f ∘ map g` by `map_compose` with the unfused pipeline as
   oracle and an emitted-C counter asserting one loop.
4. **The choice tape as an interpretation.** `Oak.Choice` (Lean): a
   generator is a term over a `Choice` functor; the random, replay, and
   shrinking interpreters; theorems that replay of a recorded tape reproduces
   the run and that a prefix tape is a run with fewer choices — the runner's
   existing behavior restated as proved properties.
5. **Protocols as coalgebras.** Restate `112-protocols.md`'s declaration as
   `S → F S` in `Oak.Protocol*`, with the DFA lowering, the DST action, and
   the TLA+ projection as morphisms from it and `-conform` as bisimulation;
   `conform_reachable_equal` is the first theorem to re-derive.

Revisit criteria: a rewrite is proposed that no declared law licenses (the
vocabulary is short); the derive code gains a third walker (the traversal is
overdue); a consumer asks for `await`-shaped composition over the IO port's
completions (the free-monad view says what that is and what it must not
allocate).
