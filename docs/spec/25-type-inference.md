# Type Inference and Explicit Contracts

Oak aims for Hindley-Milner-style inference ergonomics without making type
annotations part of ordinary implementation plumbing.

This document is normative for where Oak infers types, where it generalizes
polymorphism, and where explicit type contracts are required.

## 1. Design rule

The default rule is:

```text
inside an implementation:
    infer as much as is unambiguous and sound

at an exported/module/library boundary:
    require an explicit contract
```

This is intentional. Local code should feel lightweight; public APIs should be
stable, reviewable, documentable, and suitable for separate compilation and
formal reasoning.

Annotations are therefore primarily **contracts**, not ceremony.

## 2. HM-style local inference

Oak's core inference model is HM-style:

- expressions produce type constraints;
- fresh type variables stand for unknown types;
- unification solves compatible constraints;
- occurs checking rejects infinite types;
- eligible bindings are generalized to type schemes;
- each use of a polymorphic binding is instantiated with fresh type variables;
- qualified constraints are carried as compile-time predicates over quantified
  type variables.

The implementation target is principal typing whenever the active feature set
admits a principal type.

For example, ordinary local code should not need repetitive annotations:

```oak
fn transform(xs: []i32): i32
  doubled := map(xs, fn x => x * 2)
  total := fold(doubled, 0, fn acc x => acc + x)
  total
```

`doubled`, `total`, the lambda parameter/result relationships, and generic
instantiations should be inferred when they are unambiguous.

Exact lambda syntax remains governed by the syntax specification; the semantic
rule here is independent of punctuation.

## 3. Explicit module and library boundaries

Externally visible declarations require explicit contracts.

A public/exported function contract includes at least:

- parameter types;
- result type;
- quantified type parameters when they are part of the API;
- required generic constraints;
- public effects/capabilities when the effect system makes them observable;
- ownership/borrowing obligations that callers must satisfy.

A public/exported data contract includes the semantic type identity and any
representation contract that is intentionally public ABI.

This rule gives separate compilation a stable interface and prevents a private
implementation change from silently changing a library's public inferred type.

The compiler may verify that an explicit public signature is at least as general
as, or exactly matches according to the applicable contract rule, the inferred
implementation. It must not silently widen or weaken the declared API.

## 4. Private functions may infer more

Private/local helpers may omit types when inference has a unique sound result.

Conceptually:

```oak
fn public_api(x: Request): Response
  parse := fn bytes => decode(bytes)
  checked := validate(parse(x.bytes))
  build_response(checked)
```

The public boundary is explicit. Local helper values and intermediate types are
inferred.

Whether a top-level declaration is exported is a module-system concern; this
document specifies the typing policy rather than freezing export punctuation.

## 5. Generalization is ownership/effect aware

Oak is not a purely functional language. It has mutation, unique authority,
arenas/regions, raw pointers, effects, and explicit storage.

Therefore Oak must not adopt unrestricted ML let-polymorphism in cases where it
would make mutable or region-bound state polymorphically aliasable.

The soundness rule is:

> A binding may be generalized only when doing so cannot duplicate or widen
> authority over mutable, unique, external, or region-bound state.

A conservative implementation may use a traditional value restriction. A more
precise implementation may generalize a wider class of expressions when the
ownership/effect checker proves that the binding does not capture unsafe mutable
or escaping authority.

The long-term preferred rule is proof/effect based rather than syntax based:

```text
pure/non-escaping value                  -> generalize
pure computation producing immutable data -> generalize
unique mutable capability capture       -> do not generalize unsafely
fresh region-bound allocation           -> preserve region identity
external/MMIO authority                 -> preserve authority identity
```

This keeps inference powerful without reproducing the polymorphic-reference
unsoundness that unrestricted generalization would introduce in an imperative
systems language.

## 6. Constraints do not imply runtime dictionaries

Qualified inference may infer a concrete type argument and then discharge
record-shape or method/interface constraints at compile time.

For example:

```oak
Position: type = { x: f32, y: f32 }

fn length2[T: Position](p: T): f32
  p.x * p.x + p.y * p.y
```

A call with a concrete `T` should infer `T`, prove the `Position` obligation,
and specialize normally. Inference does not imply boxing, a runtime interface
object, or a dictionary unless a future feature explicitly requests such a
representation.

## 7. Representation is not inferred from semantic shape

Type inference may determine semantic type identity without choosing a runtime
representation.

A semantic record shape can remain representation-free. If concrete storage is
required, representation selection is a separate checked decision.

Inference must never conclude that two semantically compatible records share
layout merely because they satisfy the same shape constraint.

Likewise, selecting one of several valid representations for a semantic type
must not change its inferred semantic identity.

## 8. When annotations are required

Oak requires an annotation when inference cannot produce one sound, stable
contract without guessing.

Important cases include:

- exported/public API boundaries;
- FFI, ABI, MMIO, wire, or explicit-layout boundaries;
- ambiguous numeric or overloaded operations after available context is used;
- recursive definitions when the implementation cannot infer the intended
  recursive polymorphic contract safely;
- GADT/refinement cases where local annotations are needed to guide proof or
  type refinement;
- existential/dynamic type boundaries if such features are introduced;
- effect/authority boundaries whose omission would change caller obligations.

The compiler should request the smallest useful annotation rather than forcing a
fully annotated expression tree.

## 9. Explicit annotations are checked facts

An annotation constrains inference; it does not bypass it.

The checker must verify the implementation against the annotation and report a
precise mismatch at the source boundary. An annotation must not silently cause:

- a runtime cast;
- boxing;
- allocation;
- narrowing;
- layout reinterpretation;
- authority escalation.

Those operations require their own explicit semantics.

## 10. Inference and tooling

Editor tooling should expose inferred facts without requiring the source to spell
them repeatedly.

Useful projections include:

- hover: inferred semantic type;
- hover: generalized type scheme;
- hover: inferred effects/ownership when available;
- inlay hints for developers who want them;
- go-to-definition for inferred constraints and type constructors;
- diagnostics showing the two constraints that failed to unify;
- an "explain inferred type" view for difficult generic code.

Inlay hints are tooling, not syntax. Source remains lightweight.

## 11. Formal obligations

The inference implementation should be formalized incrementally.

Required proof targets include:

1. substitution application preserves well-formed types;
2. unification is sound: a returned substitution makes both input types equal;
3. occurs checking rejects cyclic substitutions;
4. generalization quantifies only type variables not free in the environment;
5. instantiation is capture-free and fresh;
6. qualified constraint discharge agrees with the semantic constraint relation;
7. ownership/effect-aware generalization cannot duplicate forbidden authority;
8. inferred local implementation types satisfy explicit exported signatures.

Oak may describe its current compiler as **HM-style** while these pieces are
implemented incrementally. It should claim full/principal HM inference only for
the subset for which those properties actually hold.
