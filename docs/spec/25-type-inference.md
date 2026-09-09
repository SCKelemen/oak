# Type Inference and Explicit Contracts

Oak aims for **powerful, lightweight, sound inference** without making type
annotations part of ordinary implementation plumbing.

Hindley-Milner ideas are an important foundation—fresh type variables,
unification, occurs checking, generalization, instantiation, and principal types
where they exist—but Oak is not defined as a pure HM language. Its inference
system also has to cooperate with records/ADTs/GADT-style refinements, qualified
constraints, ownership, effects, regions, representation facts, and proof
obligations.

This document is normative for where Oak infers facts, where it generalizes
polymorphism, and where explicit contracts are required.

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

Inference must never guess in order to keep source short. When multiple meanings
remain possible, Oak asks for the smallest annotation that resolves the
ambiguity.

## 2. Layered inference model

Oak's inference engine is layered rather than tied to one named type-system
family.

The core layer uses HM-derived machinery where it is a good fit:

- expressions produce type constraints;
- fresh type variables stand for unknown semantic types;
- unification solves equality-compatible constraints;
- occurs checking rejects infinite/cyclic types;
- eligible bindings are generalized to reusable schemes;
- polymorphic uses instantiate fresh binders;
- principal types are preferred when the active feature subset admits one.

Additional Oak layers then refine/discharge facts that ordinary HM does not
model:

```text
core type inference / unification
        ↓
record + interface constraints
        ↓
ADT/GADT + refinement facts
        ↓
ownership / borrowing / regions
        ↓
effects + capabilities
        ↓
representation / ABI obligations
        ↓
proof obligations where required
```

These layers should cooperate through explicit semantic constraints rather than
through hidden runtime conversions.

A later layer may reject or refine an otherwise valid core unification result.
It must not silently change the runtime representation or authority of a value.

### 2.1 Accumulated equality solving

A generic invocation solves all parameter/argument equations under one
accumulated substitution. Each newly solved equation is applied before the next
sibling or parameter is checked.

Consequently:

- distinct variables may be inferred independently across multiple parameters
  and generic-application arguments;
- every occurrence of the same binder must resolve to the same semantic type;
- a conflict such as `Pair[T, T]` against `Pair[i32, string]` rejects the
  invocation rather than overwriting or ignoring an earlier binding;
- the solved substitution is applied recursively to the result type.

Equation order must not change whether a well-formed set of equality constraints
is accepted. Diagnostics may report the first source-ordered conflict.

## 3. Lightweight local programming

Ordinary local code should not need repetitive annotations:

```oak
fn transform(xs: []i32): i32
  doubled := map(xs, fn x => x * 2)
  total := fold(doubled, 0, fn acc x => acc + x)
  total
```

`doubled`, `total`, the lambda parameter/result relationships, generic
instantiations, and applicable constraints should be inferred when they are
unambiguous and sound.

The desired user experience is closer to ML/Elm/TypeScript-style inference than
to a systems language that requires every local value and generic argument to be
spelled manually.

Exact lambda syntax remains governed by the syntax specification; the semantic
rule here is independent of punctuation.

## 3a. Integer literals take their type from context

An integer literal has no type of its own. It takes the integer type its
context requires, and the checker reports an error at the literal when the
value does not fit that type. The contexts, in the order the checker consults
them:

1. A declared or assigned type: `x: u8 = 255`, `x = 0`, record fields, array
   elements, call arguments, and the return type of the enclosing body.
2. An array index or slice bound, which is `u32`.
3. The typed operand of an arithmetic, comparison, equality, or bitwise
   operator. The typed operand types the literal-only operand in either
   order: `at + 1`, `2 * at`, `1 < at`, `at * 2 + 1`, and `hcr & 0x19` all
   infer without annotation. A literal-only operand is a literal, a signed
   literal, or arithmetic over literal-only operands.

The result is that `at + 1` and `at + u32(1)` are the same expression: the
same precise type, the same range check, and the same wraparound rule. A
literal with no context at all is `int`. Inference never widens a literal to
escape a range error; `n + 300` with `n: u8` is rejected, as is `at + -1` with
`at: u32`, and mixing a typed `int` variable with a fixed-width unsigned
operand remains an error.

Formally: literal typing is a checked coercion at elaboration time, not a
subtyping rule. The elaborated program contains only precisely typed
constants, so later phases (lowering, the C backend, and the machine-integer
refinement obligations in §13) never see an untyped literal.

## 4. Explicit module and library boundaries

Externally visible declarations require explicit contracts.

A public/exported function contract includes at least:

- parameter types;
- result type;
- quantified type parameters when they are part of the API;
- required generic constraints;
- public effects/capabilities when those are caller-observable;
- ownership/borrowing obligations that callers must satisfy;
- representation/ABI requirements only when representation is intentionally part
  of the public contract.

A public/exported data contract includes the semantic type identity and any
representation contract that is intentionally public ABI.

This rule gives separate compilation a stable interface and prevents a private
implementation change from silently changing a library's public inferred
contract.

The compiler verifies implementations against explicit public signatures. It
must not silently widen, weaken, or reinterpret the declared API.

## 5. Private functions may infer more

Private/local helpers may omit types whenever inference has a unique sound
result.

Conceptually:

```oak
fn public_api(x: Request): Response
  parse := fn bytes => decode(bytes)
  checked := validate(parse(x.bytes))
  build_response(checked)
```

The public boundary is explicit. Local helper values and intermediate types are
inferred.

A private function may also infer generic parameters when doing so is principal
and safe. Public generic parameters remain explicit when they are part of the
module contract.

Whether a top-level declaration is exported is a module-system concern; this
document specifies the typing policy rather than freezing export punctuation.

## 6. Binder identity is semantic; names are ergonomic

A type variable's source name (`T`, `U`, etc.) is not its semantic identity.
Independent binders may use the same readable name without becoming the same
unknown type.

Substitution, occurs checking, generalization, instantiation, and refinement must
operate on binder identity. Human-facing names exist for source readability and
diagnostics only.

This is necessary for sound inference across nested scopes, independently
instantiated generic functions, and module boundaries.

## 7. Generalization is ownership/effect aware

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
pure/non-escaping value                    -> generalize
pure computation producing immutable data -> generalize
unique mutable capability capture         -> do not generalize unsafely
fresh region-bound allocation             -> preserve region identity
external/MMIO authority                   -> preserve authority identity
```

This keeps inference powerful without reproducing polymorphic-reference or
capability-duplication unsoundness in an imperative systems language.

The initial implementation derives conservative evidence at each local variable or named-function binding:

- owned arrays contribute mutable and unique authority;
- views contribute a region-bound barrier;
- spans contribute mutable, unique, and region-bound barriers;
- raw pointer-sized values contribute external and unresolved authority;
- closures contribute the authority of referenced outer bindings and any
  lexically contained unsafe assumption;
- invocation initializers contribute effectful and unresolved evidence until
  their callee carries a checked effect summary.

Evidence is joined monotonically: later analysis may add barriers but must never
erase an already established one. A blocked scheme retains a shared monomorphic
substitution: the first successful use that solves a remaining free variable
fixes that variable for every later use; independent call-site unifiers must not
reopen it. Function parameter and result types alone do
not count as captured authority; only the function value's environment does.
This rule is deliberately fail-closed while effect summaries and compiler-wide
region identities are being threaded through type schemes.

Writes through a function's parameters or fresh local storage do not by themselves
capture authority at the function binding. Such helpers may specialize for
multiple concrete input types; each caller still supplies separately checked
storage and borrowing obligations. Writes rooted in outer bindings retain the
corresponding captured-authority barriers.

## 8. Constraints and refinements extend inference

Inference may produce obligations in addition to equalities.

Examples include:

```text
T satisfies Position
T implements Reader
N > 0
buffer region outlives view
function effect set excludes Allocate
representation provides required ABI alignment
```

A type result is accepted only after the required obligations are discharged or
made explicit in the surrounding contract.

Qualified constraints do not imply runtime dictionaries. A call may infer a
concrete `T`, prove its record/interface obligations, and specialize normally
without boxing or a runtime interface object.

GADT/refinement reasoning may narrow types and propositions inside a pattern arm.
Where such reasoning has no principal inference result, Oak may require a local
annotation or explicit proof fact rather than guess.

## 9. Representation is orthogonal to semantic inference

Type inference may determine semantic type identity without choosing a runtime
representation.

A semantic record shape can remain representation-free. If concrete storage is
required, representation selection is a separate checked decision.

Inference must never conclude that two semantically compatible records share
layout merely because they satisfy the same shape constraint.

Likewise, selecting one of several valid representations for a semantic type
must not change its inferred semantic identity.

Representation inference, where offered, is therefore constrained selection from
explicitly legal representation policies—not semantic type inference by another
name.

## 10. When annotations are required

Oak requires an annotation when inference cannot produce one sound, stable
contract without guessing.

Important cases include:

- exported/public API boundaries;
- FFI, ABI, MMIO, wire, or explicit-layout boundaries;
- ambiguous numeric/overloaded operations after available context is used;
- recursive definitions when the intended recursive polymorphic contract cannot
  be inferred safely;
- GADT/refinement cases where local annotations are needed to guide proof or
  type refinement;
- existential/dynamic type boundaries if such features are introduced;
- effect/authority boundaries whose omission would change caller obligations;
- representation choices when multiple legal layouts remain and the choice is
  externally observable.

The compiler should request the smallest useful annotation rather than forcing a
fully annotated expression tree.

## 11. Explicit annotations are checked facts

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

## 12. Inference and tooling

Editor tooling should expose inferred facts without requiring the source to spell
them repeatedly.

Useful projections include:

- hover: inferred semantic type;
- hover: generalized scheme/quantified binders;
- hover: inferred constraints, refinements, effects, ownership, and regions when
  relevant;
- inlay hints for developers who want them;
- go-to-definition for inferred constraints and type constructors;
- diagnostics showing the conflicting constraints/facts that prevented inference;
- an "explain inferred type" view for difficult generic/refinement code.

Inlay hints are tooling, not syntax. Source remains lightweight.

## 13. Formal obligations

The inference implementation should be formalized incrementally by layer.

Core obligations include:

1. type-variable binder identity is independent of display names;
2. substitution application preserves well-formed types;
3. unification is sound: a returned substitution satisfies the equalities it
   claims to solve;
4. occurs checking rejects cyclic substitutions;
5. generalization quantifies only variables not free in the environment and does
   not duplicate forbidden authority;
6. instantiation is capture-free and fresh;
7. record/interface constraint discharge agrees with the semantic constraint
   relation;
8. refinement/GADT narrowing preserves soundness of the surrounding type facts;
9. ownership/effect/region inference preserves their respective safety
   invariants;
10. inferred local implementations satisfy explicit exported signatures;
11. representation selection cannot change inferred semantic identity.

Oak should describe the implementation by the properties it actually provides
(e.g. unification-based inference, qualified constraints, refinement-aware
checking) rather than claiming conformance to one named family for the entire
language.
