# Pattern Analysis, Exhaustiveness, and Refinement

This document is normative for Oak match coverage, redundancy, reachable-state analysis, refinement facts, and match diagnostics. It extends `30-adts-patterns.md` without introducing additional surface pattern syntax.

## 1. Design rule

Pattern matching is both an execution construct and a static proof step.

A match arm may establish facts that make later alternatives impossible. The compiler is responsible for solving those facts and explaining the result in source-level terms. The programmer should not manually encode a coverage or refinement constraint graph.

## 2. Semantic case space

Exhaustiveness is defined over **semantic cases**, not merely over the textual set of top-level constructor names.

For a closed ADT, a constructor with a finite payload induces the product of the constructor and the payload's cases.

Conceptually:

```oak
OptionBool: type =
  | Some: Bool
  | None
```

has semantic cases corresponding to:

```text
.Some(true)
.Some(false)
.None
```

Therefore:

```oak
x ?
  | .Some(true) => a
  | .None       => b
```

is not exhaustive. A valid counterexample is:

```text
.Some(false)
```

A constructor payload matched by `_` or a binding covers the entire reachable payload space for that constructor.

Nested constructor patterns compose recursively.

## 3. Open and finite domains

Closed ADTs and finite built-in domains may be completely enumerated.

`Bool` is finite:

```oak
b ?
  | true  => yes
  | false => no
```

is exhaustive.

Integer and string domains are treated as open for coverage analysis. A finite list of integer or string literals is not exhaustive without a wildcard or binding remainder.

The compiler must not infer exhaustiveness for an open domain merely because all literals currently observed in a program are covered.

## 4. Source-order usefulness

Arms are considered in source order, matching runtime selection semantics.

Let `C` be the semantic cases covered by earlier reachable arms and `A` the cases matched by the current arm.

The arm is **useful** exactly when:

```text
A - C
```

contains at least one reachable semantic case.

An arm is **redundant** when it adds no reachable case beyond earlier coverage.

Example:

```oak
x ?
  | .Some(_)    => a
  | .Some(true) => b
  | .None       => c
```

The `.Some(true)` arm is redundant because `.Some(_)` already covers it.

Redundancy is a static warning and the arm is semantically unreachable.

## 5. Refinement and impossible arms

Entering a constructor arm establishes at least the fact that the scrutinee has that constructor.

```oak
x: Option[T]

x ?
  | .Some(v) => ...
  | .None    => ...
```

Inside `.Some(v)`:

- `x` is narrowed to the `Some` constructor of `Option[T]`;
- `v` has the constructor payload type `T`;
- the constructor fact may be consumed by later refinement/proof machinery.

If an enclosing context already proves that a scrutinee can only have one constructor, an arm for another constructor is **impossible**, not merely redundant.

Conceptually, if `x` is already refined to `.Some`, then:

```oak
x ?
  | .None    => impossible
  | .Some(v) => reachable
```

has an unreachable `.None` arm.

Impossible arms are warnings and are semantically `never`.

## 6. GADT reachable case space

GADT-style matching uses the same pattern syntax and the same analyzer.

A GADT constructor may establish equalities or propositions about type indices. Those facts restrict the **reachable semantic case space** before or while checking an arm.

Exhaustiveness is required only over cases that remain reachable after applying those facts.

If the current proof context excludes every constructor, the semantic case space is empty and exhaustiveness is vacuous. The programmer must not be required to add a fake wildcard for an impossible value.

Constructor result indices use the normative declaration syntax specified in `30-adts-patterns.md`. Before coverage is computed, the equality solver unifies each constructor result with the scrutinee's indexed ADT application. Fixed-index contradictions and inconsistent repeated parameter bindings remove that constructor from the reachable semantic case set. Successful parameter bindings are emitted as arm refinement facts. General non-equality propositions are not yet part of the core solver.

## 7. Reachable arm typing

Only reachable arms participate in the type of a match expression.

A redundant or refinement-impossible arm has semantic result type `never` for the purpose of the branch join. Its body must not force a reachable branch to widen.

The compiler should avoid cascading body diagnostics from an arm whose impossibility has already been established by pattern analysis, except for diagnostics required to establish that the pattern itself is malformed.

## 8. Counterexamples

A non-exhaustive match diagnostic must provide one or more human-readable semantic witness patterns when the analyzer can construct them.

Examples:

```text
.None
.Some(false)
.Wrap(.B)
```

These witnesses use Oak-like pattern notation for diagnostics, but they are semantic diagnostic data rather than a new grammar production.

For an open scalar domain, `_` may be used as the witness meaning "some value outside the explicitly covered finite set".

A counterexample is a **semantic pattern witness**, not necessarily a single runtime concrete value. For example `.Some(_)` means some payload value remains uncovered.

Witness order is deterministic and follows the semantic/declaration traversal order rather than map iteration order.

## 9. Invalid-pattern cascade suppression

Coverage conclusions are only emitted when the coverage analysis is reliable.

If an arm contains an invalid constructor, payload shape, or literal type, the primary pattern/type diagnostic owns that failure. The compiler must not additionally claim the match is non-exhaustive based on coverage information made unreliable by the malformed arm.

Independent redundancy or impossibility facts that do not depend on the malformed arm may still be reported when they remain sound.

## 10. Diagnostic identities

The initial stable codes are:

```text
OAK-T0201  non-exhaustive match
OAK-T0202  redundant match arm
OAK-T0203  refinement-impossible/unreachable match arm
```

`OAK-T0201` is an error.

`OAK-T0202` and `OAK-T0203` are warnings tagged as unnecessary code and should provide source-level reasons/help.

Machine-readable diagnostic data for `OAK-T0201` should carry the generated counterexample patterns so LSP/editor tooling does not need to parse prose.

## 11. Formal model

`Oak.PatternAnalysis` models:

- a closed semantic case universe;
- the subset reachable under current refinements;
- coverage/exhaustiveness over reachable cases;
- redundant versus useful arms;
- counterexamples as reachable uncovered cases;
- constructor matching as a refinement equality;
- unreachable constructor arms when a refinement excludes that constructor.

The formal model is intentionally independent of parser syntax and runtime tag representation.

The same model is stated in Oak over a closed universe of eight cases — every set a bitset, a case a bit — and decided by `oak prove` (`spec/oak/patterns.oak`; `125-verification.md` §6.2), including the tie between the verdict and the reported witness: a match is exhaustive or its first uncovered reachable case is a counterexample.

A proved semantic model is not an implementation refinement. The Go coverage tree is tested against the same laws, but an explicit machine-checked correspondence is still required before this feature receives `R` status.

## 12. Required properties

The implementation must preserve these properties:

1. every reported counterexample is reachable and uncovered;
2. a match is accepted as exhaustive only when no reachable semantic case remains uncovered;
3. a redundant arm contributes no new reachable semantic case;
4. an impossible arm matches no case allowed by the current refinement;
5. nested constructor/payload patterns are analyzed recursively;
6. unreachable arms do not widen the result type;
7. malformed patterns do not create derivative exhaustiveness noise;
8. coverage and witness generation are deterministic;
9. coverage never depends on runtime representation/layout choices.
