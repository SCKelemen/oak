# Diagnostics and Error Experience

This document is normative for Oak compiler diagnostics.

Diagnostics are part of the programming language user experience. They are not
an afterthought of parsing or type checking and they are not merely strings
printed when compilation fails.

Oak's rule is:

> **The compiler is the constraint solver. Diagnostics explain the result in
> programmer concepts.**

The programmer should not have to reconstruct the compiler's constraint graph
from internal terminology, anonymous type variables, or a cascade of secondary
failures.

## 1. First-class diagnostic values

Every compiler diagnostic is a structured semantic value with at least:

- severity;
- stable diagnostic code;
- semantic category;
- short human-facing title;
- exactly one primary source cause;
- zero or more secondary source labels;
- zero or more explanatory notes;
- zero or more actionable help messages.

CLI text, LSP diagnostics, editor hyperlinks, JSON output, tests, documentation,
and future debugger/tooling views are projections of the same diagnostic value.
No renderer is the semantic source of truth.

Compatibility APIs may temporarily accept plain strings while old compiler
phases migrate, but new load-bearing diagnostics should be structured at the
point where the semantic failure is known.

## 2. Stable codes

Diagnostic wording may improve. Diagnostic identity must remain stable.

Codes use the `OAK-<category><number>` family. Initial category prefixes are:

| Prefix | Category |
| --- | --- |
| `P` | parsing / syntax |
| `T` | types / inference / constraints |
| `B` | borrowing / ownership / lifetime authority |
| `E` | effects / capabilities |
| `R` | representation / layout / ABI |
| `S` | source / encoding / location |
| `C` | compiler pipeline / configuration |
| `I` | internal compiler invariant failure |

`0000` is the migration fallback for an otherwise structured diagnostic whose
specific stable code has not yet been assigned. User-facing production errors
should migrate toward specific nonzero codes.

Severity is not encoded into the code. A code identifies the semantic condition,
not how one particular compiler mode chooses to display it.

## 3. Primary and secondary causes

A diagnostic has exactly one **primary** source cause: the place where the
compiler needs the programmer's attention.

Other relevant source ranges are **secondary** labels. They answer questions
such as:

- where a conflicting type came from;
- where a borrow began;
- where backing storage ends;
- where a generic requirement was declared;
- where an inferred effect was introduced;
- where a concrete representation was selected.

The compiler should prefer causal explanations over proximity. The token nearest
the final failure is not necessarily the most useful primary label.

For example, a view escape should conceptually read:

```text
error[OAK-B....]: view escapes its backing storage

  primary: returned view escapes here
  secondary: backing storage ends here
  note: the view does not own the referenced bytes
  help: return an owned value or keep the backing storage alive
```

The message should not require the programmer to understand an internal region
variable unless that variable is genuinely part of an explicit public contract.

## 4. Explain programmer concepts, not solver internals

Oak may internally solve:

- unification constraints;
- ownership and exclusivity constraints;
- region containment;
- effect/capability requirements;
- GADT/refinement propositions;
- record-shape predicates;
- representation/layout obligations.

Diagnostics translate those failures into the abstraction the programmer used.

Prefer:

```text
view escapes its buffer
```

over:

```text
region r17 does not outlive region r23
```

Prefer:

```text
`Point3` does not satisfy `Position`
missing required field `y: f32`
```

over a raw failed predicate dump.

Prefer:

```text
this call inferred `T = Packet`
`Packet.payload` is writable, but the function requires a read-only view here
```

over anonymous unification-variable output.

Internal facts may be available in an expanded "explain" view for compiler
engineers and advanced users, but ordinary diagnostics lead with source-level
semantics.

## 5. Inference diagnostics

Because Oak intentionally minimizes routine annotations, inference failures are a
major part of the language interface.

An inference diagnostic should report the smallest useful conflict:

1. the value/expression whose type could not be established;
2. the strongest useful facts the compiler inferred;
3. the two requirements that conflict, when applicable;
4. the smallest annotation or program change that can resolve ambiguity safely.

Do not respond to an inference failure by demanding a fully annotated expression
tree when one local annotation is sufficient.

If inference has multiple valid semantic answers and no principal/stable answer,
Oak asks for an annotation rather than guessing.

## 6. Borrowing and ownership diagnostics

Borrow diagnostics should describe ownership operations and storage relationships:

- owner;
- view/span creation;
- mutable/read authority;
- overlap;
- escape;
- move/consume;
- backing storage lifetime.

Views and spans exist partly so ordinary code does not need explicit lifetime
syntax. Diagnostics must preserve that abstraction: users should normally see
"view", "span", "owner", "buffer", and the relevant source expressions rather
than solver-generated lifetime names.

When two writable spans overlap, show both ranges. When storage ends before a
view, show both endpoints. When an owner was moved, show the move and the later
use.

The first stable borrow-conflict family is:

| Code | Meaning |
| --- | --- |
| `OAK-B0101` | a view/span binding is reassigned while it still carries borrowed access |
| `OAK-B0102` | an owner is used directly while a writable span has exclusive access |
| `OAK-B0103` | an owner is mutated while read-only views are active |
| `OAK-B0104` | a read-only view is requested while writable span access is active |
| `OAK-B0105` | a writable span is requested while read-only views are active |
| `OAK-B0106` | writable span regions overlap or cannot be proved disjoint |

For `OAK-B0106`, known regions use half-open interval semantics. The diagnostic
should show the requested region and one earliest causal conflicting span. If a
region is unknown, Oak fails closed and explains that it could not prove the two
writable regions disjoint. It must not describe this conservative rejection as a
proven overlap.

When several active borrows could explain the same conflict, the compiler should
choose causal context deterministically, preferring the earliest relevant source
borrow. Map iteration order, allocation order, or internal pointer identity must
never select the explanation.

## 7. Help must be safe and mechanically credible

A `help` message is actionable advice, not speculation.

The compiler must not recommend a transformation that:

- weakens type safety;
- inserts a hidden runtime cast;
- changes ownership unexpectedly;
- introduces allocation without saying so;
- changes ABI/layout silently;
- broadens effects/capabilities unexpectedly;
- relies on `unsafe` merely to silence the checker.

When several repairs are possible, prefer describing the semantic choices rather
than pretending one rewrite is universally correct.

## 8. Suppress cascades

One root cause should not produce a wall of derivative errors.

Compiler phases should mark poisoned/unknown facts after a primary error and avoid
reporting consequences that add no new information. A later diagnostic is useful
only if it is independently actionable or explains a distinct cause.

The quality target is not "maximum number of detected inconsistencies". It is
"minimum set of diagnostics that lets the programmer understand and repair the
program".

## 9. Exact locations and links

Diagnostics use Oak's canonical UTF-8 byte spans and source identity internally.
Editor coordinates are derived exactly as UTF-16 positions.

All human-facing source locations should be able to project to:

- `filename:line:column` terminal links;
- `vscode://file/...:line:column` links;
- exact LSP ranges;
- source excerpts/code frames.

A renderer must not estimate a range from byte length when exact source spans are
available.

## 10. Determinism

Given the same source, compiler version, target options, and diagnostic mode,
diagnostic ordering and semantic contents are deterministic.

Map iteration order, pointer addresses, internal fresh-variable numbering, and
other unstable implementation details must not leak into user-facing output.

This is required for reproducible builds, golden tests, editor stability, and
useful bug reports.

## 11. Testing policy

Important diagnostics should have two kinds of tests:

1. **structural tests** — stable code, category, severity, labels, notes/help,
   source ranges and machine-readable data;
2. **presentation tests** — concise rendering snapshots for representative human
   output.

Structural assertions are authoritative. Wording snapshots may change when the
new wording is demonstrably better, without changing the diagnostic code.

Tests should include Unicode source positions, layout syntax, nested inference,
borrow/region failures, record-shape failures, and multi-source context where
applicable.

## 12. Internal compiler errors

A compiler invariant failure is not a user program error.

Internal failures use the internal diagnostic category and should identify:

- the violated compiler invariant;
- the compiler phase;
- relevant source location if known;
- enough structured context to file a reproducible compiler bug.

The compiler must not disguise an internal invariant failure as a type error or
encourage the programmer to rewrite valid source to avoid it.

## 13. Design test

For every new checker feature ask:

> Can a programmer understand this failure from the diagnostic without manually
> becoming the compiler's constraint solver?

If not, the feature is not complete from Oak's user-experience perspective.
