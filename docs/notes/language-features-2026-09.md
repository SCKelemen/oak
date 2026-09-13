# Note: a correctness-checklist pass over `try` and alignment facts

**Status: findings fixed the same day, three left open.** 2026-09-13,
`specification` branch. Targets: the two language features added this
session and their readings — the propagation form `try`
(`docs/spec/10-syntax.md` §2d; parser, `compiler/try.go`, checker,
interpreter, C backend, `Oak.Propagation`, the stdlib extraction) and
alignment facts on views and spans (`docs/spec/50-borrowing.md` §2a;
parser, `typechecker`, the lattice, template substitution, the C backend,
the I/O port's `io_open_region_aligned`). Lists walked:
`docs/checklists/correctness.md` §3, §4, §5, §6, §9, §10, §11. The method is
`docs/checklists/README.md`; two research agents executed their findings
with scratch programs through both realizations, and one pre-existing
checker bug surfaced while writing the tests.

## Alignment facts

Severity: **break** (a fact obtainable without the property), **divergence**
(readings differ), **unstated**, **discipline**.

| # | Finding | Severity | Disposition |
| --- | --- | --- | --- |
| A1 | A `struct(packed)` record's array field carried the element's natural alignment: `span(&p.words)` of `struct(packed) { tag: u8, words: [4]u64 }` was `[* align 8]u64` while C placed `words` at offset 1. Executed: a C probe read a misaligned base. | break | **Fixed**: `borrowAlignment` reads `Layout.Packed`; a packed record's fields carry no element fact, only the record's own alignment at offset zero (§2a). |
| A2 | Function-type assignability ignored the fact: `needs_sector: ([* align 4096]u8) -> u32` was accepted where `([*]u8) -> u32` was expected, and then called with a misaligned span. Executed. | break | **Fixed**: `alignmentAssignable` recurses into function types, parameters contravariant and the result covariant; `isAssignable` consults it for function values. |
| A3 | A `?` or match join returned the first arm's type, so `flag ? { aligned } \| { plain }` was `[* align 4096]u8` and the same expression with the arms swapped was refused. Executed. | break | **Fixed**: `Join` takes the weakest fact (`weakestAlignment`). |
| A4 | A declared return fact was not checked against the body: `claim: (x: [*]u8): [* align 4096]u8 = x` compiled; the spec both admitted and forbade it. Executed. | break | **Fixed**: the body's type must satisfy the declared fact (`a declaration may not claim more than the borrow gives`), for functions and literals; §2a says one thing now. |
| A5 | Three type-substitution sites rebuilt `IndexExpression` without `Align`, so `g[T]: (x: [* align 4096]T)` saw `[*]u8` inside its instantiation. Executed. | divergence | **Fixed**: `Align` copied in `typechecker/mono.go`, `genericfn.go`, `codegen/mono.go`. Generic bodies are still checked at instantiation only — stated. |
| A6 | Derived `align 1` was "no fact" but a declared `[* align 1]u8` kept the 1 and refused a plain span. Executed. | divergence | **Fixed**: declared `align 1` normalizes to the plain type; stated. |
| A7 | An uninitialized `[* align N]u8` is the zero span with a fact and no borrow behind it. | unstated | **Stated**: vacuous at length zero. |
| A8 | An exported function's C signature drops the fact silently; `92-ffi.md` said nothing. | unstated | **Stated** in §2.5: an unverified precondition on the C caller. |
| A9 | No test exercised function values, joins, returns, templates, packed records, or `align 1`. | untested | **Fixed**: `compiler/e2e_feature_pass_test.go`, compiled and interpreted plus seven rejections. |
| A10 | No Lean statement about the fact. | unstated | **Fixed**: `Oak.AlignmentFact` — weakening, `align 1`, the subslice rules, the join, the packed offset. |
| A11 | `subslice` compares the element index, not the byte offset, to the alignment: conservative for elements wider than a byte. | unstated | **Stated** (§2a); `subslice_index` is the rule, `subslice_elements` the exact one. |
| A12 | STATUS's Direct I/O row still listed the static fact as open. | discipline | **Fixed.** |
| A13 | Neither realization checks the base at run time; a forged fact fails silently. | open | **Open**: a debug-build witness at the consumer (checklist §8, new). |

## `try`

| # | Finding | Severity | Disposition |
| --- | --- | --- | --- |
| T1 | `OAK-M0401` was emitted without a position: `diagnostic.NodeToRange` had no case for `TryExpression` (nor `VariantPattern`), and the test asserted substrings only. Executed. | break | **Fixed**: ranges for `TryExpression`, `VariantPattern`, `BindingPattern`, `ExpressionStatement`; the test asserts `line:col`. |
| T2 | A block with `defer` was re-sliced into the `Ok` arm with `DeferredFrom` lost, so the deferred statement would run on the `Ok` path alone (today masked by the checker's refusal of `Result`-valued deferred blocks). Executed. | divergence (latent break) | **Fixed**: refused with its own sentence; stated in §2d. |
| T3 | `x := try e` was admitted and unstated. | unstated | **Stated.** |
| T4 | The "binder no program spells" (`_try_err_1`) was spellable; the name leaked into the Lean extraction. | discipline | **Fixed**: `oak_try_err_N` / `oak_try_ok_N`, the `oak_` convention of every lowering; the arm reads only its own binder, stated; the extraction golden regenerated. |
| T5 | One mistake produced two `OAK-M0401`s (the specific refusal and the leftover sweep). Executed. | divergence | **Fixed**: refused tries are recorded and the sweep skips them; the test counts one. |
| T6 | `try` in a function literal with its own `Result` return was refused as "does not return from the function". Executed. | unstated (open in STATUS) | **Fixed**: literals with a declared `Result`/`Option` return lower their own bodies; binders keep counting within the enclosing declaration. |
| T7 | Option-in-Result errors were unlocated and spoke in generated arms. | divergence | **Partly fixed**: the `VariantPattern` range locates them; the wording stays the checker's. |
| T8 | `Result[(), E]` with `_ = try e` cannot be written for want of a unit literal. | n.a. (20-types) | **Open.** |
| T9 | §2d's "a block that is the tail expression" read wider than the language (a bare nested block is a statement). | text | **Fixed.** |
| T10 | Every admitted position agreed in both realizations, including short-circuit after the first `Err`. | verified | — |
| T11 | Methods have no interpreter witness (an interpreter method-dispatch gap, with or without `try`). | untested | **Open**, recorded in STATUS. |
| T12 | A nominal alias of `Result` is not read; the help text did not say so. | discipline | **Fixed**: the message says the return type is read as spelled. |
| T13 | `compiler/inline.go` lists `TryExpression` as non-inlinable although lowering precedes inlining. | discipline | Left; harmless, phase order now stated in `95-extraction.md` §2 for the extraction and in `compiler/compilation.go`. |
| T14 | `15-diagnostics.md` had no `OAK-M0401` entry and `M` is the modules category. | discipline | **Stated**: `M0301`/`M0401` are lowering-shape codes kept under `M` for stability. |
| T15 | `95-extraction.md` never said extraction reads the lowered program. | unstated | **Stated.** |

## Found while testing

Writing the literal witness (T6) failed the borrow checker with `span()
argument must be &owner of an owned array` although the program had no
`span`. The message named neither the argument nor a position; once it did
(`stdlib.oak:7618:23: span() argument (&run)`), the cause was one line: the
borrow checker registered owners from a flat name lookup in the type
environment, so a user's top-level function `run` answered for a library
local `run` and the local's owned array was never tracked. Any program
importing `std` that declared a top-level name equal to a library local
that is borrowed failed this way. **Fixed**: owners are registered from
the declaration's recorded type (`CheckedDeclarationType`), the name lookup
is the fallback; the `span()`/`view()` messages name the operand and the
position. Two checklist items came from it (§4 "keyed by declaration",
§10 "a borrow message names the operand").

## Disposition summary

**yes** for §3 sum types, exhaustive matching, no non-local exit, views vs
spans, sizes in types; §5 results used or discarded on purpose, no side
effects in operands; §11 deterministic output. **no, now fixed** for §3
validated state constructible only through the validator (A1–A4), no
implicit conversions (A2–A4); §10 errors carry location (T1, T7), cascades
suppressed (T5); §11 generated code hygienic (T4), inference predictable
(A3, A5, A6), spec reconciled (A4, T3, T6, T9), foundational laws first
(A10). **open** for §4 debug witness (A13), §8 methods in the interpreter
(T11), §5 dead code (T13).

## What the target taught the lists

Written back into `docs/checklists/correctness.md`: facts flow through
every join and every arrow, and the neutral element has one spelling (§3);
a layout-derived fact reads the whole layout clause, and scoped facts are
keyed by declaration (§4); admitted positions are tested inside every
function form, and a fact that elides a run-time check has a debug witness
(§8); every reportable node has a range, one refusal one diagnostic, and a
borrow message names the operand (§10); a structural equality that omits a
fact is a hazard, a declared fact on a template signature survives
substitution or is rejected, and block facts travel with the slice (§11).

## Revisit criteria

- A13: when the I/O port gains a debug profile, assert the base at
  `io_open_region_aligned` in that profile.
- T8: a unit literal `()` in `20-types.md` makes `Result[(), E]` writable.
- T11: an interpreter method-dispatch increment gives methods their witness.
- A5's second half: generic bodies checked once (`correctness.md` §11) is a
  checker-wide item, not this feature's.
