# Bounded decimal refinement and buffer invariants

`BoundedDecimal.lean` proves an executable model of the decimal core used by
`rup_token` equivalent to a mathematical decimal specification. It also proves
arithmetic and buffer-guard obligations needed by the bounded Oak decoder.
These proofs are a step toward refinement of the Oak implementation; they do
not yet establish a representation relation to compiled Oak executions.

## Decimal specification and theorems

The mathematical specification decodes ASCII decimal digits, evaluates the
entire number using unbounded natural arithmetic, and then checks that the
result is at most 2,147,483,647. It rejects an empty digit sequence and invalid
bytes. An optional leading `+` or `-` is permitted. The sign is retained
separately from magnitude, including the distinction between `0` and `-0` used
by Oak's scanner tags.

The executable model instead checks each digit before multiplying or adding,
using Oak's threshold of 214,748,364 and final-digit limit of 7. Its theorems are:

| Theorem | Guarantee |
| --- | --- |
| `step_refines` | The threshold guard accepts exactly the mathematical bounded digit steps. |
| `step_bounds` | An accepted step has a decimal digit and the expected result within the magnitude limit. |
| `step_no_wrap` | Both multiplication and addition fit in 32 bits; reduction modulo 2^32 preserves the result. |
| `run_refines` | Early overflow rejection agrees with an unbounded fold followed by a final bound check. |
| `decodeDigit_refines` | ASCII byte classification produces exactly the corresponding digit. |
| `parseUnsigned_refines` | Complete unsigned byte parsing agrees with the mathematical specification. |
| `parseSigned_refines` | The equivalence extends to optional signs and signed zero. |

`run_refines` uses a monotonicity lemma: extending a nonnegative decimal prefix
cannot reduce its mathematical value. Thus a prefix that overflows cannot be
rescued by any suffix, including zeros. The proof covers arbitrary-length digit
lists and arbitrary initial accumulators, rather than enumerating inputs.

The modular arithmetic theorem models the required unsigned 32-bit operation.
It is not a theorem about Oak's compiler or C arithmetic implementation.

## Buffer obligations

`rangeSafe_refines` proves that the subtraction-based guard
`start <= size && count <= size - start` agrees with the mathematical range
condition `start + count <= size`. `range_index` then proves each offset below
`count` is in bounds.

`append_bounds` proves that an append writes at a valid index and leaves the
new used count within capacity. `append_no_wrap` proves the count increment
cannot wrap when capacity is below 2^32. `cursor_progress` proves progress,
bounds preservation, and nonwrapping increments for a cursor below an input
size of at most 65,536 bytes.

`appendBuffer_invariant` models the initialized prefix of a bounded buffer. An
accepted append preserves capacity, keeps all prior elements in order, adds
exactly the requested element, and keeps the new length within capacity. The
logical prefix is represented as a Lean list; proving its correspondence with
Oak's fixed-size arrays remains a separate obligation. These are local buffer
invariants, not a proof of all control-flow paths in the complete parser.

## Executed correspondence checks

`self_hosted_decimal_test.go` calls the actual Oak `rup_token` implementation
through the normal frontend and compiled C. A result counts as a parsed integer
only when one numeric token consumes the whole byte view starting at offset
zero. Accepted magnitude and sign must match Go's `strconv.ParseInt` result
restricted to the supported magnitude range; negative zero is checked separately.
Crashes, compiler failures, timeouts, and unsupported code generation fail the
test rather than counting as parser rejection.

The deterministic corpus includes threshold neighborhoods for every final digit,
optional signs and leading zeros, signed zero, empty and malformed tokens, long
zero and overflow strings, all 256 byte values alone and embedded in a token,
and 400 seeded 32-bit inputs. JSON stores byte values as numbers so invalid UTF-8
cannot be normalized during transport. CI passes the same corpus to
`BoundedDecimalCompare.lean`, which checks the proved model's acceptance,
magnitude, and sign against every expected result.

CI checks the Lean file with warnings treated as errors and records the axiom
reports for the public refinement and safety theorems. Existing text, stream,
RUP, Boolean CNF, and actual solver-certificate checks continue to run.

[The proof and comparison gate passed](https://github.com/SCKelemen/oak/actions/runs/34205238981):
all 13 reported refinement/safety theorems were checked, and 1,338 inputs agreed
across Oak, Go, and Lean (431 accepted, 907 rejected). The axiom reports contain
only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; they are
retained with the canonical byte corpus and comparison logs. The tested commit
and remaining proof boundary are recorded in `../validation-bounded-decimal.json`.

Repository CI, standard-library, formal-verification, and golden-file checks
passed. The existing real-certificate gates also passed, including one accepted
Oak ASCII replay with two rejected corruptions and 11 accepted Lean certificate
checks with 22 rejected corruptions.

## Remaining proof boundary

The model-to-specification refinement is proved. The compiled Oak-to-model
relationship is tested on the corpus. No universal theorem connects the Oak
scanner, compiler output, or complete DIMACS/LRAT parser to this model yet.
The C compiler/runtime and Go harness also remain trusted execution components.

The next step is a scanner-state relation covering byte positions, token ranges,
partial accumulators, and rejection states. Composing that relation with these
arithmetic and buffer lemmas would support a proof of the complete decoder.
