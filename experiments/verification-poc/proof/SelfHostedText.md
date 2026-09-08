# Bounded ASCII certificate checking in Oak

`self_hosted_text.oak` adds byte-level DIMACS and ASCII LRAT decoding to the Oak
RUP kernel and complete decoded stream checker. `rup_text_check(cnf: []u8,
proof: []u8): Bool` accepts only when both complete inputs parse and the decoded
stream establishes a refutation. All three Oak files remain in the removable
verification experiment. The host harness is Go.

## Input and resource contract

Both inputs are read-only byte views. Each is limited to 65,536 bytes and ASCII
bytes 0 through 127. Non-ASCII bytes reject even inside comments. An ASCII byte
such as NUL is not whitespace and rejects in a numeric token; comment contents
are ignored after the standalone first token `c`.

The decoded profile is unchanged: 1–64 variables, at most 256 initial clauses,
addition IDs at most 256, at most 256 commands, 4,096 literal-pool entries, 4,096
reference-pool entries, and at most 256 hints per addition. Repeated literals
consume pool space even though the RUP checker gives them set semantics. Integer
magnitudes are limited to 2,147,483,647. Deletion stamps may exceed the bounded
addition-ID capacity, as in the decoded stream checker.

The scanner uses bounded local storage. It checks each decimal digit and the
next multiply/add against the magnitude limit before performing arithmetic.
Decoding checks capacity before writing a literal, reference, clause range, or
command. The complete inputs are decoded before invoking the stream checker.
No heap allocation, compiler changes, Python runtime, or production-language
integration is introduced.

The [statement-match compiler correction](MatchLowering.md) fixes the nested
Boolean guard re-evaluation and multiple-arm selection discovered during this
work. The decoder now uses ordinary state-dependent guards without snapshot
workarounds. The original validation record below remains historical;
`../validation-match-lowering.json` records the corrected compiler and parser.

## Text rules

- Space, tab, carriage return, vertical tab, and form feed separate fields.
  Newline ends a line. A final line need not end with a newline.
- Blank lines and lines whose first field is exactly `c` are ignored. Inline
  comments and prefixes such as `comment` do not count as comments.
- DIMACS requires exactly one four-field `p cnf VARIABLES CLAUSES` header on one
  line before clause data. Clauses may span lines; multiple clauses may share a
  line. Clause counts must match and every clause must terminate with zero.
- Decimal integers allow an optional sign and leading zeros. Signed zero is
  accepted where a numeric zero is permitted. Counts and identifiers must be
  nonnegative; literals must be within the declared variable domain.
- Each LRAT addition occupies one line: ID, clause literals, zero, positive
  hints, zero. A deletion occupies one line: stamp, `d`, positive IDs, literal
  token `0`. A deletion's final token cannot be `+0`, `-0`, or `00`, matching the
  existing Go and Lean parsers.
- Missing terminators, extra tokens, negative/RAT hints, overflow, malformed
  numbers, undeclared literals, and invalid suffixes reject. The checker never
  accepts merely because an earlier prefix established an empty clause.

## Validation

From the experiment directory:

```sh
go test -count=1 -v . -run '^TestSelfHostedText$|^TestSelfHostedTextProfile$'
```

The Go harness compiles the actual Oak sources through the existing frontend,
compiles the emitted C, and runs native assertions. Compilation errors, missing
tooling, unsupported C markers, allocation calls, crashes, and timeouts fail the
test; none count as a successful negative case.

The text corpus serializes the 425 decoded stream cases and adds 48 targeted
parser cases and 256 byte-class cases: every ASCII byte appears inside a numeric
field and between tokens. Expected decisions come from Go's ASCII LRAT checker.
CI saves all 729 cases and runs the existing `RUPTextCompare.lean` adapter over
the same inputs with Lean's `checkText` implementation.

[The three-way text comparison passed](https://github.com/SCKelemen/oak/actions/runs/34198926460):
119 accepted and 610 rejected decisions agree across all 729 inputs. All 14
profile-boundary cases also passed. `../validation-self-hosted-text.json` records
the tested code commit, CI evidence, and remaining trust boundaries.

Fourteen separate profile cases cover variable, initial-clause, literal-pool,
reference-pool, command, addition-ID, byte-length, and non-ASCII limits. Positive
boundary cases exercise variable 64, 256 initial clauses, 256 commands, and
exactly 4,096 literal entries. These cases are not presented as acceptance
parity with the larger Go/Lean resource profiles.

The opt-in certificate gate takes the first actual accepted CaDiCaL certificate
from the suite report and requires the compiled Oak text checker to accept it.
It also requires rejection with an invalid proof suffix and a satisfiable wrong
formula. Go checks the positive input, and Lean checks all three saved text
cases. Failure to supply a fitting real certificate fails the gate; it does not
silently skip or substitute a synthetic proof.

The recorded solver run passed this replay: one accepted certificate and two
rejected corruptions, with all three decisions also agreeing with Lean. The
existing 11-certificate/22-corruption Lean gate and the repository's CI,
standard-library, formal-verification, and golden-file workflows passed too.

## Remaining proof boundary

The text parser and proof-stream algorithms now execute in Oak. Corpus agreement
and real certificate replay do not prove that all Oak executions refine the
Lean reference. Lean's `checkText_sound` proves unsatisfiability of the database
returned by its own DIMACS parser on acceptance; it does not prove the Oak parser
or its correspondence with an external file-format specification.

The Oak compiler, generated C, C compiler/runtime, and Go test harness remain
trusted. Solver integration, source-to-CNF reconstruction, and evidence receipts
remain hosted outside Oak. The existing solver gates continue using Go and Lean
alongside this bounded Oak replay. RAT, binary LRAT, extension variables, and
theory lemmas remain unsupported.

The [bounded decimal milestone](BoundedDecimal.md) now proves model-level
decimal refinement and local buffer invariants. Correspondence between compiled
Oak and that model remains tested rather than universally proved. The
[scanner-state milestone](ScannerState.md) adds partial-decimal trace refinement
and token cursor/range invariants, with complete state-sequence comparisons.
Connecting scanner tokens to clause and hint buffer transitions is next.
