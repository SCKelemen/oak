# Command assembly from published ranges

`CommandAssembly.lean` models the decoder's proof phase on top of the proved
segment publication state. Each proof line contributes one command: an
identifier word, then either a clause segment and a hint segment, or a
deletion segment. Additions publish the clause into the literal pool and the
hints into the reference pool. Deletions publish only references and record
the current literal offset with an empty clause range, exactly as the Oak
decoder does. The identifier rule reuses the proved executable scanner: one
numeric token with a valid sign that is nonnegative or a spelling of zero.

The `Represents` invariant relates an assembly to a list of clauses and a list
of decoded instructions. It states that the literal pool is the packer's
concatenation of encoded initial clauses and addition clauses, that the closed
reference segments are exactly the hint and deletion lists, that the initial
ranges are `ProofPacking.segments`, and that the command list is the decoder's
metadata for those instructions. Starting the proof phase from any valid
literal publication state establishes the invariant for the decoded initial
clauses. Every successful addition and deletion preserves it while appending
one instruction whose ID or stamp is the scanned identifier, and a sequence
theorem covers whole proof texts.

The range decoder ignores a deletion's clause range, so the assembled command
list and the proved packer's command list decode identically. From this, the
assembled layout decodes to exactly the published clauses and instructions
under the packer's support conditions, and its certified acceptance refutes
those clauses. The headline theorem needs no support hypothesis at all:
`assemble_sound` states that if the executable decoder-plus-certified-stream
checker accepts the assembled layout, the initial clauses published by the
literal state have no satisfying assignment.

`CommandAssemblyCompare.lean` replays a corpus of proof texts with explicit
identifier words through the proved assembly and compares the flat layout with
the Go oracle and compiled Oak observations. The Go harness gained one test
and a shared decoder observer; the existing buffer corpus is unchanged.

## Boundary

The proved connection runs from the executable Lean model of the decoder's
segment and identifier handling to the packer's layout and the certified
stream checker. Splitting a proof line into its identifier word, the `d`
marker, and its segments is the byte adapter's job and is not modeled here.
Universal refinement of the compiled Oak decoder, the DIMACS header and
clause-count checks, and compiler correctness remain open. Rejected reads
return no assembly; partial native mutations on failure are outside these
theorems.

## Validation

[The soundness job passed](https://github.com/SCKelemen/oak/actions/runs/34289063128/job/102271267459)
on commit `ae5043e2b10d64d00aeed16259c5fef032b45e5ae`. All 18 theorem and
definition reports passed with warnings treated as errors, without proof holes
or project-specific axioms. Dependencies are limited to standard `propext`,
`Quot.sound`, and `Classical.choice`.

The assembly adapter, Go oracle, and compiled Oak agreed on all 95 cases:
45 decoded layouts and 50 rejected inputs. Native assembly comparison took
4.17 seconds without the race detector. The corpus covers signed, zero,
leading-zero, whitespace-adjacent, boundary, overflowing, and non-numeric
identifier spellings for both additions and deletions, repeated and descending
IDs, deletion offsets after additions, malformed segments after a valid
identifier, and the 256-command boundary. The existing 72-case buffer corpus
still agreed through both earlier adapters after the observer refactor.
Existing proved packing comparisons passed 425 cases, and certified streams
passed 887 layouts (308 accepted, 579 rejected).

[The solver job passed](https://github.com/SCKelemen/oak/actions/runs/34289063128/job/102271267739).
The assembly corpus also passed with the race detector in 6.73 seconds.
Existing real-certificate replay accepted nine bounded certificates and
rejected 18 corruptions, with two certificates explicitly outside the bounded
profile. All 11 source certificates and 22 corruptions passed the earlier Lean
text gate. Boolean proof/model checks and the full external solver suite
passed. These certificate gates retain the previously proved packing/text
entry path; they do not yet use a complete file parser assembled from
publication states.

Repository CI, standard-library race tests, Oak testing tools, formal
verification, and golden files all passed on the tested commit.
`../validation-command-assembly.json` records the exact scope and job links.

Next: model line splitting and the `d` marker in the byte adapter, then
connect the DIMACS header and clause-count checks so the whole file state
machine is covered.
