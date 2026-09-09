# The complete certificate-file state machine

`CertificateFile.lean` reads whole DIMACS and LRAT texts byte by byte with the
proved scanner and mirrors the Oak decoder's control flow: the entry guards
(at most 65,536 bytes, all ASCII), blank and comment lines, the `p cnf` header
with its variable domain (1 to 64) and clause-count domain (at most 256),
clause segments that may span lines, and proof lines made of an identifier,
an optional `d` marker, and zero-terminated segments. Deletion terminators
must be spelled exactly `0`; a newline or end of input inside a segment
rejects; any word after a command's final terminator rejects; at most 256
commands are stored.

The module adds a position-based segment reader over the shared byte list
with completion, well-formedness, and variable-domain theorems, and a
position-based publication step with the same layout theorems as the
single-segment adapter. The single-word identifier rule proved in the command
assembly milestone is shown to be this token rule plus end of input.

Each proof line preserves the command-assembly invariant `Represents` and
appends exactly one instruction, so the whole proof phase yields an assembly
representing the published initial clauses and some instruction list. The
DIMACS phase maintains a partial invariant between clause terminators (the
published ranges describe exactly the closed clauses, and every pool item is
inside the declared domain); the final check that no literal is pending and
that the number of clauses equals the declared count turns it into a valid
publication state. `check` composes the two phases with the certified stream.

`check_sound` states that acceptance implies unsatisfiability of the initial
clauses returned by the executable DIMACS phase, whose count equals the
declared count. It composes the `represented_sound` lemma added to
`CommandAssembly.lean`, which lands on `CertifiedStream.check` directly rather
than on the range decoder: the certified stream's live table starts from
exactly the published clauses. `assemble_certified_sound` restates the
command-assembly result on the same checker.

`CertificateFileCompare.lean` replays the existing Oak text corpora through
`check` and requires the same decision as Go and compiled Oak on every case.
The Go harness now also exports the boundary-profile cases; the solver gate
additionally replays the actual Oak text certificate through the file model.
Native Oak is unchanged.

## Boundary

The proved connection runs from the executable Lean model of the whole file
decoder to the certified stream checker. The model's DIMACS phase, like the
Oak decoder, is the definition of the accepted grammar in this profile;
external DIMACS/LRAT grammar conformance and Go's broader profile are outside
the theorem. Universal refinement of the compiled Oak decoder against this
model, and compiler and C runtime correctness, remain open. Rejected inputs
return no state; partial native mutations on failure are outside these
theorems. Fuel adequacy is not proved: the model rejects if it runs out of
fuel, and agreement with Oak on the corpora covers the inputs exercised.

## Validation

Local runs on the tested commit: 19 theorem and definition reports passed with
warnings treated as errors, without proof holes or project-specific axioms.
Dependencies are limited to standard `propext`, `Quot.sound`, and
`Classical.choice`. The file model agreed with Go and compiled Oak on all 743
text cases: 729 corpus cases (comments, whitespace classes, line endings,
every byte value as a token and as a separator, malformed headers and
terminators, deletion spellings) and 14 boundary cases (variable, clause,
command, pool, and byte limits). The comparison took under four seconds.

CI results are recorded in `../validation-certificate-file.json` once the
opt-in workflow has run on the pushed commit.

Next: relate the compiled Oak decoder's states to this model for every input,
starting with a precise semantics for the Oak fragment it uses, so that Oak
acceptance implies model acceptance.
