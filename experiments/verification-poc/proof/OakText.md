# The Oak decoder, transliterated

`OakText.lean` is the first increment of roadmap step 2, *prove the Oak checker
implements the file model*. Until now the Oak decoder `rup_text_check`
(`self_hosted_text.oak`) and the proved file model `CertificateFile.check` were
related only by the corpus gate: compiled Oak and the model return the same
decision on every case. That is evidence about the cases, not a statement about
the program.

The module restates the Oak decoder in Lean structure for structure: its two
stage machines (DIMACS, then LRAT) over the proved scanner `scan`, every Oak
local a field of `Cnf` or `Proof`, every stage test a branch, every assignment
an assignment in the order the Oak source writes them. Bounded arrays become
lists whose length is the Oak counter, so the bounds `literals < 4096`,
`clauses < expected`, `count < 256`, `references < 4096` read the same. The
scanner is `scan`, whose agreement with `rup_token` the Go/Oak/Lean scanner gate
compares token by token; the stream checker is `CertifiedStream.check`, whose
agreement with `rup_stream_check` the stream gate compares layout by layout.
`layout` is `rup_text_check` up to its final call: the layout the Oak decoder
hands to `rup_stream_check` when both phases accept.

`check_sound` proves what the module establishes on its own: an acceptance
refutes the initial clauses of the layout it built, through the certified
stream's soundness. Axioms: `propext`, `Classical.choice`, `Quot.sound`.

`OakTextCompare.lean` replays the Oak text corpora and the boundary-profile
cases and requires three identical verdicts on every case: the transliteration,
the proved file model, and compiled Oak (whose verdicts the Go harness recorded).
The solver gate replays the actual Oak text certificate the same way. 743 cases
agree locally; CI repeats the comparison on every run.

What remains for step 2, stated rather than implied:

- **Transliteration fidelity.** That `OakText.check` is `rup_text_check` is a
  reading of the two sources side by side plus the corpus agreement; a checked
  translation of Oak's semantics is the general form (roadmap step 3).
- **The refinement theorem.** `OakText.check cnf proof = true →
  CertificateFile.check cnf proof = true`, relating the stage machine to the
  model's `preamble`/`header`/`clauses`/`proofLines` decomposition token by
  token. With it, `check_sound` of the file model transfers to the Oak decoder:
  every acceptance by the Oak checker refutes the formula the input format
  defines. This is the next increment.
