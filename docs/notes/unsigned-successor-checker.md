# Guarded unsigned successor in the implication checker

The generic implication checker recognizes the fixed-width law
`k < bound → k + 1 ≤ bound`. The strict unsigned guard excludes modular wrap.
`Oak.UnsignedSuccessor` proves no-wrap, the actual BitVec addition, and premise
composition. `CheckUnsignedSuccessor.lean` pins all ten theorem statements and
rejects dependencies outside the existing standard axiom allowlist.

The Go rule accepts widths 1 through 64, a parameter counter, same-width addition
of exactly one, an ordinary unsigned `lo` guard, and an ordinary unsigned `ls`
goal equated to the one-bit constant true. Counter and bound must be reused by
pointer identity. A one-bit AND walk establishes that the premise entails the
strict guard; it is limited to 128 distinct walked nodes and rejects repetitions.
Signed comparisons, OR descent, altered widths or bounds, separately allocated
name-equal terms, non-unit increments, false polarity and unsupported shapes
fall through to the ordinary decider.

The hook is after ordinary implication-call admission, bounded DAG counting,
node debit and remaining-budget rejection, before canonicalization and before
unchanged memo publication. It allocates no proof entitlement and changes no
search or proof limit. It returns an implication decision through the existing
checker; it does not construct a top-level Verdict or bypass value, effect,
trap-domain or callee-closure obligations. Verdict composition remains separate.

The matcher assumes the surrounding immutable, well-formed internal term DAG.
It validates the recognized parameter/constant/add/comparison/AND spine, not
every possible malformed serialized bound. The Lean proofs do not machine-check
the Go matcher, its representation, or their refinement. That boundary remains
explicit source review and portable positive, negative, exhaustive-small-width,
word-boundary, admission and memo-publication tests.

The three portable `TestUnsignedSuccessor` roots include 32 named negative
mutations and do not require an external capture, local artifact path or solver.
The historical retained-query replay and paired first-Validate observations are
separate diagnostic evidence. Resolving this invariant obligation does not
establish complete loop verification, a completed native build or a stable
performance improvement.
