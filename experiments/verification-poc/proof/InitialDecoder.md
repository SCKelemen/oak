# Initial decoder and real certificate replay

`InitialDecoder.lean` removes the caller-supplied per-index equation from the
certified stream's decoded soundness theorem. Successful `decodeLayout` execution
implies that the initial range traversal returned the decoded clause list.
`mapM_lookup` proves the corresponding lookup equation at every index, including
indices beyond the list. The existing live-table initialization theorem then
identifies `CertifiedStream.origin raw` with `initialDatabase d.clauses`.

`InitialDecoder.check` composes the actual range decoder with the certified stream.
Its `check_sound` theorem states that acceptance supplies a successfully decoded
layout whose initial clause database is unsatisfiable. It never invokes the
original `checkProof` to establish soundness. Five theorem reports and one
executable-definition report audit this connection with warnings treated as errors.

The existing 887-layout comparison now also exercises this composition.
`CertificateReplay.lean` reads every real certificate recorded by the external
suite and packs parsed literals, IDs, stamps, and hints into the bounded layout.
Every supported input must round-trip to the same parsed clauses and commands.
It must be accepted by the certified stream, decoder composition, and original
Lean range checker. The emitted layouts are then replayed by the independent Go
oracle and uninstrumented compiled Oak in `TestSelfHostedCertifiedCertificates`.

For each supported certificate, replacing its formula with a satisfiable unit
must reject. Appending an empty addition with reused ID 1 must also reject; the
suffix must still decode within the profile, so this specifically checks that
command validation continues after refutation. All cases are mandatory triples.
An empty manifest, zero supported certificates, parser error, crash, or mismatch
fails the gate. Reports and the full canonical layouts are retained in the unique
`build/lean-gate/attempt-*` directory, alongside the existing source hashes.

Certificates outside the fixed profile (64 variables, 256 initial clauses,
commands and addition IDs, 4096 literal/reference slots) are explicitly recorded
with their complete layouts. They remain subject to the existing unbounded Lean
text gate; an exclusion is not certified-stream acceptance. The top-level report
is marked successful only after native replay succeeds.

## Boundary

The new theorem proves the connection from executable range decoding to the
certified stream's initial database. It does not prove the external DIMACS/LRAT
grammar, the test-only packing adapter, JSON transport, or universal equivalence
with Oak. Packing correspondence is checked per supported certificate. Oak,
Go, and the old Lean checker remain differential evidence; the Oak compiler,
generated C, and C runtime remain trusted test infrastructure.

This remains entirely within the removable verification experiment. The harness
is Go; no Python or production language changes are introduced.
