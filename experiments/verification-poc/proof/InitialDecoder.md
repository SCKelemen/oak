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

## Validation

[The soundness gate passed](https://github.com/SCKelemen/oak/actions/runs/34241678960/job/102113157882)
on commit `f63fbfb0ce4bc3ea817d17e4042d6520baae6c96`. All five theorem reports
and the executable-definition report passed with warnings as errors, without
proof holes or project-specific axioms. Dependencies are limited to standard
`propext`, `Quot.sound`, and `Classical.choice`.

The decoder composition, certified stream, original Lean checker, Go oracle,
and compiled Oak agreed on 887 layouts: 308 accepted and 579 rejected. Native
comparison took 44.06 seconds without the race detector.

[The solver gate passed](https://github.com/SCKelemen/oak/actions/runs/34241678960/job/102113157970).
Nine actual certificates fit the profile and were accepted across all replay
paths; their 18 corruptions were rejected. Two certificates were explicitly
outside the bounded profile. All 11 original certificates and their 22 corruptions
still passed the existing Lean text gate. Native replay of the 27 new layouts
took 2.08 seconds. The 887-layout suite also passed with the race detector in
86.91 seconds. Existing Boolean proof and model-certificate gates passed.

Repository CI, standard-library tests with the race detector, formal verification,
golden files, and AArch64 memory refinement all passed on the tested commit.
`../validation-initial-decoder.json` records the exact proof and testing scope.

The subsequent [packing milestone](ProofPacking.md) proves roundtrip for all
supported decoded inputs and adds a sound text-entry composition. Universal
Oak text-decoder and compiler refinement remain open.
