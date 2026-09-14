# Note: symbolic protocol provers and high-performance proof checking

**Status: extraction done; the first increment of the certificate rung
landed the same day (`125-verification.md` §3 "By certificate", §4
`-solver sat`).**
2026-09-13, `specification` branch. Sources read once, on Samuel's ask to
"check the Tamarin and ProVerif proofs, ParaFROST and cuda-cic, connect to
crypto proofs, and want a very high-performance proof verification
system": the Tamarin manual and publications page, the ProVerif manual
(2.05) and Blanchet's FOSAD 2014 tutorial, the ParaFROST repository and
its TACAS 2021 / FMSD 2023 papers, the `cuda-cic` repository, Lean's
`bv_decide` documentation, and the LRAT literature. Extracted into
`docs/checklists/correctness.md` §2 (twelve items) and
`docs/checklists/performance.md` §13 (eleven items, new section). What
each system is, what maps onto Oak, and what would have to exist first.
Facts are cited; assessments are marked.

## The four systems

**Tamarin.** A symbolic verifier for security protocols with an unbounded
number of sessions. Protocol and adversary are labeled multiset rewriting
rules over a state that is a multiset of facts; `Fr(~n)` produces fresh
names, `In`/`Out` are the untrusted network, `K(m)` adversary knowledge;
facts are consumed unless persistent (`!F`). Messages are terms modulo a
declared equational theory (built-ins for hashing, symmetric and
asymmetric encryption, signing, Diffie–Hellman, bilinear pairing, XOR,
multisets, naturals; user theories must be convergent with the finite
variant property, in practice subterm-convergent). Properties are trace
lemmas in a guarded first-order fragment over action facts and timepoints
(`Fact(x) @ #i`, `#i < #j`), `all-traces` or `exists-trace`; the standard
templates are secrecy tolerating a named `Reveal` and Lowe's injective
agreement over `Running`/`Commit`. Restrictions filter traces; sources
lemmas, proved by induction, close the partial deconstructions that make
search loop; `reuse`, `use_induction`, oracles and a tactics language steer
a search that is undecidable in general. Observational equivalence is
approximated through `diff(l, r)`. Case studies on its publications page:
TLS 1.3, 5G AKA, Noise, WPA2, EMV. (tamarin-prover.com/manual; Meier,
Schmidt, Cremers, Basin, CAV 2013.)

**ProVerif.** Applied pi calculus with types, translated to Horn clauses
over `attacker(M)`, `mess(N, M)`, `event(...)`, decided by resolution with
free selection. The adversary is the Dolev–Yao clause set; fresh names
become function symbols of the session's inputs. The abstraction is sound
but forgets how many times an action ran, so it yields false attacks,
notably for temporary secrets. Queries: secrecy, correspondences and
injective correspondences (authentication), strong secrecy, offline
guessing, observational equivalence through biprocesses. Three verdicts:
true; false with a trace that is always a real attack; and "cannot be
proved" with a derivation that may be a false attack. Non-termination on
associative theories (XOR, groups) and in saturation; the knobs are
`select`/`nounif`, secrecy assumptions, lemmas, axioms, induction.
CryptoVerif is the computational-model sibling. (Blanchet, FOSAD 2014;
manual 2.05 §3.3, §4.3, §6.)

**ParaFROST.** A CDCL SAT solver whose *inprocessing* runs on the GPU:
bounded variable elimination in three phases, subsumption, eager
redundancy elimination, functional-dependency extraction, a data-parallel
garbage collector, and proof generation for the device-side
simplifications; the CDCL search stays on the CPU with CaDiCaL-derived
heuristics. Per round the formula is copied to the device, simplified,
and the proof stream and units copied back. Certificates are binary DRAT
checked by `drat-trim`; deleted lemmas are omitted to spare device memory,
so its proofs check slower than CaDiCaL's. Benchmarks: 641 formulas over
five megabytes from the 2013–2021 competitions; component speedups of
1.5× (elimination) to 35× (collection) on average, with the solver ahead
of CaDiCaL on that suite and behind Kissat. (Osama, Wijs, Biere, TACAS
2021 and FMSD 2023; github.com/muhos/ParaFROST.)

**cuda-cic.** `github.com/salihcankurnaz/cuda-cic`: "Experimental CUDA
batch evaluation/type-checking for a selected Lean/CIC fragment" — a
single-author repository created in March 2026 with flat seven-integer
term nodes and CUDA kernels for bounded weak-head normalization,
substitution, definitional equality, and universe levels over batches of
terms, with a Lean 4 export bridge. Its own README says it is not a
replacement for Lean's kernel and has no proof of equivalence to it;
inductives are limited; its September 2026 audit withdraws earlier
correctness and speedup claims and records that the Lean path checks
theorem *types*, not proof terms. No paper, no independent evaluation.
**Assessment:** a real but preliminary experiment; an existence proof of
"batch-evaluate many small terms on a GPU", nothing to build on.

## What maps onto a protocol declaration

| Oak (`112-protocols.md` §1, §4) | Tamarin | ProVerif | Status |
| --- | --- | --- | --- |
| `initial S`, states | one linear fact `St(state, data…)`; the state a public constant | control points of one process, or a table | maps; Tamarin's linear facts are exactly a consumed and re-produced state; ProVerif's abstraction forgets repetitions, the textbook false-attack case for counters |
| a line `name(p): From -> To when g then { e }` | one rule per line with `In(p)`, `_restrict(g)`, action `Step_name(p)` | one `in`/`if`/`out` branch | maps; Tamarin explores every enabled line, TLC's reading, so the §1 exclusivity rows say when the projection differs |
| scalar, refined, record payloads | `In(p)` with a restriction for the refinement | typed `in(c, p: t)` | maps for Bool and naturals; not for fixed width |
| `data` and effects | fact arguments, primed values | process variables, tables | maps |
| fixed-width arithmetic, `%`, `/`, index bounds | `natural-numbers` has `+` and order on unbounded naturals | `nat` with `+`, `<` | **absent there**: an export abstracts widths to naturals and must state that as a reading difference |
| quantifier forms over `[N]Bool` | unrolled, N fixed | unrolled | maps by unrolling |
| `fair`, `eventually` | none | none | out of scope: both are trace-safety tools; only an `exists-trace` sanity lemma is expressible |
| invariant theorems over `(state, data)` | `all-traces` lemma over the `St` fact | `query event(State(s, d)) ==> pred` | maps within the guard subset |

What is missing, as expressiveness findings (`performance.md` §0
letters; each is class (a), the declaration lacks the object, which is
itself a finding — the letters were written for machine-code deviations
and have no class for "the model lacks a semantic object"):

- message terms and function symbols with an equational theory (a);
- cryptographic primitives, whose theory class the export would have to
  check (a);
- fresh names (a) — `init` constants and enumerated payload domains are
  not unguessable values;
- the adversary and the channels: a declaration is a closed machine whose
  environment beyond fairness is "the TLA+ extension module's" (§6) (a);
- roles and unbounded sessions: one declaration is one machine, and
  `replicas: [2]Replica` is a bounded instance (a for unbounded; bounded
  roles are a partial map);
- events with timepoints: the monitor (§2c) sees the trace but no theorem
  form ranges over it (a);
- the reverse gap: exact fixed-width arithmetic, decided here (`paid__step`
  refutes at `coins: 255`), has no exact counterpart there.

**Assessment.** The smallest useful export is a state-machine sanity
export — every line a rule, `exists-trace` per state, invariants as
`all-traces` lemmas — a third reading of the declaration to compare with
TLC and `oak prove` (the "every reading compared pairwise" item of
`correctness.md` §2 then applies). A security reading needs a term
language, `fresh`, channels, and an adversary in the declaration; the
constitution's one-declaration rule argues for adding them to the
declaration rather than to a side file, which is a language design
decision recorded in `112-protocols.md` §7, not something the current
subset bends to. Until then the useful import is the method — the twelve
§2 items — not tooling.

## A high-performance verification path for `oak prove`

**Where Oak stands** (`125-verification.md` §3, §4, §7; `prove/`,
`asm/blast.go`): enumeration up to 65,536 cases, then a bit-level ROBDD
with complement edges under a two-million-node budget, three variable
orders raced, a witness pass before any diagram, a Go replay that must
match verdict and node count, Lean's `bv_decide` for the rest; budget
exhaustion is a labeled evidence verdict, never a false proof; proof
certificates are a stated direction.

**What the field says** (documented): Lean's `bv_decide` is the
architecture §7 describes — verified bit-blasting to an AIG, CaDiCaL to an
LRAT proof, an LRAT checker with a soundness proof in Lean, the result
admitted through `ofReduceBool`, which adds the Lean compiler to the
trusted base. DRAT is cheap to emit and about as expensive to check as to
solve; LRAT carries hints so checking is linear, and verified checkers
exist (ACL2 `lrat-check`, `cake_lpr` verified to machine code; CaDiCaL
emits LRAT natively so checking beats solving — Pollitt, Fleury, Biere,
SAT 2023). GPU SAT has not moved the CDCL search itself; ParaFROST moves
inprocessing and proof generation, wins on large redundant formulas, and
trails Kissat. Lean's kernel is C++; Lean4Lean re-implements it in Lean at
a 20–50% cost and found one soundness bug. No GPU CIC kernel exists in the
literature; cuda-cic does not check proof terms.

**Assessment**, recorded as `125-verification.md` §7 "A certificate rung"
(items 1 and the checkers of item 2 landed on 2026-09-13: `asm/cnf.go`,
`prove/lrat.go`, `prove/solver/lrat.oak`, `Oak.RupCheck`; the solver
written in Oak landed the same day as the rung's default,
`prove/solver/sat.oak`, then clause-database reduction with deletion lines,
two watched literals, learned-clause minimization, Luby restarts,
activity-based reduction, and bounded variable elimination at load; the
encoder's laws are stated in `Oak.Tseitin` and its code checked against
them by truth table; the clause engine written in Oak (`cnf.oak`) now
sits beside the Go one and is the rung's default, the two agreeing clause
for clause in count over the corpus; and the rung runs inside the prover
written in Oak too (`certify.oak`), the solver recording its steps as
words for the checker in the same process, so `-solver self` goes from
the law file to a checked certificate with no Go on the path — the Go
engine, the Go checker, and the Go ladder are the twins that must agree;
and the solver's own laws are stated in `Oak.SolverLaws`, over the relation
`Oak.RupCheck` decides — the resolvent step as a two-hint chain implied by
its parents, the replayed reasons in trail order then the conflict as a
chain from the learned clause's negation, the mark discipline of
`sat_analyze` over a propagation trail giving that condition, and
`sat_extend`'s reconstruction modeling the eliminated clauses whenever the
resolvents hold. `Oak.RupCheck` is why an accepted record refutes the
formula; `Oak.SolverLaws` is why the solver's record is accepted, a
completeness statement about the recording, with the code itself still
checked by fixtures and the corpus rather than proved. On the corpus the solver agrees with the ladder
on every bit-level row of `machines`, `shapes`, `lattice`, and `effects`,
and on twenty-two of `extents`' twenty-four, the whole corpus in about a
minute. Elimination was the decisive step, as the ParaFROST and CaDiCaL
reading predicted: the arithmetic obligations whose learned clauses
spanned every decision level become unit-heavy once the Tseitin gate
variables are resolved away. The two rows still open are the widest
(178k and 244k BDD nodes); subsumption and failed-literal probing are the
next techniques, still ahead of any GPU question. First run with CaDiCaL 3.0.1:
`spec/oak/machines.oak`'s `bounded__step` — 14,987 BDD nodes under the
blocked order — closes with a 204-step certificate checked in Go and in
Oak; `spec/oak/shapes.oak`'s nine rows all agree):

1. Add a SAT rung with LRAT rather than a bigger BDD budget; keep the BDD
   for canonical equivalence and counterexamples.
2. The trusted base then narrows to the clause encoder, which is
   cross-checked against Go node for node and not proved — the finding to
   close first (`performance.md` §13 "Trusted base of the checker stated").
3. The GPU is not ParaFROST-shaped for Oak: obligations are kilobytes.
   The parallel axis is the many small independent evaluations — the
   witness pass, exhaustive enumeration, reachable-state exploration — a
   kernel of `56-kernels.md`, to be measured before built.
4. cuda-cic: cite, if at all, as a negative example of throughput before
   correspondence, in its own audit's words.

## Sources

Tamarin: manual chapters 1, 4, 5, 7, 9, 11, 14 at tamarin-prover.com;
publications page; Meier, Schmidt, Cremers, Basin, CAV 2013; Basin et al.,
5G authentication (arXiv 1806.10360); Cremers et al., TLS 1.3, CCS 2017.
ProVerif: manual 2.05; Blanchet, FOSAD 2014; Blanchet, FnTPS 2016.
ParaFROST: github.com/muhos/ParaFROST; Osama, Wijs, Biere, TACAS 2021 and
FMSD 2023. cuda-cic: github.com/salihcankurnaz/cuda-cic (README, project
status, the 2026-09-04 audit, the 2026-08-19 evidence directory).
Certificates and kernels: Lean `BVDecide` documentation; LeanSAT;
Lean4Lean (Carneiro, arXiv 2403.14064); LRAT (Cruz-Filipe, Heule, Hunt,
Kaufmann, Schneider-Kamp, CADE 2017); `cake_lpr` (Tan, Heule, Myreen, TACAS
2021); Pollitt, Fleury, Biere, SAT 2023; FRAT (Baek, Carneiro, Heule, LMCS);
`drat-trim`; LRAT-Catcher (arXiv 2607.00815); Schreiber, SAT 2024.
