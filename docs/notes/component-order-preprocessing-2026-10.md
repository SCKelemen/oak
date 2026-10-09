# Component-order preprocessing in native proofs

The native ARM64 run at `8932bbc9b8f21e340920db4301f0b43b1028cc89`
(run 37988724114, job 114017143856) reached the compiler package's unchanged
90-minute timeout while `TestE2ENativeLiteralsVerdicts` had been running for
27m57s. Its live stack was constructing a components-apart variable order,
inside the repeated union-find lookups for a Boolean connective's clique.
This work precedes BDD construction and is not bounded by the diagram budget.

## Change and equivalence boundary

- Compress union-find paths without changing their representatives. Do not use
  union by rank: changing the representative changes its sorted block name.
- Represent a Boolean connective's component clique as a hyperedge. Resolve
  each atom membership once and keep each incident component once per edge.
- Expand a hyperedge only when its first component is visited. Every member is
  then queued, so revisiting that edge cannot discover another component.
- Sort the newly adjacent components before queuing them. Keep the old order
  for disconnected blocks and reverse the final traversal as before.

For a fixed union forest and input block order this produces exactly the old
BFS order, including read-only blocks and disconnected components. Existing
map-order dependence in strong unions and read insertion is unchanged; this
is not a new globally deterministic variable-order policy. Gathering atoms
from the term DAG is also unchanged. The removed work is repeated atom-pair
enumeration, repeated traversal of long parent chains, and duplicate clique
edge storage.

No implication, diagram, coupling or valuation budget changes. No changes to
BDD admission, memo limits, proof rules, native assertions, race instrumentation
or CI timeouts. The component order is still only a proposal; ordinary BDD
reasoning decides the obligation.

## Bounded evidence

Cross-host probes target Linux/ARM64 from Linux/AMD64 without executing ARM
code. Each uses an external 120-second, 2.5-GiB process-tree RSS watchdog with
2-GiB host-available and 512-MiB disk floors. Temporary profiling harnesses are
not part of the production or native test changes.

At the published baseline, a fresh normal-search `step_first` probe exceeded
120 seconds. Its stack at 100 seconds was in the same component-order clique
loop, with 152 parameter names. The profile attributed 82.74 CPU seconds
(51.27% of samples) to repeated representative lookup; peak tree RSS was
1,237,123,072 bytes. No resource floor was crossed. A separate `step_count`
identity proof completed in 17.16 seconds; that initial probe's verdict-report
lookup was incorrect and was replaced with the native test's emitted-diagnostic
assertion in subsequent probes.

The focused race run passes:

- 500 seeded randomized differential comparisons against the old explicit
  clique/BFS algorithm, holding representatives and disconnected-block order
  fixed and including duplicate atoms and multi-hop forests;
- 131,072 repeated atom memberships with exactly one representative lookup per
  membership, rather than a lookup for every pair;
- actual BDD proof and wrong-value refutation under a repeated Boolean DAG;
- existing component/read placement, one-sided-arm, BDD lifecycle, positive and
  negative semantics, and unchanged-node-allowance tests.

The complete focused race command took 2.189 seconds of test time and remained
under its watchdog (1,122,009,088-byte peak build/test tree RSS).

This evidence alone does not establish a full native compiler-suite time or
success. In particular, the dispatch test compiles the complete hash and
encoding imports, including BLAKE3 functions even when main does not call
them; its previously observed 1,104.93-second time is not attributable to this
preprocessing without a separate profile. Native execution and the full
unchanged native inventory remain required.
