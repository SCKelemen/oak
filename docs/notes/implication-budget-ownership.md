# Implication budgets and phase ownership

The implication checker has several resource limits with different units.
`nodeBudget.remaining` is the existing mixed logical proof allowance: its
ordinary debit includes symbolic DAG admissions, main BDD race maxima and
fixed oversized-input penalties. It is not a count of all BDD allocations,
CPU operations, elapsed time or physical memory. Resource refusal remains
Unknown; it supplies no proof and cannot replace value, effect, trap-domain
or callee-closure obligations.

The normative admission rule is in [the assembler specification](../spec/94-assembler.md).
The implementation owners are `nodeBudget`, `impliesEqualDepth`,
`impliesEqualDepthUncached`, `dagNodes` and `pruneUnder` in
[`asm/loops.go`](../../asm/loops.go), with race and storage ownership in
[`bdd_race.go`](../../asm/bdd_race.go) and
[`bdd_resources.go`](../../asm/bdd_resources.go).

## Units and aggregation

| Phase | Unit and owner | What it measures |
| --- | --- | --- |
| Fresh implication entry | One `calls` increment, subject to `implicationCallLimit` | Unequal, uncached attempts, including a call-limit-crossing attempt. Equality and memo hits precede this count. |
| DAG admission | Distinct non-nil term pointers across premise and both sides in one bounded `dagNodes` walk | Sharing within one walk is counted once; subsequent calls can charge the same graph again. Condition, left, right and ordered argument edges are traversed. |
| Oversized DAG refusal | Fixed `blastNodeBudget` penalty | An existing refusal policy, not a measured BDD allocation or the partial DAG count. |
| Main BDD race | One maximum `completedNodes` across all orders after join | The largest retained store length for that race, not the sum or only the winner. These maxima accumulate across races. |
| Bounded child | Parent transfer `limit - child.remaining`, with the child's call count copied back | Spending already incurred by the child. Count its phase charges or its parent transfer, never both in one non-overlapping total. |
| Standalone premise pruning | Local `pruneNodeBudget` cap, currently 200,000, plus memory admission | `pruneUnder` has no ordinary-budget parameter; its local BDD work has zero direct ordinary debit. The cap creates no transferable allowance. |
| Process storage admission | Estimated bytes under the shared FIFO owner | An estimate controlling admitted storage, not a hard RSS bound and not proof credit. |

Prefix normalization, historical `pruneUnderFacts`, structural comparison and
other surrounding operations have no separate ordinary operation meter. A DAG
debit is an existing policy proxy, not evidence that every subsequent operation
is charged. Zero ordinary debit therefore does not imply zero CPU work.

`newBDD` starts with a terminal entry. Before releasing stores,
`releaseBDDStores` preserves their length in `completedNodes`. A per-order
counter consequently includes that terminal convention. Summing those counters
describes retained entries at separate completion boundaries, including repeated
independent stores. It does not count globally unique nodes, all attempted
operations, historical allocations or peak simultaneously live storage. Keep
that observational sum separate from the ordinary per-race maximum.

## Exhaustion and zero-debit proof routes

Structural equality and existing memo decisions remain available before fresh
call and DAG admission. After the call check, an unequal uncached request with
a nonpositive owner balance returns Unknown before another DAG walk/debit.
If recursive rules exhaust the owner, the parent skips its main BDD creation
and race. The existing bounded final split still runs; its rewritten equality
or memo paths can decide without ordinary node debit.

An admitted positive balance can still become zero or negative after an
existing DAG debit or penalty. Retain that exact balance: do not clamp it,
refund it or report a nonnegative-balance guarantee. An optimistic child's
actual spending and calls transfer once; its Unknown result does not acquire
ordinary memo authority merely by sharing the map. These admission guards
change neither theorem semantics nor the surrounding verdict obligations.

## Cancellation and cleanup ownership

Each order owns its blaster until its callback finishes. Only a valid result
that survives the final interruption check can decide the race. A winner
requests cancellation and wakes queued owners; all workers are joined before
the race returns. Admitted owners retain their reservations through store
release and scavenging. Denied or queued-cancelled owners consume initialized
stores without releasing a reservation they never acquired.

Store release sets `exceeded`; that surviving flag alone does not identify
the earlier refusal cause. Keep memory admission, interruption and node-limit
outcomes distinct where the observation supports it. The release byte count
covers specified arrays, not every allocation or RSS. Neither storage release
nor reservation release restores consumed logical allowance. See
[BDD resource admission and cache lifetime](bdd-resource-admission-2026-10.md).

## Structural work and future policy

Experimental premise-aware matching can meter header, edge, comparison, memo,
string and rewrite operations. Those algorithmic work tokens have a different
meaning from admitted DAG nodes or retained BDD entries. The production cleanup
does not install that matcher or convert its units into ordinary proof credit.
Likewise, diagnostic graph-copy visits and bytes belong to an observation
budget; a partial observation is inconclusive, not a proof result.

A future resource vector must explicitly choose units, owners, aggregation,
enforcement and compatibility for DAG admission, attempts, structural work,
per-order storage and currently unmetered phases. Any changed cap or conversion
is a new resource policy. Renaming a counter, refunding measured work or adding
observational totals cannot silently create entitlement.

## Portable controls and measurement scope

`post_exhaustion_test.go` covers fresh zero/negative refusal, equality and memo
fast paths, matching effects, positive-entry overdraw, oversized penalties,
child transfers, optimistic Unknown authority, final-node decisions and final
split success. Existing race controls cover cancellation, admission and joined
cleanup. These tests establish their exercised boundaries, not closure of an
unrelated whole-function proof.

A separately retained fixed-count diagnostic fixture measures zero/negative
admission, shortcut exhaustion and an admitted successor proof. It is excluded
from repository benchmarks because its bounded execution contract does not
support the ordinary adaptive benchmark invocation. The measured production
code is the same code used by the portable controls.

That comparison resets the entire owner and memo for each operation, with
fixture construction and a real warm call outside timing. Its calls, ordinary
debit, remaining allowance and verdict counts are checked alongside time and
allocations. Keep exhausted-work savings separate from admitted-path overhead
and retain all samples, including slower and inconclusive results. Such a
warm-fixture comparison does not establish compiler-wide speed, a stable
cross-machine improvement or any additional proof acceptance.

### Local validation and measurements, 2026-10-12

The two-guard candidate passed 18 focused roots, five additional existing
regression roots and nine race roots with two child paths. The separate
four-process baseline/candidate/candidate/baseline comparison retained all
48 benchmark rows and all 48 positive-contract test invocations. Each result
contains 10,000 measured calls, with three repetitions per case and process.
The six corresponding repetition ratios belong to two process-pair clusters;
they are not six independent process comparisons.

The first baseline process exceeded its original stage limit after eight
rows. That incomplete attempt was retained and excluded from paired results.
The completed comparison reused the identical fixtures and binaries under a
separately bounded longer window. It did not alter iterations or proof limits.

| Warm fixture | Baseline versus candidate observations |
| --- | --- |
| Fresh zero/negative owner | Both Unknown with one call. Ordinary admission debit fell from 513 to 0; allocation fell from 37,320 B / 15 allocations to 0 B / 0 allocations. All 12 candidate timing samples were below 1 ms for 10,000 calls, so their timing ratios are inconclusive. |
| Exhaustion in a shortcut | Both Unknown with two calls. Ordinary debit fell from 19 to 18 by skipping the exhausted main race. Allocations fell from 987–993 to 187 per call, with 22,888 B per candidate call. The observed median candidate/baseline elapsed ratio was 0.0362744. |
| Admitted unsigned successor | Both Proven with one call, debit 9 and one allowance unit left. Both used 728 B and five allocations per call. The paired elapsed-ratio median was 1.13526, while the process-cluster medians pointed in opposite directions, approximately 0.688 and 1.235. |

Positive-successor samples lasted 8.63–13.85 ms per 10,000 calls. Their spread
does not establish a stable 13.5% regression, and it also does not establish
zero overhead. At source level this path adds one integer balance check; the
second guard is not reached because the successor rule returns before the
uncached checker. No additional graph traversal, worker, memo operation or
allocation is introduced on that path. This bounds the added source work,
not its machine-cycle or nanosecond cost.

The evidence supports removal of the exercised exhausted work with unchanged
positive functional/accounting and allocation behavior. Positive-path timing
remains uncertain. It does not establish whole-compiler throughput, a stable
performance improvement across environments or closure of the retained proof
obligation. The fixed-count fixture, parser and operational receipts remain
external diagnostic evidence, rather than repository benchmark infrastructure.
