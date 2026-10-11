# Supplied typed-CNF regression proof

This mandatory gate rebuilds the captured obligation's concrete-memory theorem
from a clean checkout. It runs no solver. The checked-in fixture contains 372
semantic DAG nodes, six declarations, the exact ordered 10,352-clause CNF and
the retained self-hosted LRAT proof (5,409 additions and 6,163 deleted IDs).

The final theorem is `TypedCNFInstance.supplied_raw_implication`:

```lean
∀ scalars memory,
  (concreteEval scalars memory n104).toNat ≠ 0 →
  concreteEval scalars memory n207 = concreteEval scalars memory n371
```

Its memory argument ranges over the concrete memory model, including reads
that alias at equal addresses. The final axiom audit permits only Lean's
standard `propext`, `Quot.sound` and `Classical.choice` and fails on missing,
ambiguous or extra output. A failed compiler invocation or placeholder proof
never yields a successful audit.

The Go capture-to-typed-model projection is independently reviewed, tested and
hash-bound; this theorem is not a universal refinement theorem for the Go
implementation, source-language compiler or target code. The gate adds no
compiler admission, `Proven` status or production solver budget.

## Clean execution

Required tools are Linux x86-64, Python 3.12 or newer, GNU timeout, a C/C++
compiler for Go's race instrumenter, Go 1.27.1 and Lean 4.33.1. The workflow
uses pinned public Go and Lean installations. Download dependencies with the
checked-in `go.mod` and `go.sum` before the offline gate. The gate fails if a
required tool, fixture, selector, generated module or receipt is missing.

```sh
python3 -B spec/lean/typed_cnf/run.py all \
  --repo "$PWD" --work /absolute/new/proof-directory \
  --ledger /absolute/persistent/proof-allocation \
  --go /absolute/go/bin/go --lean /absolute/lean/bin/lean \
  --cc /usr/bin/gcc --cxx /usr/bin/g++ \
  --modcache /absolute/prepared/pkg/mod
```

The repository must be clean and the output directory must not exist or lie
inside it, including through a symlinked parent. The work and ledger directories
are private. Reuse the same external ledger for every corrected local attempt
under one allocation. It reserves before spawning and authenticates each attempt's
source configuration and terminal receipt. An interrupted attempt with no final
receipt consumes its complete reservation. Changing work directories or invoking
the runner again does not reset that ledger. Unknown or incomplete descendant
cleanup blocks the allocation until separately authenticated cleanup is reviewed;
there is no automatic unblock. No old `.olean`, Lake cache, historical capture path, proof-run
receipt or generated source is an input. Go builds use a fresh cache and
offline dependency lookup. Lean imports use one fresh project directory plus
the pinned release's own library. Every output object and its transitive local
imports is authenticated through a successful source/command/product receipt.

Before any Go version probe, the runner creates private task HOME and XDG
configuration directories inside its evidence tree. It exclusively writes the
task's Go telemetry mode as `off\n`, binds that file in every stage's input
checks, and passes the same fixed environment to version probes and build tools.
This prevents a telemetry sidecar from outliving a preflight command. It changes
no host or user configuration. All later writes under those private directories
count against the same aggregate evidence cap; unexpected children still fail
the ownership check.

Corrected attempts freshly enumerate and hash the complete installed tool and
dependency trees. If a canonical tool-manifest chunk is byte-identical to one
already authenticated by this allocation's immutable configuration, specification
and receipt chain, the new configuration may reference that owned metadata file.
All old files remain charged to the aggregate cap. No compiler or proof output is
reused by this rule, and a new allocation writes every manifest chunk freshly.

For an independently reviewed local run, `generate` stops after freezing all
658 modules and their dependency order. `build` uses that same frozen source
set and ledger, requiring the reviewed `--config-sha256` and
`--build-plan-sha256`. Neither mode retries a failed stage. The workflow uses `all`
so this proof cannot silently become an optional or skipped check. This job runs
on every push and pull request and fails its workflow on failure; configuring a
repository branch-protection requirement is a separate repository setting.

## Finite construction limits

- One serial process tree; 9,000 seconds total charged stage time, with all
  attempts retained across corrected invocations in the same allocation.
  Historical development attempts are a separate ledger.
- A 15-second ownership control runs first. Its real missing-receipt and
  no-child paths must leave an unrelated sibling process alive. Cleanup uses
  observed parentage, positive process/start-time identities and Linux pidfds;
  PID 0 and reusable numeric process-group IDs are never signal targets.
  Discovery rechecks the child's live parent and the parent's live start identity
  before admitting an edge from the non-atomic process listing.
- Go compilation: 120 seconds. Normal/race gates: 90/120 seconds. Typed source
  emission and each of nine projection stages: 180 seconds. Each of the 658
  Lean modules: 180 seconds.
- Every ordinary 180-second stage reserves four seconds for shutdown: sampled
  stop and independent TERM at 176 seconds, KILL by 179 seconds. The watchdog
  shrinks with the remaining cumulative allocation.
- Sampled process-tree RSS: 3.75 GiB, including supervision; no Go address-space
  limit. Host available memory must remain at least 2 GiB, disk at least 512 MiB.
- Lean objects: 1 GiB total. Generated sources: 8 MiB per family, 16 MiB combined,
  counting every intermediate file path. Phase evidence: 32 MiB. Stage log:
  64 KiB; stage receipt: 14 KiB; product receipt: 2 KiB; other metadata file:
  64 KiB. The allocation charges retained physical artifacts across all of its
  work directories. Descendants must be reaped before success, including outer
  cancellation and missing-supervisor-receipt paths.
  Final success is published only after the runner's own cleanup passes, and it
  binds a separate outer-cleanup receipt.
  Stage, execution and invocation receipts also bind bounded process-observation
  sidecars, including failure paths. Each records the owner and direct owned
  children, observed PID/start/parent/group/command information, and actual
  raw or decoded join results. Missing identity stays unknown and refuses
  acceptance. The 64-identity/128-event/64-KiB observation caps do not limit
  descendant ownership or cleanup; overflow refuses success after cleanup.
  All physical sidecars count toward the same 32-MiB evidence cap. Preflight
  Git and tool probes use fixed environments and record their direct joins.

The workflow has a 190-minute outer timeout: five minutes each for checkout
and Go setup, 20 minutes for public tool and dependency setup, 155 minutes for
preparation/construction/closure, and five minutes to preserve evidence.
The inner 9,000-second construction budget covers stage execution, its input
checks, child process, shutdown and outer cleanup. Tool acquisition, preparation,
source-inventory freezing, parent receipt authentication and terminal library
hashing use the separately bounded setup/gate overhead. Resource failures are incomplete proofs; a digest,
partial counter or previously successful fixture never substitutes for the
kernel result.

The durable inputs' provenance and field schema are documented in
`asm/testdata/typed_cnf/README.md`. Generated proof modules remain build
artifacts. Their deterministic expected source hashes are checked before Lean
starts, and the final active import closure is exactly the frozen 658 modules.
