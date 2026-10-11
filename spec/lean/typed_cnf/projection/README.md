# Supplied typed-CNF source projection

This directory contains source construction and a fixed reviewed source inventory.
It does not invoke Go, Lean, a solver, a package manager, or another process.
Generated Lean files and compiled objects are build artifacts, not repository inputs.
No historical workspace path, old source artifact, receipt, or object is a runtime input.

Run the following nine stages, in order, under the bounded launcher:

```
python3 -B spec/lean/typed_cnf/projection/project.py STAGE \
  --repo-root /absolute/repository \
  --instance-root /absolute/initial-source \
  --work-root /absolute/projection-work
```

`STAGE` is `refutation`, `data`, `checks`, `permutation`, `nodes`, `bits031`,
`bits145`, `reuse`, or `assemble`. Roots must be existing canonical absolute
directories without symlinks. The work directory begins empty; each stage
exclusively creates its own directory. Reusing a partial stage is rejected.
The work directory may contain only the already completed stage directories.

The initial-source directory contains exactly `TypedCNFInstance` and its
18 files: `Data.lean`, `Checks.lean`, `Nodes00.lean` through `Nodes14.lean`, and
`Final.lean`. Set `OAK_TYPED_CNF_INSTANCE_OUT` to the initially nonexistent
`/absolute/initial-source/TypedCNFInstance` when invoking the Go instance writer.
The fixture paths are `asm/testdata/typed_cnf/raw.cnf` and `raw.lrat` within the
repository. Their exact bytes are pinned and checked before projection.

Each ordinary stage writes its source modules plus `PROJECTION.json`, schema
`typed-cnf-source-projection-v1`. Its `modules` entries are
`[module, sha256, bytes]`. The receipt explicitly says `kernel_checked: false`.
The source constructor checks the supplied certificate's full addition IDs,
ordered clauses and hints, live deletion behavior, and final empty addition;
the resulting propositions still require the separate Lean kernel compilation.

The assemble stage authenticates every selected source against the reviewed
closure and verifies that the final theorem has exactly 658 project modules in
its transitive import DAG. Only the pinned Lean distribution supplies
`Init.Data.List.Sort.Lemmas` and `Std.Tactic.BVDecide`. Assembly produces no
duplicate Lean files. It writes `repository.json`, `refutation.json`, and
`typed.json`, each with schema `typed-cnf-source-inventory-v1`, `family`, and
`modules` entries `[module, sha256, bytes, origin]`. The module path is obtained
by replacing dots with slashes and appending `.lean`. Resolve sources as follows:

- `origin: repo`: repository root / `spec/lean` / module path
- `origin: initial`: initial-source root / module path
- Other origins: projection-work root / origin / module path

The same containing root is the Lean `--root` for that source. The launcher
must separately authenticate the selected source and all produced/imported
objects, compile into its fresh private import root, and audit the final
theorem and axioms. Source inventory authentication is not a proof verdict.

The final inventory contains 26 repository modules (265,270 bytes), 162
refutation modules (5,799,628 bytes), and 470 typed modules (2,002,124 bytes).
The stages publish respectively 162, 33, 47, 1, 364, 17, 9, and 4 Lean modules;
later proof-specific stages supersede selected earlier sources. Nodes00 and
the corrected Final remain in the initial-source directory. All stages retain
their own immutable outputs, including the superseded intermediate files.
The anticipated physical total is 2,684,823 typed bytes, including the initial
18 modules, plus 5,799,628 refutation bytes. No final source copy is needed.

Each stage has an explicit 16,777,216-unit work counter and a 180-second wall
check. Published source is capped at 8 MiB per family and 16 MiB combined,
including retained intermediate source. Every metadata file is capped at
64 KiB. The outer launcher owns RSS, available memory/disk, process cleanup,
cumulative wall-time accounting, and final proof acceptance.

The expected inventory was transcribed from the independently reviewed closure
SHA256 `4087dd2664c3276383033d170a90fecb46672119b53347e01a15e9ad61d118ca`.
Each of its 658 rows was checked against that closure's successful stage plan,
receipt, source manifest, and source bytes during source authoring. The initial
writer inventory incorporates corrected Final SHA256
`484b1df961898bb3597c0cc045c6f77da00b7a33d06dada8f21db168fa8dddbc`.
These are provenance pins; the pipeline reads only repository inputs and fresh
artifacts produced by this run.

The source construction retains the successful depth-six refutation factoring,
typed data factoring, nested GateChunk witnesses with the decode-equality `rfl`
repair, direct 23-step output permutation, Node025–374 splitting, 64 Node031 and
32 Node145 scalar facts, and checker-only proof reuse at 121/242/294/340.
It does not include the rejected balanced-gate or mergeSort construction.
