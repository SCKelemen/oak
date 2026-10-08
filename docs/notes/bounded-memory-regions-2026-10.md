# Bounded memory indices, October 2026

The next verifier optimization adds conservative unsigned index intervals to
`asm.memoryAt`. The previous modular-congruence shortcut cannot separate
`x & 255` from `256 + (y & 255)`: the masks prevent linear normalization.
Their intervals, [0,255] and [256,511], are disjoint, so the later write
cannot affect the read and no equality/ITE terms need to be constructed.

## Scope and correctness

- Existing local-array owners already separate distinct buffers. Existing
  derived views flatten to the owner's root plus an element offset. This change
  uses that machinery; it does not infer pointer disjointness from names.
- Native-width intervals start with existing known-bit information. Addition
  refines them only if the largest sum fits, subtraction only if the smallest
  left operand is at least the largest right operand. Conditional arms join.
- Truncation retains a range only if its upper endpoint fits the target word.
  Otherwise known bits bound the truncated value, or it remains the full word.
  The addition precondition itself avoids uint64 overflow.
- Bounds are memoized per read, after the existing congruence shortcut. An
  unbounded read avoids analyzing each write's range. Guards, span lengths,
  and unchecked extents do not supply assumptions.
- Disjoint guarded writes can also be dropped. Overlapping ranges, possible
  wraparound, and memory snapshot markers retain their original semantics.
- `Oak.IndexBounds` proves non-wrapping arithmetic, width adaptation, joins,
  intersection, and guarded-write removal. These are arithmetic laws, not a
  formal refinement of the Go analyzer. Exhaustive mixed-width evaluation
  independently checks that implementation.

The initial bounded-offset slice was not path-sensitive range inference and an
arbitrary shared symbolic base still hid otherwise disjoint offsets. The
common-base follow-up below closes that particular case; general path-sensitive
ranges remain open. Standalone Oak lowering and solver/certificate acceptance
are unchanged.

## Common-base follow-up

The next slice cancels addends common to two 32-bit indices before comparing
their residual intervals. It therefore proves `base + (x & 255)` disjoint from
`base + 256 + (y & 255)` even though the arbitrary `base` makes both whole-term
intervals the full word. Additions flatten only at the compared width, common
terms cancel as a multiset, and each residual sum must fit without wrapping.
A narrower nested addition, a different base, more than sixteen addends, or a
possibly wrapping residual fails closed. The same relation removes dead writes
in `memoryAt` and unnecessary functional-consistency pairs in the bit blaster.

`Oak.IndexBounds.common_base_disjoint` proves that adding one `BitVec` base
preserves inequality of disjoint bounded offsets. Go tests exhaust all 4-bit
values for the admitted shared-base shape and pin duplicate bases, different
bases, residual wraparound, and complete write-log removal.

On the Apple M4 Max development host, a 128-write common-base construction
with the relation disabled took 21.6--22.0 µs, 400 allocations, and 71,336
allocated bytes, and retained the 128 alias conditions. With cancellation it
took 35.7--37.8 µs, 29 allocations, and 36,752 bytes, and returned the entry
value directly. The analyzer itself spends more CPU to establish the fact; the
win is removing the conditional DAG and its later proof cost.

## Validation

`TestIndexBoundsExhaustive` evaluates mixed-width DAGs over every valuation of
small inputs, including truncations, unsupported operations, and conditional
joins. Separate tests cover 32/64-bit overflow and underflow, concrete guarded
store semantics for overlapping/disjoint/wrapping intervals, and memory
snapshot preservation. ARM64 and RV64 verifier fixtures cover distinct local
buffers, disjoint subslices, and rejection of a wrong result after an
obviously overlapping subslice write.

Reproduction:

```sh
go test ./asm -count=1
go test . -run '^(TestOakSolverAgrees|TestOakSolverAgreesOnSerializedProblems|TestOakShellAgrees)$' -count=1
(cd spec/lean && lake build)
go test ./asm -run '^$' -bench 'BenchmarkMemoryAt(BoundedRegions|Overwrite)$' -count=3 -benchtime=200ms
```

## Focused benchmark

Linux amd64, AMD EPYC 9V74, Go 1.27.1. A read in a 256-element region follows
128 writes in later regions of the same root. The benchmark constructs the
read term; it does not include solving it. Three short samples are sufficient
for allocation counts, not a robust end-to-end latency claim.

| Metric | Before | After |
| --- | ---: | ---: |
| Allocations/read | 395 | 24 |
| Allocated bytes/read | 70,792 | 36,208 |
| Median construction time | 50.27 µs | 43.19 µs |

The existing last-overwrite benchmark retains 7 allocations and 736 bytes per
read. No standalone self-hosted solver speedup is claimed for this change.

## Extents scheduling regression check

PR #666's CI and Formal Verification runs both completed successfully. Its
previous single extents sample rose from 35.20 to 43.81 seconds elapsed, while
CPU rose only from 34.60 to 35.50 seconds. To investigate, prebuilt test binaries
from `9102507c` (before scheduling) and `8735623e` (after scheduling, before this
bounds change) each ran `BenchmarkOakShell/extents` three times, alternating
order. Solver compilation was warmed up first. `os.wait4` recorded each
process tree's CPU and peak RSS independently. Other validation jobs ran on
the host during part of the measurement; these are diagnostic samples.

| Build | Elapsed samples (s) | CPU samples (s) | Peak RSS range (KiB) |
| --- | --- | --- | --- |
| Before #666 | 30.08, 32.83, 31.60 | 30.09, 32.01, 30.66 | 270,032–270,112 |
| After #666 | 31.35, 33.93, 33.44 | 30.94, 31.78, 32.79 | 269,744–270,108 |

Median elapsed increased 5.8%, median CPU 3.7%, and memory stayed effectively
flat. The earlier 24% elapsed increase did not reproduce. A small scheduling
CPU cost remains plausible; these three samples do not establish statistical
significance or attribute it to a particular phase. This change leaves the
scheduler unchanged rather than claiming to fix that overhead.

The full assembler suite, Go/Oak solver and shell corpus cross-checks, and
full Lean build passed locally (326 build jobs before the subsequent
upstream Wasm proof update).
