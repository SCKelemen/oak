# Compiler syntax-walk metadata cache, October 2026

The compiler's pre-order syntax walker repeatedly asks reflection for every
struct field's export metadata. The `compiler-rest` timeout stack included
`collectDeclaredNames` in this walker; that stack sample motivated measurement,
but does not by itself establish a whole-suite profile.

`syntaxFields` now caches the ordered exported-field indices per `reflect.Type`.
The shared `sync.Map` publishes immutable slices. It stores no AST values,
visitor results, or visited-node set. A rewritten tree is read afresh, shared
nodes are visited at every occurrence, and returning false from a visitor
still prunes only that pointer's descendants. The existing unspecified map
iteration order and treatment of unexported fields/arrays are unchanged.

## Evidence

Linux amd64, AMD EPYC 9V74, Go 1.27.1; baseline `817bc0ae`. These are short local
measurements, not confidence intervals or self-hosted solver timings.

| Workload | Baseline median | Cached median | Change |
| --- | ---: | ---: | ---: |
| Parsed time AST traversal | 6.881 ms | 2.091 ms | 69.6% less time |
| Parsed JSON AST traversal | 5.387 ms | 1.602 ms | 70.3% less time |
| JSON-import program to C source | 1.483 s | 1.342 s | 9.5% less time |
| Strings-import program to C source | 0.959 s | 0.882 s | 8.0% less time |

Traversal uses three 300 ms samples after warming the field plans. C-source
emission uses three samples of three compilations after warming the existing
prelude caches. It includes parsing, checking, lowering and emission, but no
external C compiler. Allocation counts and bytes were effectively unchanged;
this change avoids repeated metadata work, rather than caching compilation
results. The one-time metadata cache allocation is outside the warm traversal
measurement.

Before/after generated C for both programs was byte-identical when compiled
from the same fixed input paths. The benchmark uses temporary package paths,
which appear in generated C and can change output hashes and lengths across
runs; benchmark output size alone is not a semantic equivalence check.

## Validation

- Compare pointer-occurrence counts with the original uncached traversal on
  complete parsed time and JSON trees.
- Check explicit pre-order visitation, pruning, shared occurrences, nil
  pointers, unexported fields, ignored arrays, replacements and visitor mutation.
- Race-test concurrent first use of a previously unseen struct type.
- Race-test the existing inliner seam, helper, naming, literal, view, proof and
  match-context integration fixtures (the command below).

```sh
go test -race ./compiler -run '^(TestWalkSyntax|TestInliner|TestInlineHelpers|TestE2EInline|TestE2ESmallHelpers)' -count=1
go test ./compiler -run '^$' -bench '^BenchmarkWalkSyntax$' -benchtime=300ms -count=3
go test ./compiler -run '^$' -bench '^BenchmarkCompileWithSyntaxWalk$' -benchtime=3x -count=3
```

This changes only the Go compiler's traversal implementation. It is not a new
formal compiler-refinement proof, and does not claim that the standalone Oak
compiler or solver has the same speedup.
