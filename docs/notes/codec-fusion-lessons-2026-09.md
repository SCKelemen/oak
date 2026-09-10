# Note: what the ml scheduler's fusion and tiling teach the codecs

**Status: assessment, no decisions taken.** 2026-09-10, `specification`
branch. Source: a read of `github.com/SCKelemen/ml` (fusion boundaries in
`graph/graph.oak`, kernel assembly in `schedule/schedule.oak`, emission in
`emit/emit.oak`, RFC 0001 and design-log entries 0020–0039, the license
theorem `spec/lean/Ml/Schedule.lean`) against `docs/spec/71-codecs.md`,
`stdlib/json.oak`, and the derivation in `compiler/codecs.go` and
`compiler/codec_decode.go`.

## How ml does it, in one paragraph

Fusion is decided by *boundaries* on a lazy node arena, not by search:
reductions, inputs, realize targets, and movement sources are boundaries; a
node read twice becomes one only when recomputing it would exceed a small
limit. A kernel is the member set reachable from an output without crossing
a boundary, plus a second reduction over the same iteration space or an
elementwise epilogue when the dependence shape allows. There is no kernel
IR: the member set is emitted straight to C or MSL, and identical member
structure hashes to the same kernel. Tiles are hand-picked constants gated
by structural pattern matches and measured thresholds; lane and run counts
are part of the semantics because float addition is not associative. Tails
are predicated loads with zero fill, or an eligibility fallback to the
scalar kernel — never a scalar tail loop. Every fusion change is licensed by
one theorem (inlining non-boundaries equals the graph value) and checked by
an in-tree oracle bit for bit, with counters asserting that fusion fired.

## What transfers

| Idea | ml mechanism | Codec analog | Verdict |
| --- | --- | --- | --- |
| One bounds check per record, not per field | Realized buffers are checked once at kernel launch; inlined members never re-check | `recordEncoder` preflights the record once, then each nested `__oak_json_write_<field>` re-measures and re-checks. Derive a private unchecked write form for use only under the derived parent's preflight. Nested records recompute `encoded_size` at every level today, O(depth) redundant work | **Transfers directly.** The recompute-vs-materialize question ml answers with `RECOMPUTE_LIMIT` is exactly the nested size question |
| Carry pass-1 results into pass 2 | Two-pass dependent fusion keeps the first pass's value in a register for the second | Size pass and write pass are already two passes for the "output unchanged on failure" contract. Memoize per-field sizes from the size pass into locals for the write pass instead of recomputing | **Transfers** as "carry, do not fuse": a single speculative pass with rollback would break the contract |
| Fuse UTF-8 validation with the string scan | Horizontal fusion: two accumulators over one load | `json_string_run` already loads `U8x16`; OR-accumulate the high bits in a second lane set and run the multibyte validator only when the mask is nonzero | **Transfers as a pattern**, with a constraint ml lacks: `InvalidEncoding` precedence over `InvalidSyntax` must be preserved |
| Classify, then emit | Structural predicates select an emitter (`tiled_matmul_shape`, `vectorizable`); no loop-nest IR | `codecDeriver` is already a per-field switch. A classification pass over the field list (all-ASCII plain keys, fixed-width fields, statically known total size) before emission lets statically sized records skip the size pass entirely | **Transfers as design shape.** Do not build a schedule IR |
| Oracle and counters | In-tree slow path is the oracle; fusion counters asserted in tests; a Lean theorem licenses every fusion | Keep every pre-fusion helper as the oracle (`json_read_integer_slow` already is); assert on the generated C that no nested size call survives, as §4's wrapper-absence checks do; a theorem that inlined field helpers equal their sequential composition is feasible because encoding is pure over the record | **Transfers directly**, and is the part to do first |

## What does not transfer

- **Tile choice as semantics.** Lane and run counts are canonical in ml
  because float sums are order-dependent. Byte codecs are exact; a block
  size carries no meaning and can change freely.
- **Predicated zero-fill tails.** Needs a semantic zero and no error
  precedence. JSON has neither, and §11 and §16 forbid reading past the
  input. The existing SIMD-block-plus-scalar-tail shape in `json.oak` stays.
- **Thread and lane mapping, threadgroup staging, register prefetch.** GPU
  only; §11 forbids implicit parallelism in codec paths.
- **Boundary by consumer count.** Codec field trees are trees; there is no
  DAG sharing to arbitrate.
- **Runtime kernel cache.** Codecs are monomorphized at compile time.

## If taken up

Order by evidence first: the oracle-and-counter discipline, then the
per-record bounds check with the unchecked inner form, then carrying
sizes across passes, then the fused validation lane. Each step is a
measured change against the simdjson comparison the codecs spec already
keeps, with the pre-fusion helper as the witness.
