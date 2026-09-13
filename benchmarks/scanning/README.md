# Multi-literal scanning: the third golden case

The question: which structure scans a byte stream for a set of literal
patterns fastest on today's hardware, and can Oak's portable vectors
express it at that speed with a proof? The references are Vectorscan
(Hyperscan's maintained fork, whose Teddy prefilter is the technique) and
RE2; the ceiling is a hand-written NEON Teddy in C.

## The task

Sixteen HTTP tokens (`literals.h`: `GET `, `POST `, `Content-Length`,
`Set-Cookie`, ... four to fourteen bytes, none a substring of another)
over 64 MB of random printable ASCII with the literals planted about once
per 4 KiB (`gen_input.c`, one shared generator). Every scanner counts
every occurrence of every literal and must report the same count.

## Results

Apple arm64, clang `-O2`, best of five, 2026-09-13. Taken while the Go
test suite occupied the machine; the ordering is stable across runs and
the absolute figures are upper bounds.

| Scanner | ns/byte | GB/s |
| --- | --- | --- |
| **Oak `http_count`, projected from `Http: literals = { ... }` (`literals.oak`)** | **0.10** | **10.10** |
| Hand-written Teddy, 3-byte prefilter, 64-byte steps (C, NEON) | 0.11 | 9.45 |
| Vectorscan `hs_scan`, literal database, block mode | 0.18 | 5.60 |
| Teddy, 2-byte prefilter, 16-byte steps (C, NEON) | 0.32 | 3.13 |
| RE2, alternation of the literals, `FindAndConsume` | 1.69 | 0.59 |
| libc `memmem`, one sweep per literal | 9.48 | 0.11 |

All six report 16,451 matches (16,447 planted, four accidental).

## What the numbers say

- The winning structure is Hyperscan's Teddy: literals hashed into eight
  buckets; for each of the first three bytes of every literal a low-nibble
  and a high-nibble table of bucket masks; per sixteen-byte block, two
  table lookups (`tbl`) per byte position ANDed give the buckets whose
  byte 0 matches at each position, the same over the block shifted by one
  and by two bytes gives bytes 1 and 2, and the AND of the three is the
  candidate mask. Sixty-four bytes a step with the four blocks' candidates
  ORed before any is examined: a clean step is twelve loads, twenty-four
  lookups, and one test. Candidates are verified against the bucket's
  literals with a bound on the input length.
- Three bytes of prefilter beat two by three times on random text: the
  candidate rate falls from about 16/95² to 16/95³ per position, and the
  verification, a scalar loop, stops mattering.
- The `literals` declaration reaches the ceiling: the compiler computes
  the nibble tables from the declared set and projects `http_count` over
  the standard library kernel (`docs/spec/113-literals.md`), and the
  emitted C runs at the hand-written Teddy's speed.
- Oak reaches the ceiling from its portable vector vocabulary
  (`docs/spec/93-simd.md`: `load_u8x16` under the wrap-free guard,
  `tbl_u8x16`, `and`, `shr`, `or`, `any`, `store_u8x16` to a sixteen-byte
  array for the verification lanes). The emitted C is the C ceiling's
  code shape; nothing was hand-tuned after emission.
- Vectorscan is slower here because its literal database is general: it
  handles streaming, start-of-match reporting, and pattern sets far
  larger than eight buckets hold, and its callback fires per match.
  RE2's alternation runs a DFA one byte at a time.

## What is proved

`spec/lean/Oak/Teddy.lean` models the tables as predicates — bucket `b` is
set in table `k` at nibble `n` exactly when some literal of bucket `b` has
that nibble at byte `k`, which is what `build_tables`' OR loop builds —
and proves the prefilter **sound** (`Oak.Teddy.sound`): a literal that
occurs at a position has its bucket's bit set in the candidate mask
there. Hence **exact** (`Oak.Teddy.exact`): verifying a literal only where
its bucket is a candidate finds exactly its occurrences, so the count the
kernel reports is the number of occurrences. `Oak/TeddyMasks.lean` takes
this to the bytes: the stored entries are OR-folds of bucket bits whose
bit `b` is the predicate, the AND of masks is bitwise, so the kernel's
`(cand & bucket_bit(j)) != 0` is exactly `cand` (`bit_candMask`). Not
yet modeled: the sixty-four-byte stepping and the scalar tail; the
differential check in `literals.oak`'s `main` and the six-way count
agreement above cover them.

## Landed

The kernel is `stdlib/literals.oak` (`import("literals")`) and the
declaration `Name: literals = { ... }` projects `name_count`,
`name_find`, and `name_which` over it with the tables computed at compile
time (`docs/spec/113-literals.md`). `literals.oak` here is that
declaration over the sixteen tokens, with a scalar self-check in `main`.
