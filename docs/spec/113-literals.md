# Literal sets: the `literals` declaration

Status: implemented (2026-09-13). The third golden case of the
performance track (`docs/checklists/performance.md`, multi-pattern
matching): a set of byte-string literals is declared once, and the
compiler projects the scanner the hardware prefers — Hyperscan's Teddy
prefilter over Oak's portable vectors — with its tables computed at
compile time and its soundness proved (`Oak.Teddy`). Measured at the
hand-written ceiling, ahead of Vectorscan and RE2
(`benchmarks/scanning/README.md`).

## 1. Declaration

```oak
Http: literals = {
  "GET ", "POST ", "PUT ", "DELETE ",
  "Host: ", "Content-Length", "Set-Cookie"
}
```

`Name: literals = { ... }` names a set of string literals separated by
commas or newlines; `literals` is a contextual keyword like `protocol`.
`pub` exports the projected functions. The literals are byte strings
(`10-syntax.md` §2a; `\xHH` admits any byte), and the set must be
scannable:

- at least one literal and at most 256 (sixteen groups of sixteen, §2);
- every literal at least three bytes — the prefilter classifies the
  first three bytes of each literal, and a shorter literal has no third
  byte to classify — and at most sixty-four, the carry a stream keeps;
- no duplicate — a duplicate would count every occurrence twice.

Each violation is `OAK-M0304`, as is a projected name the program
already declares. A literal may be a substring of another (`"Cookie: "`
inside `"Set-Cookie: "`): both are counted where both occur, since the
semantics is every occurrence of every literal.

## 2. Projection

The declaration projects, in the declaring package, with `pub` when the
declaration has it:

| Projected | Meaning |
| --- | --- |
| `name_count: (bytes: []u8): u32` | the number of occurrences of every literal in `bytes`, overlapping occurrences and occurrences of several literals at one position each counted |
| `name_find: (bytes: []u8, start: u32): u32` | the first position at or after `start` where some literal occurs, or `len(bytes)` when none does |
| `name_which: (bytes: []u8, pos: u32): u32` | the index (declaration order) of the first literal occurring at `pos`, or the number of literals when none does |
| `NameMatch: type = struct { at: u32, which: u32 }`, `name_match: (bytes: []u8, start: u32): NameMatch` | the first occurrence at or after `start` as one record: its position and the literal's index, `len(bytes)` and the number of literals when none |
| `name_carry: (): LiteralsCarry`, `name_feed: (c: [*]LiteralsCarry, bytes: []u8): u32` | streaming: `name_carry()` is the empty state; `name_feed` counts the occurrences ending in one more chunk — those starting in the carried bytes and completed by the chunk, and those inside it — and advances the carry to the last bytes so far (one less than the longest literal, at most sixty-three). The feeds over the chunks of an input sum to `name_count` of the whole |
| `name_literal_bytes: [N]u8`, `name_literal_starts: [K+1]u32` | the literals concatenated, and literal `j` as `bytes[starts[j] .. starts[j+1]]` |
| `name_literal_tables: [96 × G]u8` | the six nibble tables of the prefilter per group of sixteen literals (`G = ⌈K / 16⌉`), computed at compile time |

`name` is the declaration's name in snake case (`Http` → `http_count`).
The functions call the standard library's kernel (`stdlib/literals.oak`,
§3), whose functions the compiler clones into the program once under the
prefix `literals_teddy_`, so a program with a `literals` declaration is
self-contained and needs no import. A program may also use the kernel
directly on those names, as the differential tests do.

**Tables.** Literals are taken sixteen at a time into *groups*, each
with its own eight buckets and its own 96 bytes of tables: literal `j`
is in group `j / 16`, bucket `j % 8`, so a bucket holds at most two
literals. For each of the first three bytes `k` of every literal, the
group's table `k` holds sixteen bucket masks indexed by the byte's low
nibble and sixteen indexed by its high nibble: bucket `b` is set at
nibble `n` when some literal of bucket `b` has that nibble at byte `k`.
The compiler computes the `96 × G` bytes from the declaration
(`compiler/literals.go` `literalsTables`), the same way the kernel's
`build` computes them at run time. Grouping is what lets the set grow
(§4): a single group's buckets fill up, its nibble tables admit every
combination of their literals' nibbles, and verification runs through
every literal in the bucket; with two literals per bucket the prefilter
keeps its selectivity and a candidate lane verifies against two.

**Kernel.** Sixty-four bytes a step under the wrap-free guard
(`while len(bytes) >= u32(66) && off <= len(bytes) - u32(66)`, so every
load is proven in range and emitted without its check): for each of four
sixteen-byte blocks and each group, the block and the blocks one and two
bytes on are looked up through the group's three table pairs
(`simd.tbl_u8x16` on each nibble, ANDed), and the AND of the three
lookups is the block's candidate mask for that group — bit `b` of lane
`i` set when every one of the three bytes at `off + i` could begin a
literal of the group's bucket `b`. Every group's four masks are ORed
before any is examined, so a clean step is twelve loads, twenty-four
lookups per group, and one test; a step with candidates classifies again
out of line and each flagged lane is compared against its group's
bucket's literals with an explicit bound `pos + len <= len(bytes)`. A
set of one group runs a loop with the tables hoisted out of the scan,
the shape measured at the ceiling; the group loop sits inside the scan
loop so the classification inlines and the step stays call-free. The
last sixty-five bytes or fewer are tried literal by literal.

## 3. The standard library module

`import("literals")` exposes the same kernel for a set assembled at run
time: `build(patterns, starts, total, tables)` fills the 96-byte tables
(asserting every literal has at least three bytes), and `count`,
`find_from`, `which_at`, and `literal_at` take the set as `patterns`,
`starts`, `total`, and `tables`. The declaration is the compile-time
spelling of exactly this: its tables are `build`'s result, precomputed.

## 4. What is proved and measured

`spec/lean/Oak/Teddy.lean` models the tables as predicates — bucket `b`
set in table `k` at nibble `n` exactly when some literal of bucket `b`
has that nibble at byte `k` — and proves the prefilter **sound**
(`Oak.Teddy.sound`): a literal occurring at a position has its bucket's
bit set in the candidate mask there. Hence **exact** (`Oak.Teddy.exact`):
verifying a literal only where its bucket is a candidate finds exactly
its occurrences, so `name_count` is the number of occurrences and
`name_find` the first. `spec/lean/Oak/TeddyMasks.lean` closes the gap to
the bytes: the entry `build` stores — the OR of the bucket bits of the
literals whose nibble matches — has bit `b` set exactly when the
predicate holds (`bit_loEntry`, `bit_hiEntry`), the AND of masks has bit
`b` set exactly when each operand has (`bit_and`), and so the kernel's
test `(cand & bucket_bit(j)) != 0` on the stored masks is exactly
`Oak.Teddy.cand` (`bit_candMask`), with soundness restated on the masks
(`sound_mask`). `spec/lean/Oak/TeddyCount.lean` models the stepping: a
block's verified count is the occurrence count at each of its sixteen
positions (`block_eq_total`, from `exact`), a step is four blocks, and
`k` steps plus the tail over `[64 k, n)` are the occurrences over `[0, n)`
for any `k` with `64 k ≤ n` (`kernel_eq_total`) — the guard's choice
included. `spec/lean/Oak/TeddyStream.lean` states the streaming
contract: a feed counts the occurrences *ending* in its chunk, the feeds
of two adjacent chunks count what one feed of their union counts
(`countEndsIn_split`), a chunk holding the whole input counts exactly the
occurrences (`endsIn_whole`), and an occurrence ending in a chunk starts
within `longest - 1` bytes before it (`start_in_carry`), which is why a
carry of that many bytes joined with the chunk holds it whole. Not
modeled: that `feed`'s loop over the carried positions computes
`countEndsIn`; the differential tests (`compiler/e2e_literals_test.go`,
compiled and interpreted against a scalar reference, chunked feeds
against the whole count) cover it.

The theorems are per group: each group is a `LitSet` of at most sixteen
literals with its own tables, and a literal is verified against its own
group's candidate mask, so `sound` and `exact` apply to it unchanged.

Measured on sixteen HTTP tokens over 64 MB (`benchmarks/scanning/`):
the projected `http_count` runs at 0.10–0.11 ns/byte, the hand-written
NEON Teddy in C at 0.10, Vectorscan's literal database at 0.18, RE2's
alternation at 1.69, libc `memmem` per literal at 9.48; all report the
same count. Scaling with the set on the same input (`scale.c`,
`scan_oak_scale.c`, Vectorscan on random sets of the same sizes):

| Literals | Oak declaration | C, one group per sixteen | C, one group of eight buckets | Vectorscan |
| --- | --- | --- | --- | --- |
| 16 | 0.11 ns/byte | 0.10 | 0.10 | 0.27 |
| 64 | 0.36 | 0.30 | 1.35 | 0.95 |
| 256 | 1.45 | 1.09 | 18.7 | 0.95 |

One group of eight buckets collapses past sixteen literals — its
verification runs through every literal in a bucket and its nibble tables
admit every combination of the bucket's nibbles, sixteen thousand
candidate lanes per MB at 64 literals — which is why the compiler groups
by sixteen. The remaining gap at 256 is the sixteen groups' lookups per
step; Vectorscan switches to FDR there.

## 5. Direction

- Sets past 256 literals, and the gap at 256: a shift-or over wider
  windows (Hyperscan's FDR) instead of sixteen groups of lookups, and a
  rarest-byte choice of the classified bytes instead of the first three.
