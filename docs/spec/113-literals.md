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

- at least one literal;
- every literal at least three bytes — the prefilter classifies the
  first three bytes of each literal, and a shorter literal has no third
  byte to classify;
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
| `name_literal_bytes: [N]u8`, `name_literal_starts: [K+1]u32` | the literals concatenated, and literal `j` as `bytes[starts[j] .. starts[j+1]]` |
| `name_literal_tables: [96]u8` | the six nibble tables of the prefilter, computed at compile time |

`name` is the declaration's name in snake case (`Http` → `http_count`).
The functions call the standard library's kernel (`stdlib/literals.oak`,
§3), whose functions the compiler clones into the program once under the
prefix `literals_teddy_`, so a program with a `literals` declaration is
self-contained and needs no import. A program may also use the kernel
directly on those names, as the differential tests do.

**Tables.** Literal `j` is in bucket `j % 8`. For each of the first three
bytes `k` of every literal, table `k` holds sixteen bucket masks indexed
by the byte's low nibble and sixteen indexed by its high nibble: bucket
`b` is set at nibble `n` when some literal of bucket `b` has that nibble
at byte `k`. The compiler computes the 96 bytes from the declaration
(`compiler/literals.go` `literalsTables`), the same way the kernel's
`build` computes them at run time.

**Kernel.** Sixty-four bytes a step under the wrap-free guard
(`while len(bytes) >= u32(66) && off <= len(bytes) - u32(66)`, so every
load is proven in range and emitted without its check): for each of four
sixteen-byte blocks, the block and the blocks one and two bytes on are
looked up through the three table pairs (`simd.tbl_u8x16` on each
nibble, ANDed), and the AND of the three lookups is the block's
candidate mask — bit `b` of lane `i` set when every one of the three
bytes at `off + i` could begin a literal of bucket `b`. The four masks
are ORed before any is examined, so a clean step is twelve loads,
twenty-four lookups, and one test; a block with candidates is stored to
a sixteen-byte array and each flagged lane is compared against its
bucket's literals with an explicit bound `pos + len <= len(bytes)`. The
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
(`sound_mask`). Not yet modeled: the sixty-four-byte stepping and the
tail; the differential tests (`compiler/e2e_literals_test.go`, compiled
and interpreted against a scalar reference) and the harness's six-way
count agreement cover them.

Measured on sixteen HTTP tokens over 64 MB (`benchmarks/scanning/`):
the projected `http_count` runs at 0.10 ns/byte, the hand-written NEON
Teddy in C at 0.11, Vectorscan's literal database at 0.18, RE2's
alternation at 1.69, libc `memmem` per literal at 9.48; all report the
same count.

## 5. Direction

- A `find` that also reports which literal matched, as one call — today
  `name_which(bytes, name_find(bytes, start))`.
- Streaming: a set scanned across buffer boundaries with the last two
  bytes carried, the way `utf8.valid` carries its incomplete mask.
- Larger sets: more than eight buckets when the set is large enough that
  bucket sharing dominates verification, and a rarest-byte choice of the
  three classified bytes instead of the first three.
- The stepping and the tail in Lean, over the block model of
  `Oak.Utf8Blocks`.
