# Performance checklist

Everything that must be fast, and how to know it is. One flat list,
grouped by where the question bites. Each item is a question; "no" is a
finding. See [README](README.md) for the shape of an item and how to run a
pass. The [correctness list](correctness.md) wins every conflict; items
here say where the tension is real.

Sources, abbreviated in parentheses: TigerStyle/TigerBeetle (TB),
data-oriented design (DOD), mechanical sympathy (MS), simdjson, simdutf,
Hyperscan, mlx, tinygrad, Futhark, Mojo, Zig, Odin, Rust, Go, Swift,
Halide, and the papers named inline.

---

## 0. The method: golden implementations and the expressiveness gap

The organizing question is not "how do we make this fast?" but:

> The fastest known implementation of this exists, in C, Zig, Rust, or
> intrinsics. **Why can it not be written in Oak, with its correctness
> checked?** Every "because Oak cannot say X" is an expressiveness gap,
> and the gap — not the benchmark — is the finding.

This is the ml pilot's principle made general: find the optimal structure
for the golden use case, wrap it in correctness proofs, and make that the
simplest thing a user can write, so the language dictates the fast
implementation and the user never fights for performance
(`docs/notes/ml-language-requests-2026-09.md`).

- [ ] **Name the golden implementation.** For the domain under review, is
      the state-of-the-art implementation identified by name and version,
      with its measured throughput on a stated machine, before any Oak
      design work? "Fast" without a named competitor is a feeling.
      — Oak: `BENCHMARKS.md`, `benchmarks/`.
- [ ] **List its defining techniques.** Has the golden implementation
      been read (not skimmed) and its techniques written down as a list —
      the ten things without which it would be ordinary? Each becomes a
      row in §1 and a question in §2.
- [ ] **Port it literally first.** Has the golden implementation been
      ported to Oak as closely as the language allows, before any
      "idiomatic" rewrite? The places the port had to deviate are the
      expressiveness findings; an idiomatic rewrite hides them.
      (ml pilot, dbs frame scan, hypervisor ports) — Oak:
      `docs/notes/hypervisor-port-feedback-2026-09.md` is the pattern.
- [ ] **Classify every deviation.** For each place the port could not
      follow the original, which is it: (a) Oak lacks the operation, (b)
      Oak has it only in `unsafe`, (c) Oak has it but the checker cannot
      prove the precondition so a check remains, (d) Oak has it but the
      lowering does not produce the same machine code, (e) the original
      relies on undefined behavior and the technique needs a stated
      semantics. Only (e) is a reason to accept slower code; each of the
      others is a language or compiler item.
- [ ] **Ask what fact would make it safe.** For each (b) and (c), which
      single semantic fact — a bound, a disjointness, an alignment, a
      padding contract, a declared law, a validated state — would let the
      checker discharge the obligation? Is that fact a phantom type,
      a refinement, an effect, or a protocol state? (constitution: one
      fact, many projections) — Oak: `00-constitution.md`.
- [ ] **Measure the port against the golden, per byte or per element.**
      Is the gap stated as a ratio on the same machine and input, with the
      cause attributed (a remaining check, a missed vectorization, a
      call not inlined) rather than guessed? — Oak: `BENCHMARKS.md`
      keeps Go, Rust, Zig, simdjson, simdutf comparisons.
- [ ] **Assert the emitted code.** Does a test inspect the emitted C or
      assembly and assert the technique survived lowering (no bounds
      check in the inner loop, a `vld1q` where a vector load was meant,
      no call in the hot path)? Counters that the fast path fired belong
      here too. (ml counters, simdjson) — Oak: `71-codecs.md` §4
      wrapper-absence checks.
- [ ] **Make it the simplest spelling.** Once the golden structure is
      expressible and checked, is it what the obvious Oak program lowers
      to — or does the user still have to know the trick? A trick the
      compiler knows is a language feature; a trick the user must know is
      folklore. — Oak: `05-ergonomics-and-cost.md` Performance
      transparency.

## 1. Golden implementations by domain

The table is the standing agenda. A row is closed when the Oak version is
within its stated target of the golden implementation, with the
techniques expressible in safe Oak or under a recorded contract, and the
oracle agreeing bit for bit. Add rows; do not remove them.

| Domain | Golden implementation(s) | Defining techniques (expressiveness questions in §2) | Oak status |
| --- | --- | --- | --- |
| JSON parsing | simdjson (Langdale & Lemire 2019), simdjson On-Demand | two-stage parse (structural index then tape); byte classification by nibble shuffle; prefix-XOR quote masks and odd/even backslash runs; `ctz` bitmask-to-index with over-write into slack; two-block software pipelining; sentinel-terminated index; padded input with unspecified content; UTF-8 lookup4 fused into stage 1; SWAR eight-digit parse; Eisel–Lemire floats; word-compare atoms; forward-only On-Demand iterator with recoverable vs fatal errors; grow-only parser buffers from a closed form; runtime CPU dispatch; no backtracking | 1.13× simdjson on M1, 1.40× on EPYC for one typed schema (`BENCHMARKS.md`); `71-codecs.md` §16–§19; structural index, On-Demand, float fast path, table lookup, movemask, `ctz`, `mul_hi` absent; runtime dispatch absent; pass recorded in `docs/notes/codec-text-extraction-2026-09.md` |
| UTF-8 validation / transcoding | simdutf (Keiser & Lemire 2020, 2021, 2022), Zig/Rust std validators | three nibble-table lookups over each adjacent byte pair plus a saturating third/fourth-continuation check; cross-vector byte shift for the previous block; incomplete-tail compare; ASCII fast path by OR/max reduce; reject fast in lanes, locate the error with the scalar oracle; tail copied into an inert-filled stack block (no over-read); mask-indexed generated shuffle tables for transcoding with pattern fast paths; non-validating lane-count sizers with narrow accumulators; `_valid` API level over validated input; `trim_partial_utf8` for stream cuts; runtime dispatch | `stdlib/utf8.oak` (`utf8.valid`), the lookup4 validator in safe Oak over `tbl`/`shr`/`subs`/`prev`: 12.3 GB/s with the sixty-four-byte step beside simdutf 12.9 and simdjson 12.9 on Apple arm64 (`benchmarks/state-machines/cross`), tables proved against Table 3-7 in `Oak.Utf8Lookup`; open: the stream composition in Lean; transcoder is scalar and three-pass (`stdlib/strings.oak`); no error position; `string` as the `_valid` level exists but no stdlib function consumes it |
| Multi-pattern matching / regex | Hyperscan (Teddy, FDR, shift-or, Rose), RE2, `memchr` crate | SIMD literal prefilters (Teddy: shuffle-based multi-literal); shift-or / bit-parallel NFA; DFA with byte-class compression; no backtracking, linear time; state in registers; streaming with saved state | recorded as a stdlib workstream, not started (`ml-language-requests` "The regex question") |
| Hashing | BLAKE3, xxh3, wyhash, hardware CRC-32C, SipHash for keyed | wide state in registers; tree hashing for parallelism; hardware CRC/AES instructions; unaligned reads; seeded keys against collision DoS | SHA-256, BLAKE3, CRC-32C within ten percent of Rust (`stdlib/hash.oak`, `benchmarks/kernels`); hardware CRC and seeding: check |
| Sorting | pdqsort (Peters), ips4o, vqsort (Google, Highway), radix sort | pattern-defeating pivots; branchless partition (Edelkamp–Weiß block partition); insertion sort tail; SIMD sorting networks; radix for keys with known width | pdqsort with laws (`sam/stdlib-pdqsort`, `sam/pdqsort-laws`); branchless partition and vqsort: check |
| Hash tables | Swiss table (abseil), F14 (folly), hashbrown | open addressing with SIMD group probing over control bytes; metadata separate from slots; power-of-two masks; robin hood / linear probing with SSE compare | not stated; `standard-library-design.md` first containers are Ring, BitSet, Pool |
| Memory allocation | mimalloc, jemalloc, TB static allocation, Zig `std.heap` | free-list sharding; thread-local heaps; size classes; bump/arena; no allocation after init | arenas, slabs, pools, handles as types (`60-effects-allocation.md` §5–§9); allocation phase enforced (`85-discipline.md` §4) |
| Dense linear algebra | mlx (Metal), CUTLASS, BLIS, tinygrad, Halide | tiling by cache/register level; packing; FMA microkernels; threadgroup memory; fusion of epilogues; lazy graphs; kernel caching by structure hash; unified memory zero-copy | kernels with Metal and C realizations (`56-kernels.md`), `stdlib/tensor.oak`; check elision, threadgroup reductions, records as kernel params open |
| Reductions | Futhark, mlx `reduce`, CUB | fixed-tree grouping as semantics; lane-wise partials then horizontal; segmented reductions; regrouping licensed by declared laws | `reduce.tree` balanced-counter tree, `laws {associative}` (`55-parallelism.md` §4, `10-syntax.md` §14a); no backend consumes laws yet |
| Storage engine / WAL | TigerBeetle, LMDB, RocksDB (for contrast) | static allocation; batched fsync; direct I/O with aligned buffers; checksums on every block; zero-copy frame views; io_uring completion rings; deterministic simulation | `io/sim` and `io/native` completion rings (`120-io.md`); `SimDisk` six faults; borrowed decoded frame views; direct I/O alignment: check |
| Network / rings | LMAX Disruptor, io_uring, DPDK, TB message bus | SPSC/MPSC rings with power-of-two masks; cache-line-padded heads and tails; batching; single writer; no locks | SPSC expressible with `Atomic[T]` and `(align: 64)` (hypervisor ask 11); rings as memory-model consumers wanted (dbs ask 8) |
| Compression | zstd, LZ4, FSE/ANS | hash-chain matching; SWAR copies with overlap; table-driven entropy decoding; branchless decode loops | not stated |
| Number formatting / parsing | Ryu, Dragonbox, Eisel–Lemire, fast_float | 128-bit multiply; precomputed power tables; shortest round-trip | float printing with round-trip digits (`85-discipline.md` §5); Eisel–Lemire in codecs: check |
| Interpreters / VMs | LuaJIT, wasm3, CPython 3.11 (computed goto), CoreCLR | threaded dispatch (computed goto or tail calls); register VM; inline caches; NaN-boxing; tagged pointers | trampolines for mutual tail recursion (`85-discipline.md` §2) is the safe form; pointer tagging: `standard-library-design.md` §10 |
| Hypervisor / kernel paths | seL4, Linux fast paths, the `os` repo's Zig modules | MMIO with exact barriers; per-CPU state; interrupt paths with no allocation; fixed-capacity intrusive containers; bitmaps | `os-structures-survey.md` gap list; EL2 chapters `99`–`101` |
| Cryptographic constant time | BoringSSL, libsodium, HACL* | no secret-dependent branches or indices; constant-time select by mask; verified against a model | not stated; a `secret` phantom on scalars is the obvious fact to add |

## 2. Expressiveness inventory: can Oak say this, and check it?

Each item is a technique the golden implementations rely on. The question
is whether safe Oak (or Oak under a *recorded* contract) can express it
so that the lowering is the same machine code C would produce. "Only in
`unsafe` with no recorded fact" is a finding; "expressible, but a check
remains that a fact could elide" is a finding.

### 2a. Memory access shapes

- [ ] **Unchecked indexing under a discharged bound.** When the checker
      holds `i < len(x)`, does the access lower to a bare load? Is the
      elision recorded as a discharged obligation? (simdjson, every inner
      loop) — Oak: `50-borrowing.md` "Extent facts and proof-based
      bounds-check elision (implemented subset)"; kernel check elision
      open (`56-kernels.md` §3).
- [ ] **Overlapping and unaligned vector loads.** Can a 16-byte load at
      an arbitrary offset be expressed over a view, with the in-bounds
      fact `off + 16 <= len` discharged or a stated padding contract
      standing in? Can two overlapping loads cover a tail without a
      scalar loop? (simdutf, memchr, simdjson) — Oak: `93-simd.md`,
      `71-codecs.md` §11; padding contract: check.
- [ ] **Padded input as a type-level fact.** Can a buffer promise
      "readable for N bytes past `len`" as a phantom parameter, so a
      block loop's over-read is safe by type rather than by convention?
      (simdjson `SIMDJSON_PADDING`) — Oak: not stated; §16 forbids
      over-read; the fact would lift the ban where the caller provides
      padding.
- [ ] **Predicated tails.** Can a masked load with zero fill be expressed
      for element types where zero is a semantic identity, with the
      compiler choosing predication or a scalar tail per target? (ml,
      SVE/RVV) — Oak: `93-simd.md` §4.1 tail and mask policy.
- [ ] **Fault-only-first loads.** For scalable vectors, can a
      restartable load be expressed for strings of unknown length?
      (RVV, SVE `ldff1`) — Oak: `93-simd.md` §4.2.
- [ ] **Small fixed-size copies as register moves.** Does copying a
      record of 16 or 32 bytes lower to register moves, not a `memcpy`
      call? Does a `[N]u8` copy of constant N lower to wide loads and
      stores? (Zig, Rust) — Oak: check emitted C for
      `record`/`[N]T` copies.
- [ ] **Overlapping stores for copies.** Can an LZ-style copy that
      overlaps its own source (match distance smaller than length) be
      expressed with defined semantics? (LZ4, zstd) — Oak: not stated;
      needs a stated byte-at-a-time semantics or a `span` op.
- [ ] **Type punning with a stated result.** Can `f32` bits be read as
      `u32`, or a `[4]u32` as a `U32x4`, with a total, defined bitcast
      rather than a union or pointer cast? (Zig `@bitCast`, Rust
      `transmute` for POD) — Oak: `{target}_bits_{source}` in
      `20-types.md` §11.1 for scalars; vectors and arrays: check.
- [ ] **SWAR on machine words.** Can eight bytes be loaded as one `u64`
      and processed with masks (has-zero-byte, has-byte-less-than, digit
      pack) with the endianness stated? (Lemire, Mycroft) — Oak:
      `71-codecs.md` §19 word-parallel scanning.
- [ ] **Restrict / no-alias as a checked fact.** Does the borrow checker's
      disjointness of two spans reach the C backend as `restrict`, so the
      C compiler vectorizes? (Rust `&mut` → `noalias`) — Oak: the fact
      exists (`50-borrowing.md` §6 disjoint mutable regions) but the C
      backend does not emit `restrict` (it appears only in the reserved
      word list, `codegen/identifiers.go`) — gap.
- [ ] **Prefetch and non-temporal hints.** Are software prefetch and
      streaming stores expressible as effect-free hints that the lowering
      may drop? (MS, DPDK) — Oak: not stated.
- [ ] **Alignment as a precondition.** Can a function require a
      64-byte-aligned span, with the alignment a fact the caller proves
      or asserts once, so aligned loads are emitted? (direct I/O, AVX
      aligned loads, TB) — Oak: `(align: N)` on fields
      (`40-records.md`); alignment on views/spans: check.

- [ ] **Sentinel-terminated index arrays.** When a consumer walks an index
      produced by an earlier pass, is the index over-allocated by a
      constant and terminated with sentinels (`len, len, 0`) so the
      consumer needs no end check, and is the slack a stated formula
      (`roundup64(cap) + 9`)? (simdjson stage 1 → stage 2) — Oak: not
      stated; `71-codecs.md` §11 keeps structural indexes as future work.
- [ ] **Over-write into slack instead of a counted loop.** Can a compaction
      write a fixed group of outputs past the true count into declared
      slack, with the group's bound proven once per block rather than per
      store? (simdjson `write_indexes_stepped`) — Oak: the extent fact
      `i + K < len(v)` (`50-borrowing.md`) is the shape; spelling per
      block: check.
- [ ] **Constant-offset block loads discharge together.** Under
      `while at + 64 <= len(src)`, do the four loads at `at`, `at + 16`,
      `at + 32`, `at + 48` all elide their checks, and does the `len(v) -
      i >= K` spelling of a bound count as the offset fact `i + (K-1) <
      len(v)`? (simdutf 64-byte blocks, simdjson `is_made_of_eight_digits_fast`)
      — Oak: `50-borrowing.md` extent facts cover literal and scaled
      bounds; the `len - i >= K` form and `+16k` offsets: check emitted C.

### 2b. Bits and lanes

- [ ] **Bit intrinsics as total functions.** `ctz`, `clz`, `popcnt`,
      `bswap`, `rotl/rotr`, `pdep/pext`, `bit_reverse` — all present,
      total (zero input defined), and lowered to single instructions?
      (simdjson `ctz` loop, Hyperscan) — Oak: `simd.ctz_u32/u64` and
      `simd.popcount_u32/u64` (total, `ctz(0)` is the width; `93-simd.md`
      §1.2, landed 2026-09-12); `arm64.clz`, `arm64.rbit`, `arm64.rev`;
      portable `bswap`, `rotr`, `pdep`/`pext`, `bit_reverse`: not found.
- [ ] **Bitmask iteration.** Can `while mask != 0 { i = ctz(mask); mask
      &= mask - 1 }` be written in the strict profile with its bound
      recognized (popcount of the initial mask)? (simdjson stage 1) — Oak: the loop is spelled in `93-simd.md` §1.2
      and runs `popcount(m)` times (`Oak.Intrinsics.ctz_lt_of_mem_true` is
      the progress law); it is not a canonical shape of `85-discipline.md`
      §3, so it is an `OAK-D0103` obligation until the ranking law is
      recognized — open.
- [ ] **Shuffle-based table lookup.** Is a 16-entry nibble lookup
      (`pshufb`/`tbl`) a portable `simd` operation with a stated
      out-of-range lane result? (simdjson classification, simdutf, Teddy) — Oak: `simd.tbl_u8x16`
      (`93-simd.md` §1.2, landed in 3587c9b with the UTF-8 validator; NEON
      `tbl`, `pshufb`'s high-bit rule, `Oak.Simd.tbl_lane_*`).
- [ ] **Movemask / compress.** Is lane-compare-to-bitmask a portable
      operation on every target, with the emulation cost on targets
      lacking it (NEON) stated? Is lane compaction (`vcompress`,
      `pext`-based) expressible? (simdjson, Highway) — Oak: `simd.movemask_E` over the four integer
      shapes with the NEON cost stated (`93-simd.md` §1.2, landed
      2026-09-12); compress: absent.
- [ ] **Prefix operations on masks.** Prefix-XOR for quote-state tracking,
      prefix-sum for compaction indices — expressible, and lowered to
      `pclmul` where it pays? simdjson's arm64 path uses six scalar
      `x ^= x << k` steps, not `pmull`, so the scalar form is the one to
      have first. (simdjson) — Oak: expressible in safe Oak with
      constant-folded checked shifts; no `pclmul` lowering.
- [ ] **Horizontal reductions with fixed grouping.** Is `reduce_add`'s
      pairwise tree the definition, and does the lowering produce
      `vaddv`/`haddps` sequences whose grouping matches? Is there a
      portable integer horizontal add, or only the arm64 `uaddlv`?
      (F2, simdutf narrow accumulators) — Oak: `93-simd.md` §1.2a,
      `55-parallelism.md` §4; integer form only in the arm64 library.
- [ ] **Branchless select and blend.** Can `cond ? a : b` over scalars
      and lanes lower to `csel`/`bsl` without a branch, with the compiler
      free to choose? Can the author *require* branchless (constant-time)?
      (crypto, Edelkamp–Weiß) — Oak: not stated for the requirement.
- [ ] **Widening and narrowing lanes.** `u8x16 → u16x8` pairs, saturating
      narrow, zip/unzip, integer lane extract — portable and total?
      (simdutf transcoding, `vst2q` zip-with-zero) — Oak: `codegen/simd.go`
      lowers `add and eq max min or sub xor` only; `extract`/`insert`
      exist for float lanes only — gap.
- [ ] **Runtime feature dispatch.** Can one function have per-ISA-level
      bodies (NEON, SVE2, RVV, AVX2, AVX-512) selected once at startup,
      with the dispatch itself deterministic and all bodies tested against
      one oracle? (simdjson, memchr, Highway) — Oak: **absent** (dbs
      ask 6/7 recorded); design in `93-simd.md` §4 is the shape.

- [ ] **Lane shifts by immediate.** Is `shr`/`shl` by a constant on `u8`
      and `u16` lanes a portable `simd` operation, so a nibble (`x >> 4`)
      can index a 16-entry table? (simdutf `prev1.shr<4>()`, simdjson `(byte + 3) >> 4`) — Oak:
      `simd.shr_E` by a count that traps at the lane width (`93-simd.md`
      §1.2, 3587c9b); `shl`: absent.
- [ ] **Cross-vector byte shift.** Can "the last N bytes of the previous
      chunk followed by the first 16−N of this one" (`ext`/`palignr`) be
      formed in one operation rather than through a stack round trip?
      Every windowed classifier needs it. (simdutf `prev<N>`, simdjson lookup4) — Oak: `simd.prev_u8x16(prev,
      cur, n)` (`93-simd.md` §1.2, 3587c9b; NEON `ext` selected by the
      count, `Oak.Simd.prev_lane_*`).
- [ ] **Unsigned lane comparisons beyond equality.** Are `gt`/`ge` masks
      portable, or is `eq(max(a, b), a)` the stated two-op emulation with
      its cost recorded? (simdutf `gt_bits`, `is_incomplete`) — Oak:
      `93-simd.md` §1.2 has `eq`, `min`, `max`; comparison masks reserved
      for a later revision.
- [ ] **Lookup with default.** Is a table lookup whose out-of-range lanes
      take a second vector's value (`vqtbx1q`) available, or stated as
      lookup plus select? (simdjson whitespace classification) — Oak: not
      stated; depends on the table-lookup item.

### 2c. Control flow shapes

- [ ] **Threaded dispatch.** Can a state machine or interpreter loop be
      written so each state jumps directly to the next (computed goto /
      tail call) rather than through a central switch, in the strict
      profile? (LuaJIT, CPython, Hyperscan DFA) — Oak: mutual tail
      recursion lowers to a trampoline (`85-discipline.md` §2), one
      state switch per step; the backend does not emit `musttail` or
      computed goto — measure the trampoline against a threaded C DFA.
- [ ] **Loop unswitching and versioning by the author.** Can a loop be
      specialized on a runtime-constant predicate (all-ASCII, statically
      sized) with the classification once and the body twice, without
      duplicating source? (simdjson, codec classification pass) — Oak:
      `71-codecs.md` classification pass (remaining item).
- [ ] **Early exit that keeps the bound.** Can a bounded loop `break` on
      the first mismatch while keeping the strict profile's certificate?
      (every search loop) — Oak: `85-discipline.md` §3a, yes.
- [ ] **Speculation with rollback.** Can a parser speculate (parse as
      integer, fall back to float) without copying the input or violating
      "output unchanged on failure"? (simdjson number parsing) — Oak:
      two-pass codecs (`71-codecs.md` §7); a speculative form: check.
- [ ] **Unrolling with proof.** Can an author unroll by four with the
      remainder handled and the bound still recognized, or must the
      compiler be trusted? (every kernel) — Oak: check whether `i = i +
      4` with bound `n - 3` is a canonical shape.
- [ ] **Cold paths out of line.** Can error and slow paths be marked cold
      so the hot loop stays in the instruction cache? (`__builtin_expect`,
      Rust `#[cold]`) — Oak: not stated.

### 2d. Data layout shapes

- [ ] **Struct-of-arrays as a derived layout.** Can a record type be
      stored as parallel arrays with one declaration, the field access
      syntax unchanged, and the layout a representation choice?
      (DOD, Zig `MultiArrayList`, Mojo, Jai) — Oak:
      `45-representations.md` §7.1 names AoS, SoA, and AoSoA as explicit
      collection representations; only AoS is implemented.
- [ ] **Field reordering by the compiler vs. by the author.** Is field
      order semantic (serialization, FFI) or may the representation layer
      reorder to remove padding, and is the choice per type? (Rust
      default reorder vs `repr(C)`) — Oak: `40-records.md` order/layout
      separation.
- [ ] **Hot/cold splitting.** Can a record's rarely-touched fields be
      moved to a side table without changing call sites? (DOD) — Oak:
      representation axis; not stated as a mechanism.
- [ ] **Wire records as typed views over bytes, with wide scalars.** Can
      a 256-byte header be declared padding-free with `u128` checksum and
      id fields at 16- and 32-byte alignment, its layout asserted at
      compile time, and read as a borrowed record view at an offset into
      a `[]u8` after its checksum is verified? (TB `message_header.zig`
      `extern struct`, `stdx.no_padding`) — Oak: `struct(packed)`,
      `static_assert(size_of/offset_of)` (`40-records.md` §6a–§6b), C
      header asserts (`92-ffi.md` §2.6); `u128` (`20-types.md` §11, 16
      bytes at 16) but no `u256`; `struct(no_padding)` (`40-records.md`
      §6a) is the padding-free claim; record views only for JSON-derived
      fields (`71-codecs.md` §13a); the
      fixed-layout binary codec is wanted (dbs note round 3 ask 9) —
      gap, class (a).
- [ ] **Bounded arrays and busy-bitset pools.** Can a fixed array carry
      its count as a refinement bounded by its capacity, and a pool hand
      out slots by index with acquire returning "none" when full? (TB
      `BoundedArrayType`, `IOPSType`) — Oak: `count: u32 where value <=
      N` (`20-types.md` §12) can carry the bound, `stdlib/slab.oak` is
      the generational form; `Ring`/`BitSet` planned
      (`standard-library-design.md`); pointer-to-index recovery is (b) by
      design — handles replace it.
- [ ] **Niche and tag compression.** Does `Option[View]` cost zero extra
      bytes (null niche), does a tag share storage with padding or an
      unused range, and is the optimization proof-preserving? (Rust
      niche optimization) — Oak: `45-representations.md` lists niche/tag
      elision as a representation; `05-ergonomics-and-cost.md` permits it
      when proof-preserving; what is implemented: check `Option` layout.
- [ ] **Packed and bitfield layouts.** Can hardware tables (page table
      entries, descriptors, register images) be declared with exact bit
      positions, with reads and writes lowering to shifts and masks and
      the layout asserted? (os, MISRA bitfield warnings) — Oak:
      `os-structures-survey.md` §3, §6; `97-aarch64-system-registers.md`.
- [ ] **Intrusive links.** Can a node live in two lists at once via
      embedded links without a wrapper allocation, with ownership of the
      node clear? (Linux `list_head`, TB, os) — Oak:
      `os-structures-survey.md` §2 pools plus index links;
      `standard-library-design.md` §7.
- [ ] **Tagged pointers and pointer authentication.** Can spare pointer
      bits carry a tag, with the untagging total and PAC on Apple Silicon
      respected? (LuaJIT NaN boxing, ARM PAC) — Oak:
      `standard-library-design.md` §10.
- [ ] **Cache-line placement and padding.** Can a field or a static be
      aligned to a cache line, padded to avoid false sharing, and placed
      in a named section, with the emitted offsets asserted? (MS, TB) —
      Oak: `(align: 64)` (`40-records.md`), placement of statics
      (`65-machine-memory.md`).
- [ ] **Compile-time table generation.** Can lookup tables (CRC, UTF-8
      classes, DFA transitions, powers of ten) be computed at compile
      time from a definition and placed in read-only storage, so the
      table and its generator cannot drift? (Zig comptime, Mojo
      parameters, Rust const eval) — Oak: static initializers
      (`60-effects-allocation.md` §10a); const evaluation breadth: check.

### 2e. Allocation and ownership shapes

- [ ] **Bump allocation with bulk free.** Is an arena a type whose
      allocate is a pointer bump and whose free is a reset, with every
      borrow from it bounded by the arena's region? (Zig, Odin
      `context.allocator`, Cyclone) — Oak: `60-effects-allocation.md`
      §6.
- [ ] **Caller-provided storage everywhere.** Does every stdlib function
      that produces data write into a caller span rather than allocate,
      with the required size computable up front? (Zig std, TB) — Oak:
      `60-effects-allocation.md` §9; audit stdlib.
- [ ] **Zero-copy views through every layer.** Can a decoded frame,
      string token, or record field be handed back as a view into the
      input across function and package boundaries, with the region
      carried in the type? (Cap'n Proto, dbs frame scan) — Oak:
      `50-borrowing.md` §8c, `71-codecs.md` §13a.
- [ ] **Views inside records that cross calls.** Can a cursor or a frame
      record hold a view and travel through calls with its region?
      More than one region per record? (Rust structs with lifetimes) —
      Oak: `50-borrowing.md` §8c increment 4; multi-region open.
- [ ] **Move semantics without copies.** Does returning a record, union,
      or owned array by value lower to no copy (return slot / RVO), and
      is a consumed parameter's storage reused? (Rust, C++ RVO) — Oak:
      `90-backend.md` §10 values at boundaries; check the emitted C.
- [ ] **Closures without heap.** Can a lambda passed to a known
      combinator specialize away to a direct call with its captures on
      the caller's stack? (Rust, Swift non-escaping) — Oak:
      `05-ergonomics-and-cost.md` Function values and closures,
      `55-parallelism.md` §7.

- [ ] **Worst-case scratch from a closed form.** Is every parser scratch
      buffer (index, tape, string buffer, depth arrays) sized by a formula
      over input length and depth, allocated once, and never touched again
      on the steady-state path? (simdjson `document::allocate`: tape
      `cap + 3`, strings `5·(cap/3) + PADDING`) — Oak: `71-codecs.md` §16
      names reusable bounded work buffers as an investigation item; no
      formula stated.

### 2f. Machine-level access

- [ ] **Inline assembly units beside sources.** Can a routine be written
      in typed abstract assembly when the compiler cannot reach the
      golden code, with register types checked and the unit's contract
      stated? (Zig, Rust `asm!`) — Oak: `94-assembler.md`.
- [ ] **Hardware instructions as typed functions.** CRC32, AES, SHA,
      PMULL, dot-product, `fcvtzs` rounding modes, atomics variants —
      exposed per architecture with total semantics? (Zig
      `@intrinsic`-style, Rust `core::arch`) — Oak: `93-simd.md` §2
      arm64 functions; hash hardware in `sam/stdlib-hash-hw`.
- [ ] **Performance counters reachable.** Can a benchmark read cycle
      and instruction counters in-process on the targets Oak supports
      (Apple Silicon `kperf`, Linux `perf_event`)? (simdjson's counters)
      — Oak: not stated.

## 3. Know the machine

- [ ] **Napkin math before design.** Has the back-of-envelope been done —
      bytes moved, cache lines touched, branches per element, syscalls per
      operation — and does the design's shape follow from it? Latency
      numbers every engineer should know, per target. (TB, Jeff Dean) —
      Oak: practice; record in the note for each pass.
- [ ] **Memory-bound or compute-bound?** Is it known which, by a roofline
      estimate (arithmetic intensity against bandwidth and peak), so
      effort goes to the binding constraint? (Williams et al. roofline,
      MS) — Oak: `BENCHMARKS.md` workload shapes.
- [ ] **Cache line size is not 64 everywhere.** Apple Silicon has 128-byte
      lines; is padding and alignment a per-target constant, not a
      literal? (MS) — Oak: `(align: 64)` today; a target constant is the
      fact.
- [ ] **Sequential over random.** Does every hot path walk memory
      sequentially or with a fixed stride the prefetcher can follow, with
      pointer chasing confined to cold paths? (DOD, MS) — Oak: handles
      and indices over pointers (`60-effects-allocation.md` §8).
- [ ] **Branch predictability.** Are data-dependent branches in inner
      loops replaced by masks, tables, or sorting the input; are the
      remaining branches overwhelmingly one-sided? (simdjson, MS) — Oak:
      §2b branchless select.
- [ ] **Instruction cache and code size.** Does monomorphization or
      unrolling blow the hot loop past the instruction cache or the
      decoded-µop cache? Is code size measured per benchmark? (Rust
      monomorphization bloat, Go's restraint) — Oak:
      `05-ergonomics-and-cost.md` acknowledges the trade; measure.
- [ ] **TLB and huge pages.** Do large working sets use large pages, and
      are allocations aligned to them? (MS, databases) — Oak: not stated;
      allocator design item.
- [ ] **Memory-level parallelism.** Do independent loads issue together
      (multiple accumulators, unrolled independent chains) rather than
      serialize on one dependency chain? (MS, hash table probing) — Oak:
      author-level; §2c unrolling.
- [ ] **Store forwarding and false sharing.** Are producer and consumer
      indices on separate lines; are small stores followed by wider loads
      of the same bytes avoided? (Disruptor, MS) — Oak: `(align: 64)`.
- [ ] **NUMA and core affinity.** Where multiple cores are used, is
      memory allocated near the core that uses it and are threads pinned?
      (MS, DPDK) — Oak: not stated; out of scope until a scheduler exists.
- [ ] **Unified memory on Apple Silicon.** Does the host↔device story
      avoid copies where memory is shared, with custody the only
      transition cost? (mlx) — Oak: `Buffer[T, S]` custody, `92-ffi.md`
      §2.8.5.
- [ ] **Syscall and context-switch counts.** Are syscalls batched
      (completion rings, `writev`, batched fsync), and is the count per
      operation measured? (io_uring, TB) — Oak: `120-io.md` rings.

## 4. Data-oriented design

- [ ] **Design for the common case's data, not the object.** Are
      transformations written over arrays of the data they touch, rather
      than methods over objects that carry data they do not? (Acton, DOD)
      — Oak: culture; §2d SoA.
- [ ] **Existence-based processing.** Is "which state is this in" encoded
      by which array an item sits in, so processing a state is a loop
      with no branch? (Fabian, DOD) — Oak: typestate plus pools.
- [ ] **Smallest sufficient index type.** Are indices `u32` (or smaller)
      when the capacity allows, halving memory traffic versus pointers?
      (TB, DOD) — Oak: handles as typed indices.
- [ ] **Batch everything.** Does every operation accept a batch so
      per-call overhead (syscall, lock, dispatch, bounds check) is
      amortized? Is the batch size bounded and part of the type? (TB) —
      Oak: `120-io.md`; audit stdlib APIs for batch forms.
- [ ] **Separate hot and cold data.** Are rarely-read fields out of the
      cache lines the hot loop touches? (DOD) — Oak: §2d hot/cold.
- [ ] **Bitsets over arrays of bool.** (DOD, os bitmaps) — Oak:
      `standard-library-design.md` BitSet.
- [ ] **Generation-stamped handles over reference counting.** Does
      lifetime management cost an integer compare, not an atomic
      increment on every share? (DOD, TB) — Oak:
      `60-effects-allocation.md` §8; `05-ergonomics-and-cost.md` no
      mandatory refcounting.

## 5. Algorithms and data structures

- [ ] **Best-known algorithm named.** For each stdlib routine, is the
      chosen algorithm the state of the art for its constraints, with the
      citation in the source? (pdqsort, Swiss table, BLAKE3) — Oak: §1
      table; audit `stdlib/`.
- [ ] **Power-of-two capacities and masks.** Do rings and tables use
      `& (cap - 1)` with the power-of-two fact proven at the type? (every
      ring) — Oak: `Ring[T, N]` const parameter; the power-of-two
      refinement: check.
- [ ] **Open addressing over chaining; B-trees over binary trees; arrays
      over linked lists.** Is the cache-friendly structure the default,
      with the alternative justified? (DOD, MS) — Oak:
      `standard-library-design.md`.
- [ ] **Hash function fit for purpose.** Is the fast hash (wyhash/xxh3)
      used for tables and a keyed hash (SipHash) where keys are
      attacker-chosen, with seeding? (Rust `HashMap` default,
      collision-DoS history) — Oak: `stdlib/hash.oak` has SHA-256, BLAKE3,
      CRC-32C; no fast table hash and no seeded hash — gap once a hash
      table exists.
- [ ] **Radix and counting sorts for fixed-width keys.** (ips4o, TB) —
      Oak: not stated.
- [ ] **Amortized structures declare their worst case.** Does any
      "amortized O(1)" hide a pause the realtime profile forbids? (TB) —
      Oak: `60-effects-allocation.md` §12.

## 6. SIMD and vectorization

- [ ] **Data-parallel structure first, instructions second.** Is the
      algorithm reshaped so independent items are processed together
      (block classification, multi-accumulator), before any intrinsic is
      chosen? (simdjson's stage 1, Futhark) — Oak: `93-simd.md` §3
      program shape.
- [ ] **Autovectorizable loop shape.** Countable trip, no early exit
      unless via mask, no aliasing, no cross-iteration dependency other
      than a declared reduction — and a test asserting vectorization
      happened? (LLVM loop vectorizer rules) — Oak: §0 assert emitted
      code.
- [ ] **Portable vector types with per-target lowering stated.** Is each
      `simd` operation's lowering on NEON, SVE, RVV, AVX2 documented,
      including which are emulated and at what cost? (Highway) — Oak:
      `93-simd.md` §1.4.
- [ ] **Scalar tail policy chosen per algorithm.** Predicated zero-fill
      where the semantics permit, overlapping last-block otherwise,
      scalar loop as the last resort — and the choice stated. (ml,
      simdutf) — Oak: `93-simd.md` §4.1; codec note "what does not
      transfer".
- [ ] **Fusion of independent lanes.** Two accumulators over one load
      (structure and UTF-8 validity) rather than two passes? (simdjson,
      codec fused validation lane) — Oak: `71-codecs.md` §4a.
- [ ] **Vector float order is semantics.** Lane and run counts named,
      results bit-reproducible across widths? (ml, F2) — Oak:
      `93-simd.md` §1.2a, `56-kernels.md` §4.
- [ ] **No gathers where a shuffle will do.** (MS) — author-level.
- [ ] **Cross-target verification.** Is each vector lowering checked
      against the portable definition on every target (differential, or
      Sail for the ISA)? — Oak: `93-simd.md` §5, `spec/sail`.

- [ ] **Software-pipeline the block loop.** Does the block loop emit the
      previous block's results while the current block's masks are
      computing, so the serial mask-to-index tail overlaps the next loads?
      (simdjson `step<128>`, "PERF NOTES") — Oak: not stated; `93-simd.md`
      §3 shows one block per iteration.
- [ ] **Copy-the-tail tail policy.** When the block kernel must not
      over-read and predication is unavailable, is the remainder copied
      into a stack block pre-filled with a semantically inert byte
      (simdutf: 0x20, so a dangling lead reads as too short) and run
      through the *same* block code, so tail and body cannot diverge?
      (simdutf `buf_block_reader::get_remainder`, simdjson last block) —
      Oak: `93-simd.md` §4.1 names predication, overlap, and scalar tail
      only; `stdlib/json.oak` and `stdlib/strings.oak` use scalar tails.
- [ ] **Reject fast, locate slow.** Does the vector validator accumulate
      errors in lanes and decide once per block, with the error position
      and class produced by the scalar oracle re-run from the last
      known-good block (rewinding at most three continuation bytes), and
      is the "detected one block late" case tested? (simdutf `rewind_and_validate_with_errors`, `puzzler2`) — Oak:
      `utf8.locate` (`93-simd.md` §1.5, landed 2026-09-12): per-step
      rejection, then `strings.utf8_first_error_at` from a boundary three
      bytes back; the lead-at-63 and continuation-at-64 cases are in the
      differential test.
- [ ] **Structure mask indexes a generated shuffle table.** For
      transcoding, is the per-block continuation bitmask the index into a
      generated (shuffle, consumed) table over ≤12-bit patterns, with the
      most frequent patterns branch-tested first, and does the writer stay
      memory-safe when the mask came from invalid bytes? (simdutf
      `utf8bigindex[4096][2]`, `shufutf8[209][16]`, issue #514) — Oak:
      `stdlib/strings.oak` transcodes one scalar at a time — not started.
- [ ] **Speculative writer, validated after.** May the transcoder write a
      block's output before the block's validity is known, provided the
      write is bounds-safe on garbage and the output is pre-sized so
      failure leaves the contract intact? (simdutf `validating_transcoder`)
      — Oak: `71-codecs.md` §7 unchanged-on-failure requires pre-sizing;
      a fact relating remaining input to remaining output: not stated.

## 7. Parallelism and concurrency

- [ ] **Work and span stated.** Does every parallel operation document
      total work and critical path, and is the sequential lowering the
      default? (Blelloch, `55-parallelism.md`) — Oak:
      `05-ergonomics-and-cost.md` Explicit parallel cost.
- [ ] **No hidden scheduler.** Is any thread pool, task queue, or
      allocation a parallel operation needs part of its declared contract?
      (constitution) — Oak: `55-parallelism.md`.
- [ ] **Single-threaded core, parallel edges.** Does the design keep the
      state machine single-threaded and push parallelism to I/O and
      stateless stages? (TB, Redis, LMAX) — Oak: `120-io.md` model.
- [ ] **Sharding over locking.** Per-core or per-shard ownership with
      message passing, before any lock? (DOD, TB) — Oak: §2e ownership.
- [ ] **Lock-free only when measured.** Is a lock-free structure adopted
      because a benchmark showed the lock was contended, and is its memory
      ordering proven? (Preshing, correctness §7) — Oak:
      `66-memory-model.md`.
- [ ] **Amdahl checked.** Is the serial fraction measured before adding
      cores? — practice.
- [ ] **GPU: occupancy, threadgroup memory, coalesced access.** Are
      kernel launches sized to the device, tiles staged through
      threadgroup memory, and global accesses coalesced? Is the launch
      descriptor a checked artifact? (mlx, CUTLASS) — Oak:
      `56-kernels.md` §5; threadgroup memory open.

## 8. I/O and storage

- [ ] **Batch and coalesce.** Writes coalesced, fsyncs batched, reads
      grouped into one submission? (TB, io_uring) — Oak: `120-io.md`.
- [ ] **Direct I/O with aligned buffers.** Are block buffers
      sector-aligned and sized so the kernel page cache is bypassed
      deliberately, with alignment a type fact? Is the sector size a
      named constant, every file size and I/O offset asserted a multiple,
      alignment carried in the buffer's type, Direct I/O a tri-state
      (required, optional, disabled) with a filesystem probe, and `pread`
      size capped by the OS limit constant? (TB `io/linux.zig`,
      databases) — Oak: `120-io.md` §3 `open_direct`, `io_sector_bytes`,
      the sector rule decided before any call, `IoSectorRegion` aligned
      storage; alignment is checked at registration, not carried as a
      static fact on the span — gap narrowed; tri-state is the program's
      policy.
- [ ] **Zero-copy from device to consumer.** Does data cross layers as
      views into the receive buffer, never re-copied for convenience?
      (dbs, DPDK) — Oak: `71-codecs.md` §13a.
- [ ] **Checksums where the hardware helps.** CRC-32C via hardware,
      computed once per block, verified on every read? (TB) — Oak:
      `stdlib/hash.oak`, `sam/stdlib-hash-hw`.
- [ ] **Bounded queues everywhere.** Backpressure by capacity, never
      unbounded buffering? (TB, Reactive Streams) — Oak: rings with
      declared capacity.
- [ ] **Simulated and native I/O agree on cost shape.** Does the
      simulation model the *latency and batching* the native path has —
      minimum plus exponential(mean) per operation, per-path clogging,
      capacity drop — so a design validated in sim is not slow in
      native? (TB VOPR `packet_simulator.zig`) — Oak: `120-io.md` two
      realizations differ only in fault model; `SimSched` delays are
      uniform — cost model: check.

## 9. Compilers, fusion, and specialization

- [ ] **Specialize by default; dispatch by choice.** Do generics
      monomorphize to direct calls, with dynamic dispatch never introduced
      silently? (Rust, Zig, Mojo) — Oak: `05-ergonomics-and-cost.md`
      Generics specialize by default.
- [ ] **Fusion by boundaries, not by search.** Are fusion decisions
      structural (what is a boundary) rather than a search over a schedule
      IR, and is every fusion licensed by one theorem and checked by an
      oracle? (ml, tinygrad's lazy graph, Halide's explicit schedule as
      the contrast) — Oak: codec-fusion note; `55-parallelism.md` §6.
- [ ] **Recompute versus materialize decided by a stated limit.** (ml
      `RECOMPUTE_LIMIT`, tinygrad) — Oak: codec-fusion note.
- [ ] **Carry, do not fuse, across contract boundaries.** Where a
      contract (output unchanged on failure) needs two passes, is the
      first pass's result carried in registers rather than the passes
      merged? (codec note) — Oak: `71-codecs.md` §7.
- [ ] **Classify then emit.** Do structural predicates over the type pick
      an emitter (statically sized, all-ASCII keys, tile shape), rather
      than a general IR trying to discover the shape? (ml, codec
      classification) — Oak: `71-codecs.md` classification pass
      (remaining item).
- [ ] **Kernel identity by structure hash.** Are identical kernels or
      derived codecs emitted once? (ml, tinygrad) — Oak: monomorphization
      at compile time; check dedup of derived helpers.
- [ ] **Declared laws are the only permission to reorder.** Does a backend
      regroup a reduction or reassociate only under `laws { associative,
      commutative }`, and is there a backend that consumes them yet?
      (F3, Futhark's `reduce` requiring associativity) — Oak:
      `10-syntax.md` §14a; consumer open.
- [ ] **Higher-order specialization.** Does a lambda passed to a known
      combinator inline, leaving no indirect call, closure object, or heap
      environment? (Rust iterators, Futhark) — Oak: `55-parallelism.md`
      §7.
- [ ] **Flattening for nested parallelism.** Where nested data parallelism
      appears, is Futhark's incremental flattening the model, with the
      choice of version by runtime size? (Futhark) — Oak: not stated;
      kernels are flat today.
- [ ] **Tiles as gated constants.** Are tile sizes hand-picked constants
      gated by structural pattern matches and measured thresholds, with
      the measurement checked in? (ml, BLIS) — Oak: codec-fusion note.
- [ ] **Compile-time parameters over runtime flags.** Are width, tile,
      and shape parameters const generics resolved at instantiation, so
      the inner loop has no runtime `if`? (Mojo, Zig comptime, Futhark
      size types) — Oak: `20-types.md` §11.0.
- [ ] **Check elision from discharged facts.** Does every bounds, tag, or
      alignment check the checker has discharged actually disappear from
      the emitted code, and is that asserted? (Rust/LLVM range analysis,
      Idris erasure) — Oak: `56-kernels.md` §3 open; §0 assert emitted
      code.
- [ ] **Erasure of phantoms is verified.** Do phantom parameters,
      typestates, and regions cost zero bytes and zero instructions, with
      a Lean statement and an emitted-code check? (Idris erasure, Rust
      `PhantomData`) — Oak: `Oak.PhantomRepresentation`; `71-codecs.md`
      §4 Zero cost, defined.
- [ ] **Tail calls guaranteed, not hoped.** Are tail calls lowered by Oak
      to loops or trampolines rather than trusting the C compiler?
      (Zig `@call(.always_tail)`, Scheme) — Oak: `85-discipline.md` §2.
- [ ] **Inlining under control.** Can the author require or forbid
      inlining at a call, and does the C backend emit the corresponding
      attribute? (Zig `inline`/`noinline`, Rust) — Oak: the backend
      marks private leaf helpers `OAK_INLINE` (`always_inline`,
      `codegen/codegen.go`); no author-level control, no `noinline`.
- [ ] **The C backend is a real backend.** Are `restrict`, `__builtin_*`,
      alignment attributes, `musttail`, `cold`, vector extensions and
      `-ffast-math`-free flags emitted so the C compiler is helped, not
      fought? Is a native backend (AArch64, rv64) on the roadmap where C
      cannot express the lowering? (Zig's move off LLVM as the contrast)
      — Oak: `90-backend.md`, `feat(nativegen)`, rv64 planned (dbs ask 6).
- [ ] **Profile-guided and link-time optimization measured.** Does the
      benchmark harness build with LTO and PGO where the C toolchain
      supports them, and is the gain recorded? — Oak: not stated.

- [ ] **Consumer chains monomorphize to one loop.** Can a
      redact→convert→sum pipeline over one parse be written as composed
      sink types and lower to a single pass with no sink object, as a
      visitor chain does with virtual calls? (weePickle/uPickle "Chaining
      Visitors") — Oak: `71-codecs.md` §3 `stream[F, S]`, §11 fusion is
      design work; needs a method-set constraint for `S`.

## 10. Parsing and text

- [ ] **Two stages, one pass each.** Structural indexing first, then
      typed consumption over the index, neither backtracking? (simdjson)
      — Oak: `71-codecs.md` §11, §16.
- [ ] **On-demand over materialized.** Can a consumer decode only the
      fields it reads, skipping the rest by structural index? (simdjson
      On-Demand, Cap'n Proto) — Oak: not modeled; direction.
- [ ] **Number parsing state of the art.** Eisel–Lemire for floats, SWAR
      for eight digits at a time, Clinger's fast path, with correctness
      against the exact decimal? (fast_float, simdjson) — Oak:
      `71-codecs.md` §18–§19 have the SWAR integer scan; `stdlib/float.oak`
      is the exact slow path only, derived codecs do not decode floats,
      and there is no `mul_hi` 64×64→128 — the fast path is absent.
- [ ] **DFA with byte-class compression for matching.** Small
      transition tables, one load per byte, no branches? (Hyperscan, RE2)
      — Oak: UTF-8 state machines in `stdlib/strings.oak`; regex not
      started.
- [ ] **SIMD prefilter before the exact matcher.** Literal fragments
      found with Teddy/shift-or, exact engine run only on candidates?
      (Hyperscan) — Oak: not started.
- [ ] **ASCII fast path.** Is the all-ASCII block detected with one
      OR-reduce and handled without the multibyte machinery? (simdutf) —
      Oak: `71-codecs.md` §4a fused lane.
- [ ] **Grapheme, normalization, case tables generated, not hand-written.**
      (Unicode) — Oak: `sam/stdlib-grapheme`, `sam/stdlib-normalize`,
      `sam/unicode-generator-pub`.

- [ ] **Match keys on raw bytes, fall back on escapes.** Are object keys
      compared against the expected spelling byte for byte (quotes
      included, length checked), with Unicode-scalar comparison reached
      only when the raw bytes contain a backslash or non-ASCII? (simdjson
      `find_field_raw`) — Oak: `71-codecs.md` §18, `stdlib/json.oak`
      `json_key_equal`.
- [ ] **Key dispatch by length then prefix.** Does derived field matching
      switch on key length and compare shared prefixes once (a radix
      tree), with the length fact discharging the compare's bounds, rather
      than a linear list of full compares? (weePickle
      `getKeyIndexUsingRadix`, 20–60%) — Oak: `71-codecs.md` §13, §18
      linear dispatch; §16 lists schema-specialized matching as open.
- [ ] **Parse to the requested type, never through a type switch.** Does
      the consumer name the type first so the scalar parser is the one for
      that type, with "wrong type" a recoverable result rather than a fatal
      error? (simdjson On-Demand use-specific parsing) — Oak:
      `71-codecs.md` §13 `TypeMismatch`, §17.
- [ ] **Skip is as cheap as parse.** Is skipping an unwanted subtree a
      structural scan with no value materialization and a declared depth
      bound? (simdjson `skip_child`, weePickle `NoOpVisitor`) — Oak: no
      skip primitive in `stdlib/json.oak` — not stated.
- [ ] **Sizing is a non-validating count.** Once validity is established,
      are output-size functions O(n) lane counts (non-continuation bytes,
      bytes ≥ 0xF0, `min(x & 0xFF80, 1)` for UTF-16) with narrow
      accumulators flushed before overflow, rather than a second decode?
      (simdutf `*_length_from_*_bytemask`) — Oak: `stdlib/strings.oak`
      `utf8_to_utf16_size` decodes every scalar and `utf8_to_utf16`
      decodes again — three passes.

## 11. Numerics

- [ ] **Integer division by constants becomes multiply-shift.** Does the
      lowering (or the C compiler) do this, and is it checked? (Hacker's
      Delight, Lemire fastmod) — Oak: check emitted code.
- [ ] **FMA available and explicit.** Is fused multiply-add a named
      operation the author chooses, never contracted silently? (IEEE,
      correctness §6) — Oak: `56-kernels.md` §4.
- [ ] **Denormal cost known.** Do kernels that may produce denormals
      state whether flush-to-zero is on, and measure the cliff? (DSP,
      mlx) — Oak: `56-kernels.md` §4.
- [ ] **Checked arithmetic cost measured.** Is the overhead of
      `checked_add` over `+` measured and is the checked form used only
      where the value is externally influenced? (Rust overflow-checks
      debate, TB) — Oak: `20-types.md` §11.1a; measure.
- [ ] **Mixed-width avoided in hot loops.** (MS) — Oak: rejected by the
      type system (no implicit promotion).
- [ ] **Wide multiply is a total operation.** Is a 64×64→128 multiply
      (high and low halves) available as a builtin, since Eisel–Lemire
      float parsing, fast modular reduction, and wide hashes all need it?
      (simdjson `full_multiplication`, Lemire fastmod, wyhash) — Oak: no
      `mul_hi_u64` or `u128` in `stdlib` or `20-types.md` — gap.

## 12. Measurement discipline

- [ ] **Benchmarks in tree, versus named competitors, on named hardware.**
      Go, Rust, Zig, simdjson, simdutf, with versions and the machine
      recorded in the results. — Oak: `BENCHMARKS.md`, `benchmarks/`.
- [ ] **Throughput per byte or per element, not wall time alone.**
      Cycles per byte, GB/s, ns per operation, with input size and shape.
      (simdjson) — Oak: `BENCHMARKS.md` workload shapes.
- [ ] **Min and median, never mean; repetitions and warm/cold stated.**
      (benchmark hygiene) — Oak: the `run.py` harnesses report medians;
      warm/cold and repetition counts: check per harness.
- [ ] **Hardware counters, not guesses.** Instructions, cycles, branch
      misses, cache misses per run, so the cause of a gap is measured.
      (simdjson's `event_counter`, `perf stat`) — Oak: §2f counters not
      stated.
- [ ] **Regression gate.** Does CI fail a benchmark that regresses against
      the checked-in baseline, with a rule that tolerates noise — simdjson's
      `perfdiff` runs seven interleaved samples and fails only when the
      new maximum is below the reference minimum? — Oak:
      `benchmarks/json/compare.py` does paired runs but is explicitly not
      a gate.
- [ ] **Adversarial inputs benchmarked too.** Worst-case inputs (deep
      nesting, all-escapes, hash collisions) measured alongside typical
      ones, so bounded work per byte is a number. (Hyperscan, langsec) —
      Oak: check `benchmarks/json`.
- [ ] **Code size and compile time tracked.** Monomorphization and
      derived codecs measured in bytes and seconds, not only in speed.
      (Rust, Go) — Oak: not stated.
- [ ] **Every optimization ships with its oracle and its counter.** The
      slow path stays, the fast path proves it fired, and the benchmark
      shows the delta — all in one change. (ml, simdjson) — Oak:
      `71-codecs.md` §4a; codec-fusion note "the part to do first".
- [ ] **The gap has a cause.** Each remaining ratio against the golden
      implementation in §1 is attributed to a specific §2 item or accepted
      with a stated reason. An unattributed gap is an open finding.

- [ ] **Setup outside the timed region, stated.** Does the harness exclude
      allocation, first touch, and padding copies from the timed region
      and say so, with a second number that includes them? (simdjson
      `doc/performance.md`) — Oak: `benchmarks/json/README.md` keeps setup
      outside timing; allocation counts unknown.
- [ ] **Per-script corpora and a noise margin.** Are text benchmarks run
      per writing system (ASCII, Latin-1, Arabic, CJK, emoji), since the
      byte mix decides the path taken, and does the harness print best of
      N with `mean/best − 1` as a noise figure and warn above a threshold?
      (simdutf `unicode_lipsum`, `benchmark_base.cpp`) — Oak:
      `benchmarks/state-machines` uses one random mix, best of five.

