# Note: what simdjson, simdutf, and weePickle teach the codecs and text libraries

**Status: record of a pass.** 2026-09-12, `specification` branch. Method:
`docs/checklists/README.md`, applied as three parallel reads of the
sources against `71-codecs.md`, `70-strings.md`, `93-simd.md`,
`stdlib/json.oak`, `stdlib/strings.oak`, `codegen/simd.go`, and the
benchmarks. Sources: simdjson `master` (stage 1 and stage 2 generic
kernels, arm64 `simd.h`, `numberparsing.h`, On-Demand, `padded_string`,
`implementation.cpp`, `fuzz/`, `benchmark/`), the 2019 and 2023 papers;
simdutf `master` (lookup4 validator, the UTF-8→UTF-16 transcoder and its
generated tables, `implementation.cpp`, `tests/`, `fuzz/`, workflows,
`benchmark_base.cpp`), the 2020, 2021, and 2022 papers; weePickle v1.9.1
(`weepickle-core`, the Scala 2 and 3 macros, `weejson-jackson`,
`weepack`, `differences.md`), Li Haoyi's visitor write-up, jackson-core
2.15 `StreamReadConstraints` and `ByteQuadsCanonicalizer`.

The checklists absorbed the techniques: 22 new items in
`performance.md` and 29 in `correctness.md`, with pointer corrections
where the reads found something sharper. This note records what the pass
found about *Oak*, in the order the evidence suggests acting.

## The measured gap and what closes it

| Workload | Oak | Golden | Ratio |
| --- | ---: | ---: | ---: |
| UTF-8 validation, 1 MiB random mix (`benchmarks/state-machines`) | 1.97 GB/s shift-DFA | simdutf 13.4 GB/s | 6.8× |
| Typed JSON decode, one schema, M1 (`benchmarks/json`) | 119.9 ns/doc | simdjson On-Demand 105.9 ns/doc | 1.13× |
| Same, EPYC 7763 | 178.7 ns/doc | 127.6 ns/doc | 1.40× |

The UTF-8 gap is not an algorithm gap. The lookup4 validator is
expressible in safe Oak — error lanes OR-accumulated per block, the tail
copied into an inert-filled stack block, no over-read, no `unsafe` —
except for three `simd` operations the portable catalog lacks. Every
other technique in simdutf's validator (ASCII test by `max < 0x80`,
saturating compares via `eq(max(a,b),a)`, wrapping arithmetic) is
already expressible.

## Expressiveness findings, ordered

Classification per `performance.md` §0: (a) missing operation, (b)
unsafe-only, (c) unproven precondition leaves a check, (d) lowering loss,
(e) relies on undefined behavior.

| # | Finding | Class | The fact or operation that closes it | Unlocks |
| --- | --- | --- | --- | --- |
| 1 | No 16-lane table lookup (`tbl`/`pshufb`) in `93-simd.md` | (a) | `simd.lookup16_u8x16(table, idx)`, total, with one stated out-of-range rule proven on both NEON (index ≥ 16 → 0) and SSE (bit 7 → 0) lowerings; a lookup-with-default form (`vqtbx1q`) or lookup plus select | lookup4 UTF-8 validation, simdjson byte classification, Teddy prefilters, base64 classification |
| 2 | No lane shift by immediate | (a) | `shr_u8x16`/`shl_u8x16` by constant, total | nibble extraction for #1 |
| 3 | No cross-vector byte shift (`ext`/`palignr`) | (a) | `simd.ext_u8x16(prev, cur, N)`; emulable today through a `[32]u8` store and reload | the previous-block window in every carried classifier |
| 4 | No movemask, no compress | (a) | `bitmask_u8x16 → u16` (NEON: AND with a bit table plus three `vpaddq` folds — state the cost), `compress` where the ISA has it | simdjson structural masks, simdutf structure masks and UTF-16 validation, base64 whitespace removal |
| 5 | `ctz`, `popcount`, `rbit`, `bswap`, `rotr` not builtins (only `clz32`/`clz64`; `rotl64` hand-written in `stdlib/random.oak`) | (a) | total functions with `ctz(0) = 64`; simdjson calls `ctz(0)` under a sanitizer suppression — Oak defines it instead | bitmask-to-index loops, error positions from mismatch masks |
| 6 | `while bits != 0 { i = ctz(bits); bits &= bits - 1 }` is not a canonical bounded shape | (c) | the ranking law `iterations ≤ popcount(bits) ≤ 64` for `Oak.Loops`, recognized by the discipline analysis | the same loops in the strict profile |
| 7 | Integer lane extract, narrow, zip, and a portable integer horizontal add are absent (`extract`/`insert` are float-only; `uaddlv` is arm64-only) | (a) | integer forms in the portable catalog | simdutf transcoding, narrow-accumulator counts |
| 8 | No 64×64→128 multiply | (a) | `mul_hi_u64` builtin | Eisel–Lemire float parsing (`stdlib/float.oak` is the exact slow path only; derived codecs do not decode floats), fastmod, wide hashes |
| 9 | Extent facts cover `i + K < len(v)` but not the `len(v) - i >= K` spelling, and constant-offset block loads (`at + 16k` under `at + 64 <= len`) may each keep a check | (c) | recognize the subtraction form as the offset fact; assert the emitted C for the four-load block | check-free 64-byte blocks, the eight-digit SWAR guard in `stdlib/json.oak` |
| 10 | Static-table value ranges cannot be stated (`shufutf8[utf8bigindex[m][0]]` needs "every entry < 209") | (c) | a refinement on the element type of a static initializer, checked at initialization | mask-indexed shuffle transcoding |
| 11 | The `_valid` API level exists as a type (`string`, `Bytes[ValidUtf8]`) but no stdlib function consumes it: every `text_*` in `stdlib/strings.oak` takes `[]u8` and re-runs `is_valid_utf8`; transcoding is validate, size, decode — three passes | (d) at the library | signatures over `string`; the blocker is `70-strings.md` §13's restrictions on `string` values (no rebinding, no aggregates), which push the stdlib to `[]u8` | removes a full pass from every text operation |
| 12 | Errors carry no position: `TextError` and `JsonDecodeError` are bare enums; the differential test recovers the offset by stepping | (a) at the library | `InvalidEncoding(at: u32)` payloads (ADT payloads exist); attach offset and path at the root driver, as weePickle does, so `JsonIntegerScan`'s 16-byte register-return ABI (`71-codecs.md` §18) is untouched | negative tests assert position; users get a location |
| 13 | Oak's hot paths use in-band sentinels (`json_result_value` returns `4294967295`, `json_hex4`, `JsonIntegerScan.status`) | disposition | acceptable as *private* helpers under a register-return ABI, and the justification in §18 should say so explicitly; the `Errors are values` item now records the rule | — |
| 14 | Late ADT discriminators: `71-codecs.md` §7 states the buffering contract, but ADT variants are not derived and "one bounds check per record" cannot hold when the variant is unknown before the object ends | (a) | either a format/policy phantom `TagFirst` (streaming legal) or a schema-level object size bound `N` (buffered legal); replay must re-establish position | derived ADT codecs |
| 15 | Composed consumers (`stream[F, S]`) have no stated lowering to one loop; only `encode`/`decode`/`from().to()` are derived | (d) | a method-set constraint for `S` so each stage is a monomorphized call | visitor-chain pipelines without objects |
| 16 | No skip primitive in `stdlib/json.oak` (only `json_skip_space`); unknown fields are rejected, so adding a producer field is a breaking change and `82-package-semver.md` does not see wire shapes | (a) | a bounded structural skip (declared depth and size) and a per-schema unknown-field policy; classify wire changes in the SemVer snapshot | tolerant readers, API evolution |
| 17 | Schemaless `stream[F, S]` has no number, count, or non-native-value policy | not stated | lexical number transit (digits plus dot and exponent offsets); a `CountsUpFront` format property selecting the buffered form; a declared cross-format lowering table | JSON→MsgPack without loss |
| 18 | Speculative transcoder writes (six valid of eight lanes stored, reclaimed by later stores) | (c) | a fact relating remaining input to remaining output is unstatable; keep pre-sizing and accept the per-store check, which also preserves unchanged-on-failure | — |
| 19 | Runtime ISA dispatch absent (recorded before) | (a) | simdjson's arm64 path has no dispatch either; costs nothing on M-series until SVE2 | x86 targets |
| 20 | Two-block software pipelining and the C backend's emission of `restrict`, `cold`, and `musttail` | (d) | assert the emitted code per `performance.md` §0 | — |

## Audit of `71-codecs.md` §1 against weePickle

The chapter's description is accurate and, if anything, understated:
weePickle's derived readers hold `To[...]` instances behind one interface
and call through `Visitor` virtuals, so "the abstraction disappears" is a
JIT hope at megamorphic call sites. Oak was right to reject runtime
visitor objects, boxing through `visitValue(v: Any)`, `asInstanceOf`
narrowing, `ClassTag` checks on write, exceptions as the error channel,
implicit resolution with priority traits, and the runtime recovery of
tagged-ness in `FromTo.join`.

Two premises in this pass's brief were wrong and are corrected here so
they are not repeated: weePickle has **no** `index` parameter on visit
methods (uPickle does; weePickle removed it and attaches offset, line,
column, token, and an RFC 6901 pointer from the *driver*), and `NullSafe`
and `Transmogrifier` do not exist in the codebase.

What §1 leaves out, each now a checklist item and a candidate spec edit:

1. Position comes from the driver, not from threading. The root wrapper
   knows the failing helper's `from` when it returns before advancing, so
   offset and path attach at the root at zero cost to the scanner ABI.
2. Discriminator ordering is a fast path (tag first, delegate the rest)
   and a slow path (buffer, find the tag at end, replay) — and the replay
   loses position unless re-established. Naming tags to sort first under
   key-sorting formats is the cheap trick.
3. Defaults are read semantics; omission on write is a wire-compatibility
   decision that must be opt-in and is only sound for constant defaults.
4. Unknown-field tolerance is an API-evolution policy, not a strictness
   preference.
5. The derived traversal should be written once against a format
   operation set and specialized per format, not regenerated per format;
   `compiler/codecs.go` rejects any format but `Json` today.
6. Count-bearing container headers (MsgPack) decide whether a direct
   `stream[Json, MsgPack]` is streaming or buffered.
7. Non-native values need a declared cross-format lowering table.

## Stated refusals

- **Stage-1 worker thread** (simdjson `parse_many`): `71-codecs.md` §11
  forbids implicit workers in codec paths. Not a gap.
- **"Free padding" by page-boundary check** (simdjson `doc/performance.md`):
  relies on reading past an allocation when it stays inside the page —
  class (e); sanitizers flag it. Oak's padding fact, when it lands, is a
  readable-capacity contract the caller provides, never an inference.
- **Tile choice, predicated zero-fill tails, lane mapping** were already
  refused in `codec-fusion-lessons-2026-09.md` and stand.
- **`convert_valid_*` as undefined behavior on invalid input**: Oak has
  the fact as a type; the level should be a signature over `string`, not
  a precondition comment.

## Testing practices adopted into the correctness list

Every body an oracle for every other with one differential fuzz target;
the test asserts which kernel ran and a nonexistent forced kernel fails;
generators produce each error class at every offset across a block edge
with detection lag as its own class; mutation brute force (byte replace,
bit set) against the reference; generators that return the witness;
hostile emulation for scalable vectors (`rvv_ta_all_1s`,
`rvv_ma_all_1s`, `rvv_vl_half_avl`, several VLENs); canaries around
fuzzed outputs and a stored corpus; oracle independence (simdutf is built
in `benchmarks/state-machines/cross` but only timed — compare it on
invalid inputs too); in-tree JSONTestSuite vectors for `stdlib/json.oak`;
ASan/UBSan and a compiler × flags matrix over the compiler e2e suites,
not only the benchmark workflows; the simdjson `perfdiff` rule (seven
interleaved samples, fail only when the new maximum is below the
reference minimum) to turn `benchmarks/json/compare.py` into a gate.

## If taken up

**Status, 2026-09-12 evening.** Findings 1–5 are closed: `tbl`, `shr`,
`subs`, and `prev` landed in 3587c9b with `stdlib/utf8.oak` at 9.6 GB/s
(the lookup4 validator in safe Oak, tables proved in `Oak.Utf8Lookup`);
`movemask_E`, `ctz_u32/u64`, and `popcount_u32/u64` landed the same
evening as the mask vocabulary of `93-simd.md` §1.2. Finding 6 (the
`ctz` loop as a bounded shape) stays an `OAK-D0103` obligation. The sixty-four-byte step followed the same evening: 12.3 GB/s beside simdutf's 12.9 and simdjson's 12.9 on the same run, within five percent of the golden implementations, in safe Oak.


Order by evidence: findings 1–5 are one `93-simd.md` revision (table
lookup, lane shift, cross-vector shift, movemask, bit builtins) and they
alone close the 6.8× UTF-8 gap with a validator that is safe Oak; then 9
(extent-fact spelling) so the block loop is check-free and asserted;
then 12 (error position) because every negative test after that asserts
it; then 11 (`string` as the consumed validated level) because it
removes a pass from every text operation; then 8 (`mul_hi`) with float
decoding in derived codecs; then 14–17 as the codec chapter's next
design round, with the §1 additions above landing in `71-codecs.md`
together.

## Revisit criteria

- `93-simd.md` gains the five operations: rewrite `is_valid_utf8` as
  the lookup4 validator in Oak, delete the C helper the backend emits,
  and re-measure `benchmarks/state-machines`.
- `TextError` and `JsonDecodeError` carry positions: extend
  `compiler/e2e_stdlib_utf8_diff_test.go` to sweep every error class
  across offsets 0..128 and assert class and offset.
- A second derived format exists: the §1 additions on format
  independence, counts, and lexical numbers become testable.
