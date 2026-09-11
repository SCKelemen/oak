# Standard library: verification and performance status

One row per package. Every cell was derived from the tree on the date in the
footer, not from prose: test names come from `grep '^func Test'` over
`compiler/*_test.go`, Oak test names from the `Property*`/`Test*`/`Sim*`
declarations under `examples/`, theorem names from the Lean files, and the
ratios from the tables in `benchmarks/stdlib/RESULTS.md` and
`benchmarks/kernels/RESULTS.md`. When this file and a README paragraph
disagree, the file that was checked against the tree more recently wins;
fix the other.

## Legend

- **Go e2e**: files under `compiler/` whose tests compile the package through
  the C backend (and, where noted, the interpreter) and execute the result.
- **Oak tests**: `oak test` targets under `examples/` — choice-tape
  properties (`Property*`), deterministic simulations (`Sim*`), unit
  tests (`Test*`), fuzz entries (`Fuzz*`).
- **Oracle**: what the tests compare against beyond hand-written
  expectations — a Go standard-library package, a published conformance
  file, a reference implementation written for the test, or a Go
  transliteration of the same rules.
- **Extraction**: the package's Lean image produced by `oak build -lean`
  and committed under `spec/lean/Oak/Stdlib/` with the drift test
  `compiler/lean_stdlib_extract_test.go`; "—" means the package uses
  constructs the extractor still fails closed on (`docs/spec/95-extraction.md`
  section 4).
- **Universal**: theorems proved for every input (of the stated shape)
  about the extraction, or about a hand-written model where the row says so.
- **Decided**: facts the Lean kernel evaluates on specific inputs (vectors,
  adversarial cases); evidence, not a proof of the general law.
- **Remaining**: laws stated in the docs but not proved, and known gaps.
- **Faithful**: covered by `compiler/lean_stdlib_faithful_test.go`, which
  runs the committed extraction and the compiled program on one corpus and
  compares them byte for byte (the executable complement of the drift test).
- **Benchmarks**: workload names from `benchmarks/stdlib/` and the Oak / Go
  time ratio from the most recent table in `RESULTS.md` (below 1× is faster
  than Go); `kernels:` refers to `benchmarks/kernels/RESULTS.md`, which
  compares against Rust as well.

## The table

| Package | Go e2e | Oak tests | Oracle | Extraction | Universal | Decided | Remaining | Faithful | Benchmarks (Oak / Go) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `std` prelude (`Option`/`Result`, bytes, ring, endian, bitsets, buffers, builder, array lists, intrusive lists/queues, splice, min-heap, deque, ID pool) | `e2e_stdlib_test.go`, `e2e_stdlib_bits_endian_test.go`, `e2e_stdlib_buffer_test.go`, `e2e_stdlib_collections_test.go`, `e2e_stdlib_splice_test.go`, `e2e_stdlib_heap_test.go`, `e2e_stdlib_deque_id_test.go` | — | sequence/array/occupancy models written in the tests; Go `encoding/binary` fixtures for endian rows; Go `copy` for byte moves | — (prelude helpers such as `bytes_range_fits` extract only as callees of extracted packages) | — | — | no laws stated; ring and collection contracts are model-tested only | as callees only | — |
| `strings` (UTF-8, UTF-16/32 views, Latin-1, BOMs, search, split, builder, number text) | `e2e_stdlib_text_test.go`, `e2e_stdlib_text_encoding_test.go`, `e2e_stdlib_utf8_diff_test.go` | `testing/text_encoding_test.oak`: `PropertyLatin1RoundTrip`, `PropertyUtf16BytesRoundTrip`, `PropertyNumberRoundTrip`; `testing/arithmetic_test.oak`: `FuzzUtf8` | Go `unicode/utf8` (validity, count, first ill-formed offset, every decoded scalar on 1,440 inputs), `strconv`, `encoding/json` | — (strings fail closed) | hand models, not the package: `Oak/Utf8Validity.lean` (`seq_yields_scalar`, `seq_length_canonical`, `seq_length_bounds`, `ascii_valid`, `valid_pieces_are_scalars`) states the UTF-8 validity the source gate and `utf8_validate` implement; `Oak/StrEncoding.lean` (`retag_preserves_units`, `retag_utf8_wf_iff`, `ascii_retag_utf8_wf`, `utf8_retag_ascii_needs_ascii`) the encoding retags | — | the package's own functions are unproved; extraction of strings is the blocker | no | `strings/utf8_validate` 1.11×, `strings/utf8_scan` 1.63×, `strings/parse_u64` 0.71×, `strings/append_u64` 1.19× |
| `unicode` (case mapping, folding, cased/case-ignorable tables; Unicode 17.0.0) | `e2e_stdlib_text_test.go` (`TestE2EStdlibTextUnicodeCase`, `TestE2EStdlibTextUnicodeTables`) | — | generated-table check in CI (`stdlib/generate_unicode.py`) | — | — | — | no laws | no | — |
| `json` (strict string codecs; derived record codecs live in the compiler) | `e2e_json_codec_test.go`, `e2e_json_decode_test.go`, `e2e_derived_json_test.go` | — | Go `encoding/json` in the text tests; simdjson in `benchmarks/json/` | — | — | — | codec fusion witnesses are generated-C checks (`e2e_codec_fusion_test.go`), not proofs | no | `benchmarks/json/RESULTS.md`: 1.13× simdjson (Apple M1 virtual), 1.40× (EPYC 7763) |
| `filters`, `hash_table`, `bitset_algebra` (collection ports) | `e2e_oak_libraries_test.go` | — | models written in the tests | — | — | — | no laws | no | — |
| `causal_frontier` | `e2e_causal_frontier_test.go` | — | — | — | hand model `Oak/CausalFrontier.lean` (lattice laws: `le_refl`, `le_trans`, `le_antisymm`, `bottom_le`, `le_join_left`, `le_join_right`, `join_least`, `join_idempotent`, `join_commutative`, `join_associative`, `join_bottom_left`, `join_bottom_right`, `join_monotone`, `join_preserves_left_cover`, `join_preserves_right_cover`) and `Oak/CausalFrontierRefinement.lean` (`execJoin_refines_join`, `execLe_refines_LE`, `execCovers_refines_covers`, `execObserveComponent_*`) | — | the Oak package is related to the model by the refinement file's transliteration, not by extraction | no | — |
| `math` (transcendentals) | `e2e_math_test.go` (`TestMathLibraryFourthWitness`, seeded) | — | reference evaluations in the test against Go `math`, ulp-bounded | — (floats extract since #187, but `math` is not among the committed extractions) | `Oak/Floats.lean` models the float discipline, not these functions | — | no laws about the functions themselves | no | — |
| `hash` (SHA-256, BLAKE3, CRC-32C) | `e2e_hash_test.go` (`TestE2EHashKnownAnswers`, `TestE2EHashDifferential`, `TestE2EHashBlake3`, `TestBlake3ReferenceAnchors`) | — | FIPS 180-4 vectors, RFC 3720 check value, Go `crypto/sha256` and `hash/crc32` on random input, an in-test BLAKE3 reference | `HashExtracted.lean` | — | — | no laws yet (the natural first ones: CRC table equals the bit-serial definition; SHA-256 against a reference compression) | yes (`crc32c`, `sha256`) | `hash/crc32c` 20.0×, `hash/sha256` 7.31× (Go uses hardware instructions); `kernels:` 1.10× Rust (crc32c), 0.96× Rust (sha256) |
| `mx` (MXFP4 blocks) | `e2e_mx_test.go` (`TestE2EMxBlocks`, `TestMxReferenceProperties`) | — | reference properties in the test | — | — | — | no laws | no | — |
| `sort` | `e2e_stdlib_sort_varint_random_test.go` (`TestE2EStdlibSortAndSearch`), `e2e_stdlib_sort_pdq_test.go` (`TestE2EStdlibSortMatchesGo`) | `testing/sort_varint_random_test.oak`: `PropertySortPermutes`, `PropertySortAdversarial` | Go `slices.Sort` (seven shapes, fourteen lengths, both depth-budget fallbacks) | `SortU32Extracted.lean` (the `u32` instantiation) | `SortLaws.lean`: `sort_insertion_spec`, `sort_insertion_sorted`, `sort_heap_spec`, `sort_heap_sorted`, `writeback_perm`, `sort_span_small`, `sort_span_budget_small`, `sort_span_budget_zero` | `span_sorts_sorted24`, `span_sorts_reversed24`, `span_sorts_equal24`, `span_sorts_organ_pipe24`, `span_sorts_few_distinct24`, `span_sorts_sawtooth24`, `span_budget_one_reversed16`, `heap_sorts_example`, `span_sorts_example`, `span_sorts_reversed` | `sort_span` beyond the insertion threshold on the pattern-defeating path (needs the range-stack invariant and in-bounds proofs of every swap) | yes (`sort_insertion`, `sort_heap`, `sort_span`) | `sort/random` 1.02×, `sort/reversed` 1.18×, `sort/sorted` 1.12× |
| `varint` (LEB128, ZigZag) | `e2e_stdlib_sort_varint_random_test.go` (`TestE2EStdlibVarint`) | `PropertyVarintRoundTrip` | — (round trip and the protobuf `300 = AC 02` example in the tests) | `VarintExtracted.lean` | `VarintLaws.lean`: `round_trip`, `round_trip_all`, `size_le_ten`, `varint_size_spec`, `canonical` (whatever `varint_decode` accepts, the encoder writes back byte for byte) | `encode_300`, `round_trip_0` … `round_trip_len10`, `round_trip_max`, `round_trip_one_byte`, `overlong_tenth_byte_rejected`, `truncated_rejected`, `decode_stops_at_terminator`, `zero_padding_rejected`, `padded_one_rejected`, `plain_zero_accepted` | ZigZag and the signed composites are not stated | yes (encode, decode) | `varint/decode` 0.75×, `varint/encode` 1.08× |
| `random` (xoshiro256\*\*) | `e2e_stdlib_sort_varint_random_test.go` (`TestE2EStdlibRandom`) | `PropertyShuffleIsPermutation` | — | `RandomExtracted.lean` | `RandomLaws.lean`: `random_next_spec` (equals the xoshiro256\*\* reference step), `random_below_lt`, `random_range_mem` | — | `random_fill` and `random_shuffle` (a permutation) are not stated | yes (`random_next` sequences) | `random/xoshiro` 0.31× (against a Go xoshiro256\*\* written for the harness; Go's PCG shown alongside) |
| `encoding` (hex, base64, base32, percent) | `e2e_stdlib_encoding_test.go` (`TestE2EStdlibEncodingVectors`, `…Rejections`, `…QualifiedImport`), `e2e_stdlib_encoding_diff_test.go` | `testing/encoding_test.oak`: `PropertyEncodingRoundTrip` | RFC 4648 section 10 vectors; Go `encoding/base64`, `encoding/base32`, `encoding/hex` on 28 lengths × 9 codec/alphabet/padding combinations | `EncodingExtracted.lean` | `EncodingLaws.lean`: `hex_round_trip` (both cases, every source below 2^31−2 bytes) | `base64_foobar`, `base64_foob`, `base32_foobar` (the RFC vectors) | base64/base32 round trips universally, hex strictness (`hex_decode` accepts a string iff it is an encoding), percent-encoding laws | yes (hex, base64) | `encoding/base64_decode` 1.19×, `base64_encode` 1.10×, `hex_decode` 1.22×, `hex_encode` 0.93×, `percent_encode` 1.03× |
| `url` (RFC 3986) | `e2e_stdlib_url_test.go` (`TestE2EStdlibUrlParse`, `…Resolve`, `…Qualified`) | `testing/url_test.oak`: `PropertyUrlRangesPartition`, `PropertyDotSegmentsIdempotent` | RFC 3986 Appendix C reference-resolution examples (all 42) | — | — | — | no laws; not extracted | no | — |
| `uuid` (RFC 9562 v4, v7) | `e2e_stdlib_uuid_test.go` (`TestE2EStdlibUuid`, `…Qualified`) | `testing/uuid_test.oak`: `PropertyUuidTextRoundTrip`, `PropertyUuidV7Order` | RFC 9562 Appendix A.6 vector | `UuidExtracted.lean` | — | — | version/variant bits of `uuid_v4`/`uuid_v7`, `uuid_v7_millis` recovery, `uuid_parse ∘ uuid_format` identity | no | `uuid/v7_format` 0.85× |
| `path` (Go `path` semantics, glob with `**`) | `e2e_stdlib_path_test.go` (`TestE2EStdlibPath`, `…Qualified`) | `testing/path_test.oak`: `PropertyPathCleanIdempotent`, `PropertyPathEscapedSelfMatch`, `PropertyPathDoubleStarSubsumesStar` | Go `path` and `path.Match` test tables | — | — | — | no laws; not extracted | no | — |
| `float` (shortest and correctly rounded decimal text) | `e2e_stdlib_float_test.go` (`TestE2EStdlibFloatHardCases`, `…Differential`, `…QualifiedImport`) | `testing/float_test.oak`: `PropertyFloatShortestRoundTrip`, `PropertyFloatFixedNearby`, `PropertyFloat32RoundTrip` | Go `strconv` (`FormatFloat`, `ParseFloat`) on thousands of random bit patterns and spellings, exact midpoints via `math/big` | `FloatExtracted.lean`; `FloatKernelsExtracted.lean` (an ml-shaped dot product / sums / axpy / quantize program) | — | — | Lean's `Float` is opaque to the kernel, so nothing about the extraction is decidable; float theorems stay against `Oak/Floats.lean`; the extraction is an executable model for differential comparison | no | stub only (workload not yet in the harness) |
| `grapheme` (UAX #29 extended grapheme clusters, Unicode 17.0.0) | `e2e_stdlib_grapheme_test.go` (`TestE2EStdlibGrapheme`, `…Conformance`, `…Qualified`), `e2e_stdlib_grapheme_laws_test.go` | `testing/grapheme_test.oak`: `PropertyGraphemeChainPartitions`, `PropertyGraphemeAscii` | `GraphemeBreakTest-17.0.0.txt` (all 766 lines exact); a Go transliteration of the rule relation over every class sequence up to length 5 (18^5) | — | hand model `Oak/GraphemeBreak.lean`: `machine_agrees` (the state machine equals the rule relation on every history of well-formed symbols), with `run_prev`, `run_riRun`, `run_pict`, `run_conjunct`, `conjScan_seen`, `pictState_eq_one`, `pictState_eq_two`, `conjState_eq_two` | — | the Oak state machine is related to the Lean machine by the Go law test, not by extraction; the well-formedness side condition is checked against the table by the Go test | no | — |
| `normalize` (UAX #15 NFD/NFKD/NFC/NFKC, quick checks; Unicode 17.0.0) | `e2e_stdlib_normalize_test.go` (`TestE2EStdlibNormalize`, `…Conformance`, `…Qualified`), `e2e_stdlib_normalize_laws_test.go` | `testing/normalize_test.oak`: `PropertyNormalizeLaws`, `PropertyNormalizeAsciiFixedPoint` | `NormalizationTest-17.0.0.txt` (all 20,034 lines, five-column invariants and quick checks); a Go transliteration on 400 random sequences × 4 forms | — | hand model `Oak/Normalization.lean`: `order_perm`, `order_sorted`, `order_stable`, `order_idem`, `nfd_idem` (canonical ordering is a stable sorted permutation; NFD is idempotent) | — | NFC laws (`nfc` idempotent, `nfd ∘ nfc = nfd`) are defined and stated, not proved; Part 1 completeness sweep, stream-safe text, NFKC_Casefold not provided | no | `normalize/nfc` 0.40×, `normalize/nfd` 0.57× (against a naive allocating Go transliteration — Go's standard library has no normalizer), `normalize/is_nfc_ascii` 0.91× |
| `time` (instants, durations, calendar, RFC 3339, `TimeSource`, interval readings) | `e2e_stdlib_time_test.go` (`TestE2EStdlibTimeCalendar`, `…Duration`, `…Rfc3339`, `…Overflow`, `…Differential`), `e2e_stdlib_timesim_test.go` (`TestE2EStdlibTimeSource`, `…UnrefreshedTraps`) | `time/time_test.oak`: `TestEpoch`, `TestLeapSecondRejected`, `TestLowercaseAccepted`, `PropertyCivilDaysRoundTrip`, `PropertyInstantCivilRoundTrip`, `PropertyFormatParseRoundTrip`, `PropertyDurationTextRoundTrip`, `PropertyCheckedAdd` | Go `time` (3000 instants at seven offsets, 1000 durations, 400 duration spellings, every expectation computed by Go) | — (library-only package; not among the committed extractions) | hand model `Oak/TimeInterval.lean` for interval readings under an attested bound: `honest_iff`, `bound_break_dishonest`, `before_sound`, `overlap_unordered`, `refusal_claims_nothing`, `order_sound` | — | calendar and RFC 3339 functions are differentially tested only | no | `time/format_rfc3339` 0.45×, `time/parse_rfc3339` 0.59× |
| `timesim`, `timenative` (simulated clocks with faults, host clocks) | `e2e_stdlib_timesim_test.go` (`TestE2EStdlibTimeNative`) | `timesim/lease_test.oak`: `TestLeaseFixedClock`, `PropertyLeaseUnderClockFaults`, `SimLeaseTwoClients`, `PropertyLeaseCommands`, `PropertyGenerators` | the lease consumer's laws under every fault mask (monotonic never decreases; a timer fires once and never early; at most one holder) | — | (`Oak/TimeInterval.lean` covers the skew/bound semantics `timesim` drives) | — | the fault ledger and generators are property-tested only | no | — |
| `testing`, `sim_storage`, `sim_sched` (choice tapes, simulated disk, crashes, scheduling) | runner tests under `testrunner/`; `compiler/e2e_protocol*_test.go` for protocol declarations | `testing/sim_storage_test.oak`: `TestSimDiskCrashContract`, `TestSimDiskTornWriteIsLedgered`, `TestSimDiskLostFsyncIsLedgered`, `PropertySimDiskExact`, `SimWalRecovery`, `TestSimDiskCleanUnderFaultMask`; `testing/sim_sched_test.oak`: `TestSimSchedForcedPick`, `TestSimProcessCrashThenRestart`, `PropertySimSchedFair`, `SimWalEvents`; `testing/irq_test.oak`, `testing/protocol_test.oak`, `testing/protocol_data_test.oak` | protocol declarations render to TLA+ and are model-checked (`docs/spec/112-protocols.md`) | — | `Oak/Protocol.lean`, `Oak/ProtocolQuorum.lean` cover protocol declarations, not the simulation packages | — | no laws about the simulation packages themselves | no | — |
| `iosim`, `ionative` (the IO port) | `e2e_io_port_test.go` (`TestE2EIoPortSimulated`, `…Native`, `…NativeRejectedInSimulation`) | — | — | — | hand model `Oak/IoPort.lean`: `chain_all_ok`, `chain_canceled_rest`, `chain_cancels_rest`, `fsync_covers`, `fsync_keeps`, `fsync_claims_nothing_else`, `read_sees_write`, `write_elsewhere` | — | the Oak port is related to the model by the spec (`docs/spec/120-io.md`), not by extraction | no | — |
| `arena` (reservations over an owner) | `e2e_buffers_test.go` (`TestE2EOwnedBuffers`, `TestOwnedBufferRejections`), `e2e_ffi_inbound_test.go` | — | — | — | — | — | no laws | no | — |

## How to read the gaps

Three tiers of evidence appear in the table, and they are not
interchangeable:

1. **Proved on the extraction** (`sort`, `varint`, `random`, `encoding`'s hex
   path). The theorem is about the Lean image of the Oak code that the C
   backend also compiles; the drift test keeps the image current and the
   faithfulness test keeps its meaning equal to the compiled program on a
   corpus. The remaining assumptions are the extractor and the compiler
   themselves (`docs/spec/95-extraction.md` section 3 states the modeling
   choices: out-of-range reads yield zero, dropped stores, division by zero
   yields zero, clamped `subslice`, masked shift counts).
2. **Proved on a hand-written model** (`grapheme`, `normalize`,
   `causal_frontier`, `time`'s interval readings, the IO port, UTF-8
   validity). The theorem is about the rules; a Go law test or a
   transliteration relates the Oak code to the model on enumerated or random
   inputs. Extracting these packages would replace that test with a proof
   obligation.
3. **Differential and conformance tests only** (everything else). The
   oracle column says what the code was compared against and how many
   inputs; "models written in the tests" means a sequence or array model in
   Go, not an external reference.

## How to extend

- **Extraction**: add a row to the table in
  `compiler/lean_stdlib_extract_test.go` (package name, file, namespace,
  dependencies or a driver source), run
  `OAK_LEAN_EXTRACT_UPDATE=1 go test ./compiler -run TestLeanStdlibExtract -count=1`
  to write `spec/lean/Oak/Stdlib/<Name>Extracted.lean`, import it from
  `spec/lean/Oak.lean`, and confirm `lake build` in `spec/lean` elaborates it.
  The test without the variable fails on drift; CI runs it in the
  standard-library workflow.
- **Faithfulness**: extend the corpus and the Oak driver in
  `compiler/lean_stdlib_faithful_test.go` so the new package prints one line
  per case from both the extraction (`lake env lean --run`) and the compiled
  module; the Formal Verification workflow runs it after the Lean build. It
  skips without a Lean toolchain.
- **Laws**: one file per package under `spec/lean/Oak/Stdlib/<Name>Laws.lean`
  (or a rule model under `spec/lean/Oak/` when the package implements a
  published specification), imported from `Oak.lean`; CI builds with
  warnings as errors, so no `sorry` and no unused-simp-argument warnings.
  Record what is universal versus decided in this table and in
  `docs/spec/95-extraction.md` section 6.
- **Benchmarks**: `benchmarks/stdlib/README.md` "Adding a package": an Oak
  program under `benchmarks/stdlib/oak/<pkg>/`, a C bridge, a Go twin in
  `goref/`, matching corpus generators and checksums, and a row in
  `RESULTS.md` from a run at scale 1 on a named machine.

Snapshot taken 2026-09-12 against `specification` at a486e90.
