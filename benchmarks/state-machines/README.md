# State-machine lowerings

Which code shape steps a protocol machine fastest on today's hardware when
the step stream is input-driven, and whether Oak's backend emits it. This is
the measurement behind `docs/spec/112-protocols.md` §2a and
`docs/spec/90-backend.md` §14: the declaration is the only thing a user
writes; the compiler chooses the lowering; `Oak.Protocol` proves it computes
the declaration.

## Files

- `lowerings.c` — three workloads against three hand-written lowerings:
  the branch tree clang produces from the old projection, a dense `u8`
  table with an illegal sentinel, and a shift DFA (one `u64` row per
  symbol, the state as a 6-bit field offset).
- `utf8_protocol.oak` — the UTF-8 validity DFA written as an Oak protocol,
  eight states plus the sink.
- `utf8_protocol.c` — what the backend emits for it (regenerate with
  `OAK_UPDATE_BENCH=1 go test ./compiler -run TestEmitStateMachineBenchmarkSource`).
- `run_utf8.c` — times the emitted `oak_utf8_run` over the same 64 MB of
  random valid UTF-8 that `lowerings.c` uses.
- `cross/` — the same validation against other fast implementations over
  one shared input file: Go's `unicode/utf8.Valid`, Rust's
  `std::str::from_utf8`, Zig's `std.unicode.utf8ValidateSlice`,
  `simdutf::validate_utf8`, and `simdjson::validate_utf8`, plus Oak's
  `is_valid_utf8` builtin. `cross/run.sh` builds and runs everything.

```sh
cc -std=c11 -O2 -o lowerings lowerings.c && ./lowerings
cc -std=c11 -O2 -o run_utf8 run_utf8.c && ./run_utf8
```

Steps are generated so the branch tree never traps (a random walk over
legal steps) and so that the byte machine moves between states (random
code points encoded as UTF-8); a predictable stream would flatter the
branch tree, and an input that parks the DFA in one state flatters
everything.

## Results

Apple arm64, clang `-O2`, best of five, 2026-09-12. Taken while another
process occupied the machine; the ordering is stable across runs, the
absolute figures are upper bounds.

| Workload | branch tree | dense table | shift DFA |
| --- | --- | --- | --- |
| One 3-state machine, 64M input-driven steps | 3.08 ns/step | 1.58 | 0.53 |
| UTF-8 DFA, 9 states, 64 MB valid text | 2.42 ns/byte | 1.66 (full 256-column table), 2.29 (class then table) | 0.51 |
| 1M machines × 32 rounds, one step each | 4.56 ns/step | 0.30 (u8 tags), 0.32 (u32 tags) | — |
| 16M machines × 4 rounds | 4.22 ns/step | 0.31 (u8), 0.33 (u32) | — |

Oak-emitted `utf8_run` (`run_utf8.c`): **0.52 ns/byte**, the hand-written
shift DFA's speed, from the declaration in `utf8_protocol.oak`.

What the numbers say:

- For input-driven steps the branch tree loses everywhere: the predictor
  cannot learn a random walk, and every step pays a misprediction.
- The dense table is one dependent load per step. Tag width did not matter
  at these sizes; the step stream, not the state array, is the traffic.
- The shift DFA is a load that does not depend on the state followed by a
  shift and a mask that do; its dependency chain is two cycles where the
  table's is a load latency. It needs the state to fit a 6-bit field
  offset, ten fields per `u64`, which covers most control protocols and
  most byte-class DFAs.
- Where the caller knows the state at compile time, none of this applies:
  the branch tree folds away entirely, and the phantom-typestate form has
  no run-time state at all (`docs/notes`, "Oak State Machines").

## Against other implementations

`cross/run.sh`, same machine and conditions, one 64 MB input file shared by
every program (`cross/gen_input.c`), best of five. Go 1.27, Rust 1.93,
Zig 0.16, simdutf 9.1, simdjson 4.6, all at their release optimization
levels.

| Implementation | ns/byte | GB/s |
| --- | --- | --- |
| simdjson `validate_utf8` (SIMD) | 0.07 | 13.5 |
| simdutf `validate_utf8` (SIMD) | 0.07 | 13.4 |
| **Oak protocol `utf8_run` (shift DFA, emitted from the declaration)** | **0.51** | **1.97** |
| Oak builtin `is_valid_utf8` (scalar, Table 3-7 transliteration) | 2.50 | 0.40 |
| Zig `std.unicode.utf8ValidateSlice` | 2.55 | 0.39 |
| Rust `std::str::from_utf8` | 2.56 | 0.39 |
| Go `unicode/utf8.Valid` | 2.73 | 0.37 |

What the comparison says:

- Among scalar validators the declaration-derived machine is five times
  faster than the three standard libraries and than Oak's own builtin. The
  standard libraries branch on byte classes; their ASCII fast paths rarely
  fire on this input because multi-byte sequences interleave every few
  bytes. Real text with long ASCII runs would narrow the gap for them.
- SIMD is a different regime: the lookup-table validators (Keiser and
  Lemire's algorithm, as shipped in simdutf and simdjson) process sixteen
  or more bytes per step and run seven times faster than any scalar DFA.
  That is the ceiling on today's hardware for this golden case, and no
  scalar lowering reaches it.
- The consequence for Oak: for byte-driven machines that are validators of
  a fixed format, the peak structure is a SIMD algorithm, not a DFA, and
  Oak's portable 128-bit vectors (`docs/spec/93-simd.md`) can express it.
  The next increment for this golden case is `is_valid_utf8` written over
  `simd.U8x16` with a proof against `Oak.Utf8Validity`, made the builtin's
  lowering. General protocol machines keep the DFA lowering; it is the
  best structure for a machine that is not a fixed format.
- Hyperscan and Vectorscan are regex engines and are the right comparison
  for the next golden case, multi-pattern byte scanning; neither is
  installed here, and this table does not include them.

