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
