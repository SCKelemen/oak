# Four-language ARM64 reduction comparison

This preparation/measurement harness compares Oak native, independent C, Rust,
and Zig implementations of the unchanged `../paired_loads/sums.oak` u32/u64
reductions. The C row is **not** Oak-generated C. Two microkernels cannot establish
representative ±8% language parity, and instruction counts are not timing results.

All implementations sum initialized, aligned elements with unsigned modular
arithmetic. Each uses the ARM64 C ABI (pointer plus u32 length). C layout asserts
and cross-language boundary checks cover the ABI; this is not a formal ABI proof.
The runner links separate optimized objects without LTO and calls each through
the same volatile function-pointer harness. Input generation, warmup, result
checking, and volatile sinks are shared. C uses `-O3 -mcpu=generic`, Rust uses
`opt-level=3,target-cpu=generic`, and Zig uses `ReleaseFast,-mcpu=baseline,-fllvm`.
These are explicit generic/baseline targets, not identical feature guarantees or
M4-specific tuning. Zig 0.16 resolves the macOS baseline to `apple_m1`, including
NEON; the harness records its actual target diagnostics and refuses missing NEON.
Its current scalar reduction output is not evidence of disabled SIMD capability.
Oak uses its current ARM64 native backend defaults.
All comparator objects target macOS 13.0 explicitly, including Rust's
`MACOSX_DEPLOYMENT_TARGET`; Oak's companion object is linked into that executable.

Prepare first (ARM64 macOS; all four compilers are mandatory):

```sh
python3 -m unittest discover -s benchmarks/native/four_way -v
python3 benchmarks/native/four_way/run.py prepare \
  --artifacts /private/tmp/oak-four-way-unique/build \
  --rustc /absolute/path/to/working/rustc
```

The artifact directory must not already exist. Preparation emits two **proven**
Oak native bodies with verifier caching disabled, builds all four implementations,
and checks 112 implementation/width/length combinations, including zero, vector
tails, 511/512/513 boundaries, and overflow-inducing deterministic input. Check
mode does not invoke the benchmark clock. Missing compilers, selected assembly,
proof verdicts, or correctness rows fail closed; there is no optional comparator.

`prepared.json` retains exact tool paths/versions/hashes, source hashes, compiler
actual nonstandard Go-package build-input hashes checked before/after the build
(including embedded inputs, excluding unrelated tests), revision and dirty status, native
assembly, build argv/logs, disassembly, object/binary hashes, and correctness rows.
An unsuccessful prepare leaves its diagnostics but no successful manifest. Set
`GOCACHE` externally to a task-specific or approved existing Go cache if needed;
Zig caches stay inside the artifact directory. Inherited `OAK_*` options are cleared.
If CPU metadata cannot be read, preparation records `null`; measuring that manifest
is refused, so rerun preparation where `sysctl` can read the CPU model.

Only after compiler/proof builds and other host work stop, measure the same artifacts:

```sh
python3 benchmarks/native/four_way/run.py measure \
  --artifacts /private/tmp/oak-four-way-unique/build \
  --confirm-host-quiet --max-load 1.0 --samples 9 --calls 128 \
  --elements 7 4096 1048576 --output /private/tmp/four-way-timing.json
```

Measurement performs no builds. It rejects changed benchmark sources/artifacts,
requires the prepared CPU identity, checks all three load-average windows before
each sample and afterward, rotates implementation/width order, and verifies row
identity and checksums against a Python integer oracle. Raw positive elapsed times
are retained; samples are not filtered. Load guards and operator confirmation do
not guarantee isolation, thermal/power stability, or performance-core placement.
Affinity is uncontrolled, inputs are warmed, and call/check/sink overhead is included
equally. Choose calls for a useful signal; tiny reductions can be dominated by this
overhead. A raised load limit must be disclosed, not called an isolated result.

This is a correctness-and-provenance baseline for future quiet-host measurement,
not proof of source-to-ARM-ASL correspondence or memory-ordering correctness.
