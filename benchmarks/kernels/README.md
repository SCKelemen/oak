# Kernel comparison: Oak against Go and Rust

`run.py` builds the same ten kernels three ways and times them on identical
data: Oak (`oak/kernels.oak`, compiled through `oak build` to C and `cc -O3`,
with the bounds checks the checker cannot discharge left in), Go
(`go/main.go`, `go build`), and Rust (`rust/main.rs`, `rustc -O`, standard
library only). Every implementation prints the checksum of its result and the
driver refuses to record a timing until all agree.

| Kernel | Workload | Shape it stands for |
| --- | --- | --- |
| `crc32c` | CRC-32C of 1 MiB | page checksum (dbs) |
| `sha256` | SHA-256 of 1 MiB | content hash (dbs, os images) |
| `blake3` | BLAKE3 of 1 MiB, Oak only | content hash |
| `dot` | f32 dot product, 2^20 elements | reduction (ml) |
| `sum` | u64 sum, 2^20 elements | the simplest loop |
| `search` | binary search of 2^16 probes in 2^20 sorted keys | index lookup (dbs) |
| `page_probe` | 2^16 probes: fence-key search over 2^11 pages of 512 keys, then a search inside the page view | B-tree leaf probe (dbs) |
| `bitmap` | free-bit count over 2^20 u64 words | allocator bitmap scan (os) |
| `dispatch` | 2^20 bytecodes, eight opcodes over two u64 registers | syscall and interpreter dispatch (os) |
| `tiled` | f32 sum of squares, eight accumulators, 2^20 elements | tiled reduction (ml) |

Two Go rows exist where they differ: `go-stdlib` is the standard library,
which uses the CPU's SHA-256 and CRC-32C instructions on this class of
machine and its population-count instruction for `bitmap`, and
`go-generic` is the plain pure-Go algorithm of the same shape as Oak's
(the SWAR popcount for `bitmap`). Rust's `bitmap` row uses `count_ones`,
also the hardware instruction; Oak has no popcount intrinsic yet, so its
row is the SWAR form. Rust's rows are hand-written plain algorithms
(word-at-a-time SHA-256, table-driven CRC-32C); no crates are used, so they
are not the `sha2` or `crc32c` crates.

What is not measured: allocation, hardware counters, cache-controlled or
affinity-controlled runs, and anything but these workloads. `dot` is a
strict left-to-right f32 sum in all three (Oak forbids reassociation and
contraction, Rust and Go do not vectorize this form either), so it compares
scalar loops. Run:

```sh
python3 benchmarks/kernels/run.py --output results/kernels.json
```

Results and the optimizations they drove are recorded in
[RESULTS.md](RESULTS.md).
