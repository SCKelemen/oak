# The Oak Book

Oak is a systems language for firmware, kernels, and hypervisors: borrow
checking without lifetime syntax, compilation to readable C, and a Lean 4
proof gate that keeps the semantics honest. This book is the **conceptual
companion** to the normative specification in [`docs/spec/`](../docs/spec/)
— the spec defines the language; the book explains the *hierarchies* the
language is organized around, because systems programming is mostly the
discipline of knowing which rung of a ladder you are standing on:

- **values and places** — what can be read, what can be assigned
  ([foundations/values-and-places.md](foundations/values-and-places.md))
- **the type lattice** — how types order, join, and meet
  ([foundations/type-lattice.md](foundations/type-lattice.md))
- **atomicity, consistency, isolation, durability** — four ladders, one
  page each: [atomicity](hierarchies/atomicity.md),
  [consistency](hierarchies/consistency.md) (eventual through
  linearizable, plus the invariant-obligation ladder),
  [isolation](hierarchies/isolation.md) (the borrow checker as a static
  isolation-level scheduler), and
  [durability](hierarchies/durability.md)
  (overview: [hierarchies/acid.md](hierarchies/acid.md))
- **progress guarantees** — blocking to wait-free-bounded, and why Oak's
  bounded-loop certificates are progress proofs
  ([hierarchies/progress.md](hierarchies/progress.md))
- **containers** — ownership × shape × capacity
  ([hierarchies/containers.md](hierarchies/containers.md))
- **intrusive containers** — pools and typed index links instead of pointer
  graphs ([hierarchies/intrusive.md](hierarchies/intrusive.md))
- **the memory-order ladder** — plain, volatile/MMIO, relaxed to seq_cst,
  barriers ([concurrency/memory-order.md](concurrency/memory-order.md))
- **a catalog of kernel structures** with their classifications
  ([structures/catalog.md](structures/catalog.md))

## How to read claims in this book

Three levels of confidence appear, and the book always says which one a
statement carries:

1. **Executed** — an end-to-end test in this repository compiles the Oak
   source to C, builds it with the system compiler, runs it, and asserts
   behavior. Cited as `compiler/e2e_*.go`.
2. **Proven** — a Lean 4 module in `spec/lean/Oak/` machine-checks the
   stated law; where the compiler's own decision procedure is a
   transliteration of the model, `docs/spec/STATUS.md` records a refinement
   (R) claim with its exact scope.
3. **Design** — normative direction in `docs/spec/` not yet implemented.
   The book marks these explicitly; `docs/spec/STATUS.md` is the only
   authoritative status matrix.

The book renders with any SUMMARY-driven toolchain (GitBook, mdBook,
HonKit): the table of contents is [SUMMARY.md](SUMMARY.md).
