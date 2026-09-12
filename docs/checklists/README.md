# Extraction checklists

Two documents collect, once, the techniques Oak keeps re-deriving from its
reference material — Go, Rust, Zig, Odin, Elm, the ML family, Swift,
Futhark, Mojo, Scala; Idris, Coq, Lean, TLA+, Apalache, Z3; mlx, tinygrad,
data-oriented design, mechanical sympathy, TigerBeetle and TigerStyle,
MISRA C, NASA's Power of Ten, simdjson, simdutf, Hyperscan — so that a
review pass walks a list instead of re-reading the sources.

- [`correctness.md`](correctness.md) — everything that must be true.
- [`performance.md`](performance.md) — everything that must be fast, and
  how to know it is.

The constitution orders the two: correctness, then performance, then
simplicity (`../spec/00-constitution.md`). A performance item is never
license to weaken a correctness item; the performance list says so where
the tension is real, and points at the correctness item that wins.

## Shape of an item

```text
- [ ] **Name.** The question to ask, stated so that "no" is a finding.
      (source) — Oak: where the rule lives, or `open`, or `not stated`.
```

- **Name** is what a finding is filed under.
- The **question** is phrased against a concrete artifact: a spec chapter,
  a standard-library module, a compiler pass, a benchmark.
- **(source)** names where the technique comes from, in a word or two.
  It is provenance, not authority; the constitution and the spec are the
  authority.
- **Oak:** is a pointer into `docs/spec/`, `docs/notes/`, `stdlib/`, or
  `benchmarks/`, so a pass can check the claim against the text.
  `open` means the spec or a note records the item as not done;
  `not stated` means no chapter takes a position yet — which is itself a
  finding worth a line.

## Running a pass

1. Pick one target: a chapter, a module, a lowering, a benchmark. Not the
   whole language.
2. Walk one list top to bottom. For each item answer yes, no, or not
   applicable — write down the "no"s and the "not stated"s.
3. Record the findings as a `docs/notes/<target>-<yyyy-mm>.md` disposition
   table in the existing style (ask, disposition, revisit criteria). Every
   finding names the spec section it changes or the test it adds.
4. Anything learned about the *technique* — a sharper question, a new
   source, a case where the item was wrong — goes back into the checklist.
   The sources are read once; the lists are what accumulate.

A pass over a performance change also walks the correctness list's
sections on oracles, numeric semantics, and transformation legality. A
change that makes a benchmark faster and an oracle disagree is a
correctness finding, not a performance win.

## Adding an item

Add an item when a source teaches something that is not already a line,
or when a pass finds a class of problem no line would have caught. Merge
rather than append when a line already covers it: the lists are meant to
stay walkable in one sitting. Delete items the spec has made unnecessary
only when the spec enforces them mechanically — a rule the compiler
checks no longer needs a reviewer to ask about it, but the line should say
which diagnostic code took over.
