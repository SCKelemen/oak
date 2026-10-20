# Stateful-copy representation proof gate

This is the bounded **lifted extracted-semantics** adapter following the frozen
three-file [source/layout contract](../../docs/notes/stateful-copy-contract-2026-10.md).
It changes no production compiler, extractor, checker, ABI, or acceptance profile.

## What is proved

`Oak.StatefulCopy` reuses the actual `Oak.Stdlib.Bytes.copy_into`, its Result ADT,
`BytesLaws`, and `ViewRefinement`; it introduces no replacement byte-copy loop.
`logical` takes a real backing-array window. `RepresentsWindow` relates every
initialized backing byte to partial memory, live owner metadata, backing bounds,
u32 length, and a conservative representable owner endpoint. `Invocation` adds
explicit read/write grants and physical source/destination separation. Grants
are invocation metadata, **not** a proof of borrow-checker soundness.

`extracted_total` derives the Result and complete array prefix/suffix behavior
without assuming a successful run. `liftedCopy_total` derives termination and
`ObservesCopy`: exact Result, the frozen caller's match/length Bool observation,
copied destination prefix, unchanged destination suffix and source, and unchanged
external memory. The sufficient extracted fuel premise applies only to success;
`liftedCopy_short` works at zero fuel. `liftedCopy_empty` gives identical memory
with one final guard step. One-past empty windows retain live owner/provenance and
representability premises but need no mapped byte at the empty pointer.

`writeWindow` is generic logical-array writeback. These are **final-state** memory
claims, not an instruction/read/write trace or proof that no equal-value store
occurred. `observes_with_frames` composes an explicitly supplied exact caller/
callee frame list only after a target proves agreement outside it and separation
from both windows. It does not infer those frames, target fuel, SP restoration,
return behavior, or callee-saved-register preservation.

`NativeResultWords` models the two actual u32 fields observed by the frozen
production specialization/layout test: `(0,count)` for Ok, `(1,0)` for the sole
Err. `decode_exact` rejects invalid outer and nested error tags.
`observed_words_exact` quantifies arbitrary observed words, **conditional on a
target proving they decode to the lifted returned Result**. Neither that premise
nor register/byte/endian transport follows from an encoding round trip.

## What is tested or remains open

The source fixture, real stdlib dependency bytes, existing extraction, and frozen
production layout-test source are hash-bound. The Go gate freshly regenerates
the bytes extraction. The exact required suite reruns actual package/type/call
resolution, ARM64/RV64 direct-call **shape** and layout observations, current
OptIR/Wasm refusals, and 21 C/interpreter memory fixtures. Hashes and finite tests
are not source/frontend/extractor/compiler refinement proofs.

`callerObservation` is an explicit transliteration of the frozen caller's match;
its source/extractor correspondence and actual retained-value transport remain
open. No admitted copy artifact, source-to-OptIR theorem, target execution, native
or Wasm memory ABI execution, external Sail/Core bridge, or full compiler proof
is established. Current OptIR/Wasm refusal expectations remain unchanged.

## Equipped gate

The existing Lean-equipped `formal.yml` job runs:

```sh
OAK_REQUIRE_STATEFUL_COPY_LEAN=1 \
  python3 .github/scripts/required_backend_tests.py stateful-copy
```

This requires all **7** exact test/subtest names, including fresh extraction and
proof, both native shape lanes, source closure, refusals, and C/interpreter cases;
missing tests, nested skips, and package/process failures fail the gate. No new
toolchain installer is introduced. The optional developer test fails rather
than skips when the required environment flag is set.

The isolated proof checker is also callable directly:

```sh
python3 -B -m unittest discover -s tools/stateful_copy_proof -p test_check.py
python3 -B tools/stateful_copy_proof/check.py --lake /path/to/pinned/lake
```

It reuses the existing Wasm-module gate's dependency walker and strict axiom
parser, but has its own exact root inventory and source bindings. It builds all
**5** local modules fresh under a new `LEAN_PATH`, Lean 4.33.1, trust zero, one
thread, and a 1,600 MiB Lean limit; no candidate olean cache is accepted. It then
checks all **33** public adapter/control theorem roots with only `propext`,
`Quot.sound`, and `Classical.choice` permitted. Source bytes are rehashed after
checking. The full aggregate library imports the adapter; this focused gate does
not claim to freshly build the entire library.

The 16 kernel-checked controls include a family of genuinely inhabited window
invocations, nonzero offsets and zero/high bytes, same-owner disjoint windows,
short-at-zero-fuel, unmapped one-past empty pointers, and rejection of overlap,
dangling empty owners, uninitialized memory, wrapping endpoints, malformed
Result tags, wrong retained length/count, corrupted destination contents, and
insufficient success fuel, plus explicit scratch composition.
