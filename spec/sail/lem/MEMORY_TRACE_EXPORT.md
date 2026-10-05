# Original prompt requests checked by the Lean projector

`memory_trace_export.ml` observes the actual prompt constructors emitted by
Sail's generated `Oak_memory.__WriteMemory`. It records the register name,
selector response, plain effective-address/data requests, byte payload, and
acknowledgement. It supplies fixed test responses, requires normal completion
with every response consumed, and replays the observations with the original
`runTrace`. Unexpected requests, failure, or a request-budget overrun abort
before any report is printed; no event is filtered out or deduplicated.

Two fixtures each issue two writes at address 4096: zero followed by a distinct
value with true/false acknowledgements, and identical repeated writes with
undefined selector bits. Undefined bits retain their own encoding, not zero.
The first fixture's false acknowledgement deliberately demonstrates that
prompt completion is not successful state replay or memory commitment.

`TestSailLemMemoryTraceProjection` builds this adapter against the same audited
Arm declarations and source-pinned Sail/Lem runtime as the existing request
oracles. It parses a bounded, versioned format without accepting raw Lean
expressions, compiles the existing `MemoryEventProjection.lean` in a private
directory, and kernel-checks both exported traces against independent expected
calls and complete occurrences. Ordinary `by decide` and exact `[propext]`
axiom guards are used, not `native_decide`, `sorry`, or an external proof axiom.
The test requires the checked-in Lean 4.33.1 pin, installed via elan before
running the test. It does not automatically download a missing toolchain.

Negative controls reject malformed exports and dropped, duplicated, reordered,
or altered observations, including collapsed identical calls and undefined
selectors coerced to zero. Four mutations of the actual Sail wrapper are also
generated and compiled: bypassed selectors/extra writes must fail the export;
wrong addresses/data must fail the kernel check, not compilation. The original
99-check request suite still uses its own harness after sharing the build helper.

Run with Sail 0.20.2, libsail 0.20.2, Lem 2026-05-01, OCaml, and the pinned
Lean installed via elan:

```sh
OAK_REQUIRE_ORACLES=1 go test ./asm \
  -run '^TestSail(LemMemoryExportParser|LemMemoryTraceProjection|LemWriteMemoryTraces|MemoryEffectFragmentExactAndMutated)$' \
  -count=1 -v -timeout=10m
```

The `lem-ram-traces` CI job requires these checks; missing tools cannot turn
that job into a successful skip. The Lean projector imports only `Std`, so
this check does not need the complete Sail Lean package or its support checkout.

Local validation on 2026-10-05 (Darwin/ARM64): ten targeted Go tests passed with
oracles required, including 22 malformed-export controls, nine kernel-negative
trace controls, and four generated-source mutants. The existing 80 RAM,
99 wrapper, and 84 state-replay assertions still pass. All seven Stateright
tests also passed with locked/offline dependencies. Formatting, whitespace,
and workflow YAML/gate checks passed; these are not remote CI results.

## Trust boundary

This connects an **executable original-model request sample** to a
kernel-checked concrete projection. The OCaml observer, serializer, Go parser,
code generator, Sail/Lem translations, compilers, and runtime are not verified
by that projection. Source audits and mutation tests do not prove those tools.
It is not a universal trace-production/refinement theorem or a kernel-verified
raw Lem importer. `DONE` is an adapter assertion, not a Lean execution proof.

These remain plain request occurrences, not CAT W/TTD events. No descriptor
classification, full instruction execution, translation, fault handling,
coherence, visibility, DSB/TLBI completion, or architectural publication follows.
Nor do these fixtures implement the Stateright protocol's assumed contracts.
The Stateright-to-Sail/CAT relation and those contracts remain open. No compiler
pin, production lowering, strict admission rule, or optimizer permission changes.
