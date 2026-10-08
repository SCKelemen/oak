# Same-kernel fetched-byte bridge

This isolated project uses Lean 4.29.0, the original generated RV64 model's
pinned toolchain. Its `srcDir` entries compile the repository's exact Oak,
source checker, framed-body and external-composition files into a separate
cache. It does not copy or substitute their definitions and does not infer
compatibility between separately checked Lean versions. The canonical core
and bounded execution composition keep their Lean 4.33.1 toolchain.

The generated `Fetch` module imports `FetchRvfi`, which imports `RvfiDii`,
even though this profile sets RVFI off. Two unchanged-source 4.33 builds of
`RvfiDii` were stopped for resource pressure without producing an artifact.
The second used raw `lean -o`, no C or interface output, one thread and
synchronous elaboration; sampled RSS reached about 5.67 GiB. This is a local
resource limitation, not evidence of a semantic or kernel incompatibility.
The original complete 4.29 model and its `Fetch` module are already built.

## Boundary

`OakSailFetchedFrame` connects all 36 admitted production function bytes in
actual sequential RAM to the pinned generated `fetch ()` result at each of
nine explicitly chosen PCs. Successful physical reads, PMP/PMA checks and
Machine-mode translation are derived from concrete configuration and byte
membership premises. No assumed fetch-success proposition is used.

The profile is freestanding Machine/Bare, with the precise `MemoryConfig`
from the framed bridge, `misaRV64I`, aligned four-byte instruction addresses,
an executable matching PMA region and each four-byte read below 0x02000000.
This is not an arbitrary Linux user-mode state. Each successful fetch is
proved to leave the complete interpreter state unchanged. No clock tick or
interrupt handling occurs inside this claim.

`FrameCodeAt` requires complete byte placement, four-byte alignment and a
nonwrapping 36-byte interval. `CodeStackDisjoint` excludes both saved eight-
byte stack intervals. The placement theorem derives that the framed stores
preserve every code byte; fetch is then proved again in the final saved-memory
state. Code placement is an abstract RAM premise, not an ELF loader theorem.

The caller explicitly sets PC for each fetch query. Sequential instruction
execution with `try_step`, PC-to-nextPC advancement, interrupt dispatch,
retirement counters and outer-loop clocks remains open. The existing
nine-body execution theorem and these fetch queries do not by themselves
prove a fetched execution loop. Generated Lean semantics are the target;
faithfulness of the Sail-to-Lean exporter remains an external boundary.

## Compatibility

Lean 4.29 lacks the newer `List.splitOn` API. `Oak.ByteFields` uses the same
byte-splitting recursion, shared by both projects. The 4.33 theorem
`Oak.ByteFields.splitOn_library` proves equality with the original API for
all byte lists and separators, including empty and repeated fields.
Framed memory reconstruction reuses the repository's kernel-only shared
byte theorem. These changes preserve source acceptance and theorem statements.

## Audit and reproduction

From the repository root, after restoring/generating the original pinned
export, run:

```
python3 spec/lean-sail433/prepare.py --generated external/sail-riscv/build/model/Lean_RV64D
(cd spec/lean-sail429 && lake update && lake build OakSailFetchedFrame && python3 audit.py)
(cd spec/lean-sail433 && lake build OakSourceSplitCompatibility OakSailFetchedCode)
OAK_REQUIRE_RV64_LEAN=1 go test ./compiler -run '^TestRV64(Framed|Fetched)BitwiseCompilerMatchesLean$' -count=1 -v
```

The original export and support sources retain the exact hashes and provenance
recorded in `../lean-sail433/export-provenance.json`; `prepare.py` verifies them
before either new required CI gate. No generated definitions or imports change.
The 4.29 project checks source grammar, typed-expression meaning, all nine
instruction-body execution and fetch theorems together. Its 13-theorem audit
also verifies the running Lean version and fails on missing/unlisted axioms.
The separate 4.33 check validates shared-source compatibility and the original
source splitter equivalence, rather than serving as an assumed kernel bridge.

Actual fetch closures retain standard `propext`, `Classical.choice`, `Quot.sound`
and these opaque model declarations:

- `plat_term_write.{u} : {α : Sort u} → α → LeanRV64D.SailM Unit`
- `sys_enable_experimental_extensions : Unit → Bool`

The terminal operation is an effectful primitive, not an assumed correctness
proposition. The concrete non-MMIO proof excludes its branch. No terminal
success or particular experimental-extension value is hypothesized. The
imported full framed-body theorem additionally retains the original opaque
`load_reservation : [Arch] → Arch.pa → Nat → SailM Unit` and
`match_reservation : [Arch] → Arch.pa → Bool`, with `Arch.pa = BitVec 64`.
Their unselected branches and precise scope are described in `../lean-sail433/FRAME.md`.
All other audited physical fetch, placement and core-body lemmas admit only
standard Lean dependencies. No native-evaluation or sorry axioms are allowed.

Kernel-checked negative examples cover missing RAM bytes, a non-executable
PMA region, wrapped code placement and code/stack overlap. Existing source and
body checks reject malformed or changed bytes. The mandatory production pin
compiles AND/OR/XOR through the real compiler, extracts the complete function
symbol, rejects any relocation in its extent, and checks both the restricted
original declaration and every extracted byte in this same fetch project.
