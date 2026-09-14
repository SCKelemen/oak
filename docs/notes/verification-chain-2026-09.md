# The verification chain, source to object: an audit (2026-09-13)

The question: is Oak specified and verified all the way from source to
object and assembly, and are the source-level proofs connected to the
Sail ISA specifications? This note records what stands at each stage
today, what the audit measured, what it broke open, and what is missing,
in the order it should be closed. It is the companion of
`docs/spec/94-assembler.md` §8–§9 and `docs/spec/125-verification.md`.

A word on architectures. Oak has two assembler lanes, AArch64 and RV64.
The Sail models are Arm's (`sail-arm`, generated from Arm's ASL) and
RISC-V's (`sail-riscv`, the ratified golden model). There is no amd64
lane: amd64 targets compile through C only, and no Sail connection exists
or can exist for them until a lane does (REMS's `sail-x86` is partial).
"Arm and RISC-V" is what the chain below covers.

## 1. What stands at each stage

| Stage | Artifact | Decision procedure | Mechanical ground | Oracle | What is trusted |
| --- | --- | --- | --- | --- | --- |
| Theorems in source | `name: theorem (params) { Bool }` | `oak prove`: exhaustive; bit-level over the verifier's term language; Lean over the extraction | `decided` shares the term semantics of `Oak.AssemblerSemantics` (below); `proved` is Lean on `95-extraction.md` | the interpreter is the exhaustive decider's evaluator | the extraction's modeling choices, stated in `95-extraction.md` §3 |
| Types, borrows, extents | the checked tree; `IndexProven` facts | Go decision procedures in `typechecker/` | laws in Lean: `Oak.Extents` (35 theorems), `Oak.Borrowing`, `Oak.Reborrow`; refinements of the admission procedures in `Oak.ReborrowRefinement`, `Oak.ViewRefinement`, `Oak.BorrowStateRefinement` | the differential corpus (compiled C against the interpreter) | the extents decision procedure itself: each rule cites its law, none is refined |
| Lowering to asm | `asm.Function` per body (`nativegen`) | the seam checker (`asm/check.go`, `asm/rv64_check.go`) and the verifier (`asm/verify.go`), per function | checker laws in `Oak.Assembler` (24), `Oak.RiscV` (54); verifier semantics `Oak.AssemblerSemantics` (64) | the C backend under `OAK_PORTABLE_INTRINSICS`; the differential corpus | bodies the verifier labels trusted (§2), the checker's and verifier's own code as transliterations |
| Instruction semantics, AArch64 | the term semantics | — | `Oak.AssemblerSemantics` ≡ `Oak.ArmASL` (19) ≡ Sail-generated Lean (`spec/sail/lean/Bridge.lean`, 17 bridge theorems) | the silicon differential: 181 bodies × 60 inputs on an M-series core | the Go executor is a transliteration of the Lean, checked on the silicon, not extracted |
| Instruction semantics, RV64 | the term semantics | — | `Oak.RiscV` ≡ the Sail RISC-V model's Lean export (`spec/lean-sail`, 15 theorems against the imported prelude operators; `Oak.SailRiscVBridge` keeps the verbatim restatement, 14, and `asm/rv64_sail_bridge_test.go` fails on drift) | QEMU and the Sail C emulator on the same units | the `execute_*` bodies are read by inspection: the export's whole library still does not compile (`Vmem`, rems-project/sail#1729), so the bridge imports `LeanRV64D.Prelude` (`spec/lean-sail/README.md`) |
| Encoding | machine words | table-driven encoders from Arm's ISA XML and riscv-opcodes | `Oak.Assembler` frame/align laws; `Oak.RiscV` RVC immediates | llvm-mc (2471 fuzzed encodings, 254 SVE/SME spellings), `riscv64-elf-as` on every mnemonic, the Sail decoder audit (`asm/sail_coverage_test.go`), the ISA XML operand audit | the encoder's bytes: tested against two assemblers, not proved against a decoder |
| Object and executable | ELF/Mach-O relocatable objects, static ELF executables | `asm/object.go`, `asm/executable.go` | — | llvm-objdump/nm on the objects; QEMU runs the executables on both lanes | the writers, by construction ("every offset computed and checked") |

Two things that are mechanically closed today: Arm's ASL → Sail → Lean ≡
`Oak.ArmASL` ≡ `Oak.AssemblerSemantics` (proved), and the source-level
`decided` rung resting on exactly those semantics. So a theorem the
bit-level decider proves is proved against Arm's own instruction
semantics, and the verifier's proof that a lowered body equals its Oak
body is a proof in the same semantics.

## 2. What the audit measured

Every function a stdlib-bearing program carries (`examples/stdlib_builder.oak`,
about six hundred bodies including the standard library) was run through
the native backend on both lanes, tallying the verdicts. Before the fixes
of §3 the build failed closed on both lanes.

| Lane | Proven | Witnessed | Trusted | Left to C | Checker refused | Verifier refuted |
| --- | --- | --- | --- | --- | --- | --- |
| AArch64, before | 87 | 3 | 280 | 88 | 68 | 3 |
| AArch64, after | 92 | 5 | 304 | 88 | 2 functions | 0 |
| AArch64, after call summaries and the last two | 101 | 13 | 305 | 93 | 0 | 0 |
| RV64, before | 36 | 3 | 264 | 156 | 165 | 0 |
| RV64, after | 38 | 3 | 295 | 156 | 0 | 0 |

Why bodies are trusted rather than proven (AArch64, after): a call (`bl`)
in the body 159; a record result beyond one register chunk 42; vector or
non-integer parameters 37; more paths than the budget 16; `strb` 12; a
load from a frame slot never stored on the path 11. On RV64: a call 119;
vector or non-integer parameters 84; a record result beyond one chunk 29;
a load whose width differs from the slot's store 29.

Why bodies are left to C (RV64): an `i32` element index 23; an expression
statement that is not a call 13; a call to `is_valid_utf8` 11; record
parameters and locals of shapes the lane does not place yet.

## 3. What the audit broke open, and closed

Every finding was a fail-closed rejection of the build, never a wrong
binary — the chain worked. Each was a defect in the backend, the checker,
or the verifier, not in the program:

1. **The verifier refuted correct code.** A Bool field is a 1-bit leaf in
   the composite model; `recordBytes` rounded its width to zero bytes, so
   a Bool at the start of a copied 8-byte word fell out of the window and
   read as zero. `!parsed.scheme.present` (`url_is_relative`),
   `url_is_absolute`, and `filter_config_valid` were refuted. Fixed in
   `asm/verify.go`; pinned by `compiler/e2e_native_bool_field_test.go`.
2. **Result registers written inside arms.** Both lanes lowered each arm
   of a result conditional to write `x0`/`a0`. The checker is linear:
   the write forgot the parameters' span and record facts for every arm
   after it, so a later arm's element access through the parameter was
   refused. Arms now meet in one scratch register (a frame temporary for
   a record result) and the result register is written once at the join
   (`resultInto`, `resultRecordInto`, both lanes).
3. **Undefined scratch registers spilled around calls.** A register
   allocated for a value not yet computed was stored before a `bl`, a
   read the checker knows is uninitialized. Only defined registers spill;
   every emission path marks its destination (`markDefined`, `put`).
4. **By-reference regions forgotten on RV64.** The region of a record
   parameter arriving by reference was dropped at the first
   guard-forgetting point when a later arm writes its register; it now
   holds until the register is written on the path (`rvRegion.param`).
5. **The second result chunk refused on AArch64.** The checker required
   `x1` at `ret` for a two-chunk record result and refused writing it
   without a clobber; the second chunk is a result register.

## 4. What is missing, in the order to close it

1. **CI does not check the Sail links.** `formal.yml` builds `spec/lean`
   (160 jobs, passing). Not in CI: `spec/sail/lean` (the Arm bridge; needs
   the lean-sail checkout of `spec/sail/setup.sh` and `sail` for the
   regeneration test), `spec/lean-sail` (the RV64 bridge against the
   import), the Sail RISC-V emulator differential (`external/sail-riscv`),
   the Sail decoder audit (the `sail-arm` model), and the ISA XML audit
   (Arm's license forbids redistribution). Every one skips silently when
   its input is absent, so the links are checked only on a developer's
   machine that has them. **Closed (2026-09-13):** `.github/workflows/formal-sail.yml`
   fetches every input pinned — the Sail 0.20.2 binary release and the
   sail-riscv 0.14 emulator by checksum, Arm's decode tree by commit,
   lean-sail by `setup.sh`'s revision — builds the Arm bridge with lake,
   and runs the oracle tests with `OAK_REQUIRE_ORACLES=1`, under which an
   absent oracle fails the test instead of skipping it
   (`asm/oracles_test.go`). The RISC-V GNU tools resolve under their
   Debian spelling as well as Homebrew's. **The RV64 bridge joined
   (2026-09-14):** a second job of `formal-sail.yml` generates the export
   from the pinned sail-riscv release with the pinned Sail, repairs it
   (`spec/lean-sail/patch-export.py`), builds it, proves `spec/lean-sail`
   against it, and runs the bridge tests with the export required; the
   built export is cached by its pins. Still outside CI: the ISA XML audit
   (Arm's license).
2. **The RV64 bridge proves against a restatement.** `Oak.SailRiscVBridge`
   restates the library and prelude definitions verbatim because the Sail
   0.20.2 export does not compile. Building Sail from git (as sail-riscv's
   own CI does) and compiling `spec/lean-sail` turns the restatement into
   an import; the drift test keeps the restatement honest until then.
   **Attempted, then closed (2026-09-13):** Sail built from git in its own
   opam switch (`sail-dev`, every Sail package pinned) generates the export
   from sail-riscv 0.14; it fails to compile in the generated `Defs.lean`
   (`PTW_Output` over a `pte_bits` the Lean backend left in Sail syntax,
   rems-project/sail#1729) and then in `Vmem.lean`. The fix is upstream's,
   but a pinned repair is not: `spec/lean-sail/patch-export.py` restates
   the seven virtual-memory type sites and, in `Vmem`, three shadowed type
   synonyms and the two-stage translation's termination measure — nothing
   about instruction semantics — and the whole export builds. `spec/lean-sail`
   then proves against the import: the data theorems, and the
   `execute_RTYPEW`/`execute_RTYPE`/`execute_BTYPE` bodies rewritten to
   Oak's canonical form through the monad laws (`OakSailBridge/Execute.lean`).
   `TestRV64SailBridgeBuilds` and `TestRV64SailBridgeStubsMatchSail` run
   instead of skipping; the patch goes when upstream fixes #1729. Also
   closed the same day: rv64 translation validation had skipped silently
   in `ci.yml` (the RISC-V GNU toolchain was installed only in
   `formal-sail.yml`); the `packages` shard now installs it,
   `TestTranslationValidationRV64` accepts the Debian spelling, and
   `OAK_REQUIRE_RV64_GCC=1` turns the skip into a failure there.
3. **The encoder is tested, not proved.** Both Sail models carry decoders
   (sail-riscv's `encdec` mappings; Arm's decode tree). The natural
   connection is a round-trip theorem, `decode (encode i) = i`, for every
   instruction form the encoder emits — stated against the generated
   Lean for RV64 first (the mappings export cleanly), then for AArch64.
   That would make the machine words, not only the semantics, a
   consequence of the Sail specification. **Stated (2026-09-13):**
   `Oak.RiscV.Enc` restates the encoder's placement and the decided
   mnemonics' table entries (held to the Go table by
   `asm/rv64_encoding_lean_test.go`), and
   `spec/lean-sail/OakSailBridge/Encoding.lean` states thirty theorems
   `encdec_forwards (instruction) = pure (encode …)` against the export.
   **Checked (2026-09-14):** with the export compiling (item 2) all thirty
   prove. Meeting the export corrected them: `encdec_forwards` and the
   operand mappings live in `LeanRV64D.Functions`; the four-thousand-line
   match unfolds once rather than through per-clause equations; `congrArg
   pure` replaces `congr` on the monadic result (the word's width is a
   nest of `hi - lo + 1` sums); and the six branch theorems were false as
   stated — the model encodes a branch only for an even offset and errors
   otherwise, so they carry the evenness as a hypothesis. The encoder is
   now proved against the ISA's `encdec` for the decided RV64 mnemonics;
   AArch64's remains tested.
4. **Calls are the largest trusted class.** The verifier did not model
   `bl`/`call`: 159 of 304 trusted AArch64 bodies and 119 of 295 on RV64
   were trusted for that reason alone. **Closed (2026-09-13):** the
   verifier takes a call to a program function with a scalar signature
   at the callee's Oak body (`94-assembler.md` §9, "Call summaries"), on
   both lanes, and names the callees so taken in the verdict. `bl` is no
   longer a trusted reason; what remains trusted after it is record
   results beyond one chunk, vector and floating-point parameters, the
   path budget, stores through spans (`strb`), and callees returning
   `()`. The model exposed a latent ABI gap: the AArch64 lane read a
   narrow call result straight from `w0`, relying on the callee's
   zero-extension that AAPCS64 does not promise; the caller now
   normalizes it.
5. **The extents decision procedure is not refined.** Each rule cites its
   law in `Oak.Extents`, but the Go procedure is not proved to decide the
   laws, as `Oak.ReborrowRefinement` does for reborrow admission. An
   `Oak.ExtentsRefinement` over the fact kinds (`factUpperBound`,
   `factIndexLit`, the conditional-minimum rule) is the same shape of
   work. **Closed for the discharge (2026-09-13):**
   `spec/lean/Oak/ExtentsRefinement.lean` transliterates `indexUnder` and
   proves `indexUnder_sound`; the fact extraction and kills remain
   transliterations with laws. **Pinned (2026-09-14):** the Go decision is
   rendered against the Lean model's examples
   (`typechecker/extents_refinement_test.go`), as the lowering seam is. The seam checkers' new facts (frame element
   regions, span aliases, composites) remain proof debt in STATUS.
6. **The checkers are linear over the block.** Base facts (spans,
   regions, frame addresses) are definitions, not per-path state; guard
   facts already flow through labels by a fixpoint on AArch64. The two
   remaining AArch64 refusals (`text_fold_next`, `utf8_to_utf16_bytes`)
   and the backend discipline of §3.2 come from this. **Closed for those
   two (2026-09-13):** a calling value is evaluated before its target
   place, frame addresses and constants parked in callee-saved registers
   survive calls, constants join the label fixpoint, and a compare
   against a register holding a known constant is a constant guard
   (`94-assembler.md` §9, "The last two refusals"); the stdlib-bearing
   program now builds natively on both lanes with no refusal. Base
   facts through spills and spans copied across labels remain outside
   the label state.
7. **The object and executable writers have no laws.** Their arithmetic
   (section offsets, relocation ranges, program-header extents) is
   checked at run time and tested against llvm-objdump and QEMU; the
   `Oak.Assembler` frame laws are the model for stating them in Lean.
8. **amd64.** Only through a lane. Until then, amd64 binaries are the C
   compiler's, checked by the differential corpus alone.
9. **A real program all the way down.** `oak build -link oak` links a
   program from the Oak assembler alone, so every body and every global
   must be native. Measured on the stdlib-bearing program
   (2026-09-13): the first refusal was its first global. **Closed for
   globals (2026-09-13):** constant tables live in the object's
   read-only data and are addressed by `adrl`/`la` under both checkers
   (`94-assembler.md` §9, "Constant tables"); constant scalars are
   folded; statement-position and chained conditionals and `i32`
   indices lower natively ("Statement conditionals and `i32` indices").
   The link now names what is left: 36 bodies on AArch64 (`is_valid_utf8`
   in a bare build, more than eight parameters or span parameters past
   the argument registers, span values chosen by a conditional, a record
   local without an initializer) and 120 on RV64 (local spans and views,
   span-of-record parameters, expression depth past the scratch
   registers, calls through a value, floating-point record results).
   **The verified profile (2026-09-14):** `oak build -verified` refuses
   any witnessed, trusted, or C body and prints the burn-down list
   (`94-assembler.md` §9, "The verified profile"). Its first day closed,
   on both lanes: record results of two chunks, calls returning or taking
   records and sum types, span arguments to summarized calls, table reads
   as span elements, frame bytes no store reached, RV64 record
   parameters, RV64 byte-granular frame slots, and RV64 stores through
   spans as memories; and it found the decision had to be over well-typed
   union tags. The stdlib-bearing program went from 115 to 151 proven
   bodies on AArch64 and from 42 to 149 on RV64, with no mismatch. What
   led the list next: the path budget, which was mostly loops whose exit
   tests read memory or call a program function; those are recognized and
   summarized now (`94-assembler.md` §9, "Exit tests that read memory",
   "Calls and spills inside loops"), and the path-budget bodies fell from
   71 to 21 on AArch64 and from 58 to 10 on RV64, with 166 and 160 bodies
   proven. Then the span memory through the loop summary landed ("Span
   memories through loops"), with the loop proof's budgets that keep the
   prover's native build bounded: 176 and 167 proven, no mismatch. What
   leads the list now: vector and floating-point parameters (outside the
   scalar profile by design), results past 16 bytes returned through
   memory, unit callees whose bodies assert, the path budget (loops that
   call functions with memory effects), and the witnessed verdicts — Bool
   loop variables the coupling finds no register image for, and bodies
   past the bit-level node budget.

## 5. How to reproduce the tally

```
go build -o /tmp/oak . && OAK_NATIVE_DUMP=1 /tmp/oak build -native -target linux/riscv64 -o /tmp/sb examples/stdlib_builder.oak 2>&1 | grep -c 'proven equal'
```

The diagnostics name every verdict (`proven equal`, `agrees with its Oak
body on every witness input`, `not verified (...)`, `left to the C backend
(...)`, `the checker refuses the lowering of ...`); `OAK_NATIVE_DUMP=1`
prints each lowered body as the checker sees it.
