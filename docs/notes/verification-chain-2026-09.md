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
| Instruction semantics, RV64 | the term semantics | — | `Oak.RiscV` ≡ the Sail RISC-V definitions restated verbatim (`Oak.SailRiscVBridge`, 14; `asm/rv64_sail_bridge_test.go` fails on drift) | QEMU and the Sail C emulator on the same units | the restatement: the export does not compile under Sail 0.20.2, so the theorems are not yet against the import (`spec/lean-sail/README.md`) |
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
   Debian spelling as well as Homebrew's. Still outside CI: the ISA XML
   audit (Arm's license) and the RV64 bridge against the export (item 2).
2. **The RV64 bridge proves against a restatement.** `Oak.SailRiscVBridge`
   restates the library and prelude definitions verbatim because the Sail
   0.20.2 export does not compile. Building Sail from git (as sail-riscv's
   own CI does) and compiling `spec/lean-sail` turns the restatement into
   an import; the drift test keeps the restatement honest until then.
3. **The encoder is tested, not proved.** Both Sail models carry decoders
   (sail-riscv's `encdec` mappings; Arm's decode tree). The natural
   connection is a round-trip theorem, `decode (encode i) = i`, for every
   instruction form the encoder emits — stated against the generated
   Lean for RV64 first (the mappings export cleanly), then for AArch64.
   That would make the machine words, not only the semantics, a
   consequence of the Sail specification.
4. **Calls are the largest trusted class.** The verifier does not model
   `bl`/`call`: 159 of 304 trusted AArch64 bodies and 119 of 295 on RV64
   are trusted for that reason alone. `oak prove` already inlines
   same-shape callees at the term level; giving the verifier the same
   callee inlining (or a proved summary of the callee's own verdict) would
   move most of them to proven.
5. **The extents decision procedure is not refined.** Each rule cites its
   law in `Oak.Extents`, but the Go procedure is not proved to decide the
   laws, as `Oak.ReborrowRefinement` does for reborrow admission. An
   `Oak.ExtentsRefinement` over the fact kinds (`factUpperBound`,
   `factIndexLit`, the conditional-minimum rule) is the same shape of
   work. The same holds for the seam checkers' new facts (frame element
   regions, span aliases, composites), recorded as proof debt in STATUS.
6. **The checkers are linear over the block.** Base facts (spans,
   regions, frame addresses) are definitions, not per-path state; guard
   facts already flow through labels by a fixpoint on AArch64. The two
   remaining AArch64 refusals (`text_fold_next`, `utf8_to_utf16_bytes`: a
   span base copied into another register across a label) and the
   backend discipline of §3.2 both come from this. Making base facts part
   of the label state removes the discipline and the refusals.
7. **The object and executable writers have no laws.** Their arithmetic
   (section offsets, relocation ranges, program-header extents) is
   checked at run time and tested against llvm-objdump and QEMU; the
   `Oak.Assembler` frame laws are the model for stating them in Lean.
8. **amd64.** Only through a lane. Until then, amd64 binaries are the C
   compiler's, checked by the differential corpus alone.

## 5. How to reproduce the tally

```
go build -o /tmp/oak . && OAK_NATIVE_DUMP=1 /tmp/oak build -native -target linux/riscv64 -o /tmp/sb examples/stdlib_builder.oak 2>&1 | grep -c 'proven equal'
```

The diagnostics name every verdict (`proven equal`, `agrees with its Oak
body on every witness input`, `not verified (...)`, `left to the C backend
(...)`, `the checker refuses the lowering of ...`); `OAK_NATIVE_DUMP=1`
prints each lowered body as the checker sees it.
