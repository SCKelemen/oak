# The verification chain: source to object, per target

Status: an audit of what is proved, refined, audited, tested, and trusted
at each hop from Oak source to a linked object, for every target the
compiler builds, as of 2026-09-13. Nothing here is normative on its own;
each hop names the document and the artifact that hold it. The point of
the map is that a proof about an Oak program is worth exactly what the
weakest hop below it is worth, and that hop differs by target.

## 1. The labels

- **proved**: a Lean theorem over the same definitions the implementation
  transliterates, with the transliteration pinned by a test so that
  either side changing must visit the other (the refinement pattern of
  `Oak.ModulesRefinement`).
- **refined**: the implementation's decision procedure or emitted text is
  transliterated into Lean and proved to meet the specification's rule,
  pinned by a text or table test.
- **audited**: an external, machine-readable specification is walked
  mechanically and every element it names is accounted for (in the table,
  or excluded by name with a reason).
- **differential**: two or more realizations execute the same program and
  must agree bit for bit (interpreter, compiled C, extracted Lean, silicon).
- **trusted**: an assumption the chain rests on without a check of its own,
  named as such (the constitution's visible unsafe boundary).

## 2. The hops

### 2.1 Source → checked program

The type checker, borrow and resource checker, protocol projection, and
discipline analyzers decide what the program means and whether it is
admitted. **Refined**: the type lattice (`Oak.TypeLatticeRefinement`),
pattern analysis and reachability (`Oak.PatternAnalysisRefinement`),
generic constraints, record shape and layout, borrow states and
reborrows, modules, literal ranges (`Oak.LiteralFitRefinement`),
integer conversions, wrapping/checked arithmetic, the view and span
helpers, the atomic order tables and the CAS helper — each row carries R in
`STATUS.md`. **Proved**: typestate (`Oak.Typestate`), protocol
conformance (`Oak.ProtocolConformance`), quorums (`Oak.ProtocolQuorum`),
closure capture, effect rows, UTF-8 validity, the self-hosted laws
(`125-verification.md` §6, decided in Oak and proved in Lean).
**Trusted**: the parser and the checker's code outside the refined
decision procedures; the module loader beyond `Oak.ModulesRefinement`.

### 2.2 Checked program → lowered program

`try`, closures, quantifier forms, protocol declarations, derived codecs
and the memory-model selection are rewritten into ordinary Oak before the
backends see them. **Proved** where the rewrite has a model (typestate,
quorums, the shift-DFA lowering, the monitor's projection);
**differential** everywhere: the interpreter runs the checked program and
the compiled C runs the lowered one, and every e2e test compares them.
**Trusted**: the rewrites' Go code.

### 2.3 Lowered program → C

**Refined**: the trusted core the generated prelude carries — total
arithmetic (`Oak.ArithmeticRefinement`), checked/saturating/trapping
arithmetic and shifts, the explicit conversions, view/span/owned-array
guards, the strong compare-exchange, natural struct layout, the memory
order tables — is transliterated and proved to `20-types.md` and
`65-machine-memory.md`, pinned to the emitted text. **Proved**: the C11
mapping of Oak's orders on AArch64 and RVWMO (`Oak.AArch64Memory`,
`Oak.RiscVMemory`, `Oak.RVWMO`), with the instruction families clang emits
pinned by the refinement tests. **Differential**: the golden corpus, and
every e2e program against the interpreter; the extracted Lean of the
self-hosted checkers against compiled Oak (`OakTextCompare`, 729 cases).
Evaluation order is now sequenced by the backend (`10-syntax.md` §3d,
`90-backend.md` §15) and held by a differential of its own. **Trusted**:
the rest of the C emitter — statement and expression lowering outside the
refined helpers has no semantic model; its evidence is differential.

### 2.4 C → object

The system C compiler (`toolchain.Resolve`: the host `cc`, `zig cc`, a
cross `clang`, or a GNU prefix) is **trusted**. Nothing in the repository
checks the machine code a C compiler produces for Oak's C, except: the
memory-refinement tests read clang's assembly for the atomic families on
`rv64gc` and AArch64, and every differential test executes the object. The
driver selection itself is **proved** (`Oak.Target`: lane and object
format as functions of the target, LP64 or ILP32, `OAK_CC` precedence,
zig resolving every target from any host).

### 2.5 Asm units and native bodies → machine words

Two lanes bypass the C compiler for the functions they cover: `.oakasm`
units (`94-assembler.md` §7) and the native backend (`nativegen`, `oak
build -native`), whose output is a unit like any other. For both, the Oak
body is the specification and the assembler verifier decides the unit
against it (§8): a **proof** when the two terms have one linear normal
form or the bit-level decision closes, **evidence** when a witness set
agrees, **trusted** when the unit reaches outside the decided subset
(labels, calls, memory off the frame, system instructions) — every verdict
labeled. Then the assembler encodes the words itself (§9) and writes the
companion object; the object format and lane are those of `Oak.Target`.

### 2.6 Object → binary

Linking is the C compiler's driver (`compileC`), static for Linux cross
builds, with the manifests' `link`/`framework` inputs and the realization
shims. **Trusted**; **differential** through `oak run -target` under
QEMU where present.

## 3. Per target

| Target | Source → C | C → object | Asm/native lane | ISA semantics the lane is held to | Encoding | Execution check |
| --- | --- | --- | --- | --- | --- | --- |
| linux/arm64, darwin/arm64, freestanding/arm64 | refined core + differential | trusted (cc) | arm64: verifier proof/evidence/trusted | **proved to Arm's ASL**: `Oak.ArmASL` transliterates the Sail Armv8.5-A primitives with the Sail text beside each, proved equal to `Oak.AssemblerSemantics`; the hand transliteration is proved against Sail's mechanically generated Lean (`spec/sail/lean/Out.lean`); the decode tree **audited** (`asm/sail_coverage_test.go`), operand forms audited against the A64 ISA XML | table **generated from the ISA XML**, checked against `llvm-mc` | silicon **differential** (181 bodies × 60 inputs on the host core) |
| linux/riscv64, freestanding/riscv64 | refined core + differential; RVWMO mapping proved | trusted (cc) | rv64: same verifier, RISC-V semantics (`Oak.RiscV`) | **bridged to the Sail RISC-V model** for `RTYPE`, `RTYPEW`, `BTYPE` (`Oak.SailRiscVBridge` restates the export's primitives verbatim, a Go test keeps the copies honest against the fetched sources); loads, stores, AMOs, `auipc`, calls are outside the decided subset; the Lean-against-export project (`spec/lean-sail`) waits on a Sail newer than the opam release | own encoder (`rv64_encodings_gen`) checked against GNU `as`; RVC | `qemu-system-riscv64` where present |
| linux/amd64, darwin/amd64, freestanding/amd64 | refined core + differential | trusted (cc) | **none** (`Oak.Target.lane = none`) | **none**: no Oak semantics of x86-64 and no bridge to a machine-readable x86 specification | none | host execution (differential) |
| freestanding/arm (Cortex-M), freestanding/riscv32 | refined core + differential; ILP32 proved | trusted (cc) | none | none (Arm's M-profile ASL is not public; `docs/notes/oak-cortex-m-deferred`) | none | cross build only |

## 4. Where source-level proofs connect to the ISA today, and where not

A theorem about an Oak program (`oak prove`, or the Lean extraction of
`95-extraction.md`) is a statement about Oak's semantics: the
interpreter's, and the shallow embedding's (fixed-width integers as Lean
`UInt`s with the same wrapping). For a function the native lane realizes,
the verifier proves the emitted instructions equal to *its own* lowering of
the Oak body into the term language of `Oak.AssemblerSemantics`, and that
language's instruction semantics are proved to Arm's ASL. The chain from a
source theorem to the machine therefore has one **unproved seam**: nothing
in Lean states that the verifier's Oak lowering (Go, `asm/verify.go`,
"under Oak's total wrapping arithmetic") and the extraction's embedding
agree. Both transliterate `20-types.md` §11.1, both are held to it by
tests, and `Oak.ArithmeticRefinement` proves the C helpers meet it — but
the term language and the embedding are not related by a theorem. That is
the smallest addition that would make "source theorem ⇒ machine behavior"
one proof on the arm64 lane.

For the C route (every function the native lane does not cover, and every
function on amd64 and the microcontrollers), the source-level proofs reach
the C text through the refinements of §2.3 and stop at the C compiler.

## 5. What would extend the chain, in order of leverage

1. **Close the seam** (§4): a Lean module relating `Oak.AssemblerSemantics`'s
   term lowering of an Oak expression to the extraction's embedding for
   the shared subset (arithmetic, comparisons, conversions), pinned by a
   test on the verifier's lowering.
2. **Validate the C compiler's output for the trusted core**: compile the
   prelude helpers (`oak_add_u32`, the conversions, the CAS helper) to
   assembly on arm64 and rv64 and run them through the existing verifier
   as units whose Oak body is the helper's specification — translation
   validation of exactly the helpers the refinements prove, with no new
   machinery.
3. **Finish the RISC-V bridge**: build `spec/lean-sail` against a Sail
   built from git so the theorems are checked against the export itself
   rather than verbatim copies; extend the decided subset to loads and
   stores through the frame and to the AMOs the memory refinement already
   pins.
4. **An amd64 lane and an x86 semantics**: the native backend's third lane,
   with instruction semantics bridged to a machine-readable x86-64
   specification. The candidates are the Sail x86 model (REMS; partial),
   the ACL2 `x86isa` model (Intel-validated and comprehensive, but in
   ACL2, so the bridge would be a verbatim restatement checked by a test,
   as the RISC-V bridge is today), and Intel XED as the decode/encode
   audit oracle in the role `llvm-mc` and Arm's XML play for arm64. Until
   then amd64 is a C-only target and its chain ends at the compiler.
5. **The microcontrollers**: wait on Arm's M-profile ASL
   (`docs/notes/oak-cortex-m-deferred`); rv32 can follow rv64's lane once
   the psABI differences are stated.

## 6. Reading the map

Every "trusted" entry is a place where a bug would not be caught by a
proof, only by a differential test or by execution. The two that matter
most for a formally specified operating system are the C compiler (§2.4)
and the unmodeled part of the C emitter (§2.3): the native lane exists to
remove both from the path of the functions that matter, and it removes
them today for arm64 and, for the decided subset, rv64. On amd64 nothing
removes them yet.
