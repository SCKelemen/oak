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
helpers, the alignment-fact normalization/flow/join decisions
(`Oak.AlignmentFactRefinement`), the atomic order tables and the CAS helper —
each row carries R in `STATUS.md`. **Proved**: typestate (`Oak.Typestate`), protocol
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
`rv64gc` and AArch64; the trusted core is **translation-validated**
(`codegen/translation_validation_test.go`): the prelude's total-arithmetic
and conversion helpers — the text `Oak.ArithmeticRefinement` and
`Oak.ConversionRefinement` prove — are compiled by clang for arm64 and by
GCC for rv64, and each function runs through the assembler verifier (§2.5)
as a unit whose Oak body is the helper's operator, so for these helpers
the compiler's output is checked, not trusted (add, sub, neg, the
conversions and the checked shifts at the constant counts 1, 3 and
width − 1 proven — the count below the width, the helper's trap check
folds away and the verifier admits the constant shift — multiplication
witnessed, division and remainder decided through the uninterpreted
quotient (`94-assembler.md` §8, the thirty-first increment): the 32- and
64-bit quotients and every remainder proven structurally, the narrow
quotients (computed at 32 bits by the helper, at 8 or 16 by Oak) and the
signed ones behind the `MIN / -1` arm witnessed, since a bit-level
counterexample the diagrams raise for two applications of an
uninterpreted quotient and the evaluation refutes is the abstraction's,
not the terms' (`blastEqual`), and the machine's zero-divisor trap path
leaves the input domain (`pathEffects.trap`); the guarded element read
`oak_index` over a
`[]T` parameter is proven against `v[i]` on both lanes — clang's
`cmp w2, w1; b.hs; ldr [x0, w2, uxtw #s]` is the arm64 checker's guarded
element shape, and GCC's `bgeu i, len` on the psABI's widened `u32` pair,
fused `slli 32; srli 32−s` zero-extend-and-scale, and `add` into the base
register is the rv64 checker's second admitted shape
(`Oak.RiscV.index_guard_widened`, `widened_scale`; `94-assembler.md` §9);
the guarded element write `oak_store` over a `[*]T` parameter is proven
against `v[i] = x` on both lanes as the span memory the unit writes
(the verifier's memory effects, `asm/effects.go`), the same shapes with a
store; the pinned prelude text of these helpers is what `generateC` emits,
`TestGuardMacrosMatchValidatedText`); and
every differential test executes the object. The
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

The OptIR scalar-call memory path has the first deliberately small
proof-certificate core beneath its larger graph producer. One fail-closed
CFG-order checker resolves active opaque IDs against separate authority, and
its accepted projection feeds both summary construction and the
child-before-parent trace. `Oak.OptIRMemoryAuthorityProjection` proves the
matching structural operation/authority model has exact active direct and call
membership, exact non-root coverage, and composes with the exact typed summary
fold. The production Go trace consumer then checks only exact typed region
effects and graph names; `Oak.OptIRCallSummaryCertificate` proves that model
yields exact reachable read/write bits and a closed acyclic graph. Selected Go
decisions at both seams are pinned to kernel-checked examples. This is a
**proved structural model with bounded correspondence**, not full
implementation refinement: concrete CFG extraction and SSA verification,
source and opcode/type validators, authority construction, SHA identity,
callee-summary truth, and source re-lowering remain outside the theorems.

The downstream static machine-callee identity seam is now separately
**proved with bounded correspondence** for every current scalar OptIR call,
whether or not it carries memory effects. Each call's nonzero SSA result ID is
retained as non-emitted metadata on its final AArch64 `bl` or RV64 `call`.
After cleanup, reallocation, and scheduling, candidate admission re-verifies
the exact CFG and block-layout evidence and rejects an untagged, missing,
extra, duplicated, retargeted, malformed, or indirect occurrence.
`Oak.OptIRMachineCallIdentity.check_sound` proves that acceptance gives an
exact permutation of certified `{site ID, callee}` occurrences with unique
IDs; compiler tests exhaust both target classifiers and pin the
accepting/refusing occurrence decisions to Lean examples. This proves static
occurrence identity, not control-flow placement,
dynamic call counts, arguments/ABI, callee implementation equivalence,
encoding, relocation, or the non-OptIR native path.

The verifier's ordinary machine-call summary path now has a separate exact
callee-identity gate. `asm.ResolveNativeCallee` is shared by call
summarization, loop discovery, outgoing-stack-area analysis, and the verdict
cache. It requires the function-map key and declaration name to agree and the
machine symbol to be exactly that scalar name, or exactly the active lane's
suffix of a declaration whose signature carries a fixed vector. Reserved-name
collisions, arbitrary aliases, unsuffixed vector entries, suffixed scalar
entries, opposite-lane suffixes, malformed declarations, and ambiguous
exact/base bindings refuse. `Oak.AssemblerCalleeIdentity.resolve_sound` proves
the corresponding ambiguity-aware model returns only a canonical declaration
whose native symbol is the queried machine symbol. Cross-target Go tables
cover the accepting and refusing decision families, with representative live
decisions pinned to Lean examples. This
closes static symbol-to-Oak-body identity for summarized direct calls, not call
placement, ABI argument transport, the truth of the callee body summary, or
callee implementation equivalence.

The first native-equivalence certificate slice is now available as an
**audit**, not as admission authority. For closed call-free, loop-free,
trap-free fixed-scalar AArch64/RV64 bodies,
`asm.ExportNativeEqualityCNF` reruns machine execution and Oak lowering and
constructs the exact result-disequality clauses.
`prove.CheckNativeEqualityCertificate` regenerates those clauses before
checking LRAT; the integration path also requires the checker written in Oak
to accept the certificate against the same DIMACS formula. Source-body and
machine-operation replay attacks are tests. `Oak.NativeEqualityCertificate`
proves the abstract composition from accepted RUP plus exact CNF completeness
to result equality. `Oak.TseitinCNF` proves that each raw AND/OR/XOR/ITE gate
record's exact clause list characterizes its Boolean equation,
composes any supplied gate sequence with its supplied non-settled final
clause, and carries that characterization to the exact 1-based initial RUP
database. `Oak.CNFBuilderTrace` checks a supplied production-shaped
input/gate allocation stream and proves that acceptance gives contiguous
unique shared allocations, exact complement-edge and operation-tag decoding,
backward operands, and `WellFormedSequence`. `Oak.CNFFinalObligation` proves
the exact four-way construction and that a pending decoded-root clause is
satisfied exactly when a trap fires or the claim is false. `Oak.CNFTermRoot`
proves evaluation preservation and pending counterexample semantics for a
supplied normalized one-bit Boolean term/root encoding under those gate
equations. Independently, the concrete exporter memo-replays the supplied trap
terms in slice order and the claim term, and checks the producer's root
filtering, order, polarity, and outcome before every successful return. A
pending snapshot additionally passes through
`validateCNFTrace` before serialization, checking the exact
gate-record/unique-table-memo bijection, allocator coverage/disjointness, exact
raw-clause order and multiplicity, and exact final-edge conversion; settled
outcomes run the gate/memo audit separately. Any mismatch among those checked
representations refuses export. It does not yet prove the Go checkers refine
the Lean checkers, actual Go terms satisfy `CNFTermRoot.Encodes`, or the
bit-blaster selects the right operations and folds. Term-memo semantics,
trap/claim term-list provenance or source ordering, and DIMACS correspondence
also remain open.
The hardened Go acceptance kernel is isolated in the standard-library-only `internal/lrat`
package, below `prove`'s compatibility wrappers and word codec. This removes
the SAT solver from the audit, but it does not yet remove symbolic execution,
Oak lowering, the remaining term-to-CNF generation, or the Go/Oak checker
implementations from the TCB, and it does not promote a compiler verdict.

Native verifier verdicts carry the Oak callees whose summaries they used.
Every successful result shape—including unit effects, multi-register
aggregates, deferred span decisions, and two-half vectors—preserves that
dependency union. The versioned on-disk verdict cache stores and validates the
same list, and its key includes direct machine-call targets as well as source
and theorem-rewritten reference-body reachability. Thus cold and warm builds
feed the same dependency graph to the
verified-profile closure; malformed or legacy records are cache misses. This
closes metadata preservation, not the larger proof-engine TCB: the cache holds
no certificate authority, and the bounded audit above always regenerates its
formula instead of trusting a cached verdict.

For the six AArch64 barrier forms, an independent executable regression witness
now checks the direct-native portion of this seam: six Oak source functions must
produce complete two-word object bodies containing the literal expected
barrier word and `RET`. The actual cold prepare and entry sources must produce
literal DAIFSet, their eight context-register MSR words, the exact ISB word, and
`RET`/`ERET`, with no stack frame. This pins static object-code occurrence,
order, and zero overhead but is not a Lean proof of the compiler or dynamic
execution. `Oak.AArch64ColdEntry.Step`
therefore still requires an
explicit occurrence-indexed external Arm context-synchronization witness. That
witness now pins every register-write action's register, word, and Rt and
requires the total HCR-through-SPSR program order; Lean proves the eight write
occurrences pairwise distinct. The unified generated decoder agrees with each
witnessed word/Rt/target, but does not create the occurrence or order edge.
The generated Sail bridge kernel-proves that the exact ISB word selects
`InstructionSynchronizationBarrier` in Oak's local pure projection and
conjoins that fact with the witness. A Go drift gate audits all six projection
mappings against the pinned official Sail source. Its
`InstructionSynchronizationBarrier` and `SynchronizeContext` functions are
separate unit-returning stubs, so this new dispatch proof deliberately does not
discharge the external state-semantic obligation.

The same narrow seam now covers the cold-entry IRQ-mask leaf. Lean computes
`MSR DAIFSet, #2` as `0xd50342df`; the occurrence-indexed cold-entry relation
retains one exact DAIFSet/#2 action through every later stage and requires it
before all eight register writes, ISB, and ERET. Generated Lean agrees on its
DAIFSet/#2 target and, in a separate conditional theorem, proves the successful
four-bit body sets PSTATE.I while preserving D/A/F. A Go drift gate pins the
complete nine-word Lean/native prefix and the official decoder, access/trap
boundary, dispatch, and assignments. The external occurrence is a premise,
not a trace extracted from object bytes. Access/trap/PostDecode admission,
dynamic execution, a runtime PSTATE transition, other architectural state,
interrupt recognition/delivery, interval-wide masking, memory ordering, and
context synchronization remain outside these facts.

The next cold-entry word, `MSR HCR_EL2, X0`, is computed as `0xd51c1100`.
Generated Lean proves its HCR_EL2/X0 target and component transition: EL2
directly installs the supplied value. The source gate pins the generic MSR
chain, exact nested route, old HCR NV/NV2/TGE aliases, SCR NS/EEL2 aliases,
direct assignment, and EL1 NVMem(120) alternative. Lean models only the
redirect flag and HCR component; consistency between its old-bit inputs and
the old 64-bit HCR value is an external premise. Access/traps, dynamic
occurrence, runtime X0
provenance, HCR validity and desired configuration, stage-2 enablement,
exception routing, later observation, ordering, and synchronization remain
open.

The following `MSR VTTBR_EL2, X1` is computed as
`0xd51c2101` from generated instruction and SysReg tables. Generated Lean
proves its pure decoder target and component transition: at EL2 the VTTBR_EL2
component becomes the supplied 64-bit value, while the official EL1
nested-virtualization redirect leaves that component unchanged. The official
source gate pins the generic MSR access/decode chain and direct/redirect
assignment. Access/trap admission, dynamic occurrence, runtime X1-to-source
argument provenance, register-field validity, table publication, BBM, TLBI
effects, completion, synchronization, and other machine state remain open.

The following `MSR VTCR_EL2, X2` is computed as `0xd51c2142`. Generated Lean
proves its decoder target and component transition. The official register is
32-bit, so the direct EL2 result is exactly X2 bits 31:0; bits 63:32 are not
preserved. The source gate pins the distinct `op2 = 010` nested route, five
HCR/SCR predicate aliases, low-32 direct assignment, NVMem(64) alternative,
and 32-bit register declaration. Access/traps, occurrence, runtime X2
provenance, predicate consistency with machine state, VTCR validity and VTTBR
compatibility, stage-2 behavior, NVMem effects, other state, publication,
ordering, BBM/TLBI completion, and context synchronization remain open.

The next `MSR CNTHCTL_EL2, X3` word is `0xd51ce103`. Generated Lean proves the
exact target and the admitted body's unconditional X3-bits-31:0 update of the
official 32-bit register. The source gate pins the full op1=100 route and keeps
the separate op1=000 `CNTKCTL_EL1` VHE path distinct. Access/minimum-EL/trap
admission, occurrence, runtime X3 provenance, timer-control field validity,
timer behavior, upper-bit preservation, other state, ordering, completion,
and context synchronization remain open.

The following `MSR CNTVOFF_EL2, X4` word is `0xd51ce064`. Generated Lean proves
the exact target and full-width component transition: direct at EL2, with the
EL1 nested-virtualization alternative represented as a redirect flag and
unchanged CNTVOFF. The source gate pins the complete op2=011 route, five old
HCR/SCR predicate aliases, NVMem(96) alternative, and 64-bit declaration.
Access/traps, occurrence, runtime X4 provenance, predicate-state consistency,
NVMem effects, counter arithmetic/monotonicity and guest-timer behavior, other
state, ordering, completion, and context synchronization remain open.

The following `MSR SP_EL1, X5` word is `0xd51c4105`. Generated Lean proves its
exact bank/operand target and full-width transition: direct at EL2, with the
official EL1 nested-virtualization alternative represented as a redirect flag
and unchanged SP_EL1. The source gate pins the complete route, five HCR/SCR
aliases, NVMem(576), and the 64-bit declaration. Access/traps, occurrence,
runtime X5 provenance, predicate-state consistency, NVMem effects, stack
alignment/canonicality/mapping/contents/safety, post-ERET selection/use,
relation to SPSR, other state, ordering, and synchronization remain open.

The following `MSR ELR_EL2, X6` word is `0xd51c4026`. Generated Lean proves the
exact S3_4 target, Rt preservation, and the official admitted body's unchanged
64-bit assignment. The source gate pins the full route and declaration while
keeping the distinct S3_0 ELR_EL1/VHE/NV path outside the theorem. Access/traps,
occurrence, runtime guest-PC-to-X6 provenance, target alignment/canonicality/
mapping/executability/PAC, relation to SPSR, ERET observation or success, other
state, ordering, and synchronization remain open.

The following `MSR SPSR_EL2, X7` word is `0xd51c4007`. Generated Lean proves
the exact S3_4 target, Rt preservation, and the official admitted body's
low-32 assignment to the 32-bit register. The source gate keeps the distinct
S3_0 SPSR_EL1/VHE/NV/NVMem(352) path outside the theorem. Access/traps,
occurrence, runtime guest-PSTATE-to-X7 provenance, upper-bit preservation,
SPSR field and legal exception-return validity, relation to ELR_EL2, ERET
observation or success, other state, ordering, and synchronization remain open.

These eight leaf proofs now compose through generated code. One Sail decoder
classifies the complete ordered word list with its X0-through-X7 Rt fields, and
a generated projected-state function calls the same eight component bodies.
`Oak.SailBridge.cold_entry_register_sequence_end_to_end` proves that generated
result equals Oak's EL2 fold, including the three low-32 destinations and the
ordered log. A Go gate ties the theorem's numeric words to the native object
oracle. This closes static projected composition only: full Arm state,
access/traps, runtime value provenance, dynamic occurrence/order, memory
ordering, ISB effects, and ERET semantics remain outside the theorem.

The terminal plain `ERET` now has its own narrow generated seam. The generated
instruction table and Lean both fix it as `0xd69f03e0`; generated Sail Lean
proves the exact non-PAC decode fields under an explicit non-EL0 input to its
pre-`__PostDecode` checks, excludes EL0/authenticated/corrupted inputs, and
projects the composed EL2 state to the installed ELR_EL2/SPSR_EL2 inputs.
Its dedicated nested-virtualization trap predicate is false at EL2 under the
official predicate's required EL1 conjunct. A Go source gate pins the official
decode clause and bodies, EL2 selectors, and `SynchronizeContext` before
PSTATE restoration and branch. This closes exact static encoding, decode
target, and selected inputs—not dynamic occurrence, `__PostDecode`, global
trap freedom, SPSR validity, synchronization semantics, architectural state
transition, branch success, or observation.

Live stage-2 maintenance has a separate restricted proof layer.
`Oak.AArch64Stage2Maintenance` projects the pinned CAT `BBM` sequence for one
old descriptor event and proves that DSB ISH-classified occurrences around an
abstract TLBI construct two local projected edges corresponding to its
ordered-before operands. The CAT AST gate pins the exact seven-operand `BBM`
definition and separately pins `DSB-ob`/`ob`. It now also pins the cacheable
and uncacheable TTD sets, all six `TTD-update-BBM-cand` arms, the exact
`TTD-update-needsBBM` sequence, and the exact flagged
`Warning-BBM-expected` difference test. That CAT construct is a diagnostic
warning, not an execution-validity axiom. Lean proves its propositional warning
shape empty only under explicit premises that all old events are maintained,
official-needs membership projects to Oak's local requirement, and Oak's
`ProjectedBBM` implies official `BBM`; none of those refinement premises is
claimed here. A conditional wrapper preserves externally supplied exact
`STR XZR,[X0]`/DSB ISH/VMALLS12E1IS/DSB ISH/`STR X2,[X0]` word/action
occurrences at the same five indices as the BBM ordering chain and proves the
five `po`-linked break-through-make events distinct. Its word and action
fields are independent. The Sail bridge conjoins the TLBI's named call-target theorem without
replacing that external premise. Dynamic instruction-trace extraction,
descriptor event classification, coherence-after, invalidation scope, concrete
IPA/VMID target selection, completion, and context synchronization remain
explicit obligations. Sail's coarse single-model-TLB reset implementation,
which ignores architectural target granularity, is not used to discharge them.

Two checked-in tests are byte-compared with exact blobs in Herdtools7's pinned
official AArch64-BBM catalogue before execution. The synchronized VMSA case is
`Never` with no BBM warning; the unmaintained case is `Sometimes` with exactly
`Warning-BBM-expected`, and both stable Herd hashes/witness counts are pinned.
They use stage-1 `VAAE1IS`, not Oak's stage-2 `VMALLS12E1IS`, and prove only
generic CAT model/diagnostic behavior—not Oak event classification, `ca`,
`inv-scope`, target suitability, completion, synchronization, Sail/ASL state,
or the local-to-official BBM refinement premise.

An adjacent exact-sequence layer records DSB ISH, VMALLS12E1IS, DSB ISH, and
ISB occurrences and their program-order directions. Its completed form retains
external predicates relating the exact TLBI/post-DSB pair and the exact ISB
occurrence. The module does not derive either predicate from decoder identity or
capability flags; when a supplied predicate is refuted at those events, a
negative theorem prevents construction of the completed wrapper. Predicate
adequacy and provenance remain external. This is an instruction
maintenance/context-sync slice, not a descriptor BBM witness.

The exact sequence additionally constructs Oak's restricted local ordering
shape corresponding to the pinned first `DSB-ob` arm, from its TLBI occurrence
through the post-DSB ISH to its ISB occurrence. If a caller supplies a later
occurrence and `po` edge from that same ISB, Lean constructs the shape
corresponding to CAT's `DSB-ob; [IFB]; po` arm. The CAT gate pins the normalized
official arm hash and rejects removal of `DSB-ob`, `IFB`, or `po`; extracting
the external sequence from the Sail-decorated conjunction preserves all
occurrence indices. These are restricted local projections only. They do not
prove DSB completion, ISB context synchronization, official CAT event tagging
or destination filtering, dynamic trace extraction, or TLBI scope/effects.

The adjacent encoding seam now proves one concrete Inner Shareable instruction
encoding and named Sail call-target identity without conflating either with
those obligations or with plain, local-PE `TLBI VMALLS12E1`:
`Oak.AArch64Encoding` computes
`TLBI VMALLS12E1IS` as `0xd50c83df`, and generated Sail Lean proves that word
selects `TLBI_VMALLS12E1IS` in Oak's pure projection. The drift gate ties the
projection to the generated Arm XML row, pinned generic SYS field decode, and
official nested dispatch; it also proves that the distinct plain-VMALLS12E1
word does not select the IS-only target. The closed
`arm64.tlbi_vmalls12e1is()` source operation and an independent direct-native
gate now pin the complete object body to the IS word followed by `RET`; this is
executable occurrence evidence, not the still-open formal extraction of a
dynamic execution occurrence. The downstream OS currently emits the plain
VMALLS12E1 sequence, so this encoding theorem, conditional bridge, and object
witness are not evidence for that consumer path.

The deliberately incomplete stage-2 BBM ordering source slice is separately
pinned in full. Its Oak type requires an 8-byte-aligned span and its assertion
requires one element; `Oak.Forwarding.unsigned_lt_one_is_zero` licenses the
direct zero test and `zero_index_store` the local store cleanup. The
freestanding ELF/AAPCS64 native symbol is exactly `CBZ w1`, the two exact STR
words around the three exact maintenance words, `RET`, and trap `BRK`. The C
lane preserves the same fall-through store/system order. `Oak.Forwarding`
proves only the local Boolean-branch and zero-index address/value equalities
used by lowering/cleanup. Because DSB is outside the semantic verifier's
decided subset, the whole-body verdict is trusted. Neither that verdict nor
the exact STR encodings derives an official Sail/ASL memory write, PTE
provenance/alignment beyond the source base fact, CAT `ca`/`inv-scope`
membership, TLBI effects, DSB completion, publication, or ISB synchronization.
There is no Darwin/Mach-O object oracle or privileged Apple EL2 execution gate.

The fixed Oak context-sync example has a bootstrap C system-instruction order
gate and an independent native zero-overhead gate: the bootstrap C lane retains
the four system instructions in order, and the native ELF symbol is exactly
their four words plus `RET`. The Sail bridge decorates the
external exact-sequence witness with DSB/TLBI/ISB decoder and named-call-target
facts only. Current OS entry uses the structurally similar plain local TLBI,
while revoke also omits ISB, so neither consumer is covered by this IS-only
slice.

The seam checker's join rule for index bounds is **refined**:
`Oak.CheckerMeetRefinement.meetFact` transliterates `meetIdx`'s
per-register equality/reconciliation decision, and `meetFact_sound` proves
that every retained bound holds on both predecessor register states. The Go
decision table is pinned to executable Lean examples by
`asm/check_meet_test.go`. This closes that join rule only; it does not turn
the whole seam checker or semantic verifier into a certificate-checked
implementation.

The object writer's relocation-footprint admission is also **refined** at one
small boundary. `Oak.ObjectLayout` transliterates the production four/eight
byte width decision and proves that every admitted first instruction, and the
second instruction of each `adrl21`, `riscv_pcrel`, or `riscv_call_plt` pair,
lies inside its defining function. `asm/object_layout_refinement_test.go` pins
all live kind spellings and their boundary decisions to kernel-checked Lean
examples. The writer now rejects missing symbols and incomplete pairs before
format-specific emission. This does not prove ELF/Mach-O record encoding,
relocation meaning, symbol resolution, section layout, or linking.

One executable-relocation case now has a **proved model and bounded production
correspondence**. `Oak.ObjectRelocation` specifies AArch64 `B`/`BL` patching:
the original opcode, four-byte alignment, the exact signed 26-bit scaled reach,
replacement of only the immediate bits, signed decoding, opcode preservation,
and arrival at the target. The final-ELF resolver applies the corresponding
fail-closed helper for `call26`, `jump26`, and the legacy `branch26` spelling;
its Go boundary decisions are pinned to kernel-checked examples and the start
stub's linked call word is checked in the written ELF. The pins are not a
universal implementation-refinement theorem for Go. This closes only the
model's word-level arithmetic. Symbol/layout authority, other relocations, ELF
structure, and the complete output bytes remain trusted.

### 2.6 Object → binary

The default link is the C compiler's driver (`compileC`), static for Linux
cross builds, with the manifests' `link`/`framework` inputs and the
realization shims. `-link oak` instead writes the closed native program's
static ELF in process. Both remain **trusted** as complete layout/link steps;
the AArch64 direct `B`/`BL` patch described above is the one proved word-level
exception. Finished images are **differentially** exercised through
`oak run -target` under QEMU where present.

## 3. Per target

| Target | Source → C | C → object | Asm/native lane | ISA semantics the lane is held to | Encoding | Execution check |
| --- | --- | --- | --- | --- | --- | --- |
| linux/arm64, darwin/arm64, freestanding/arm64 | refined core + differential | trusted (cc); every trusted-core helper translation-validated through the verifier, as clang builds it at armv8.0, at armv8.1-a and for the Apple cores (73 proven, 20 witnessed) | arm64: verifier proof/evidence/trusted; atomics and division decided under the sequential model | **proved to Arm's ASL**: `Oak.ArmASL` transliterates the Sail Armv8.5-A primitives with the Sail text beside each, proved equal to `Oak.AssemblerSemantics` (including complete NZCV equality for addition, subtraction, and `ccmp`; signed overflow is proved generically with direct 32-/64-bit corollaries); the hand transliteration is proved against Sail's mechanically generated Lean (`spec/sail/lean/Out.lean`); the decode tree **audited** (`asm/sail_coverage_test.go`), operand forms audited against the A64 ISA XML | table **generated from the ISA XML**, checked against `llvm-mc`; DMB ISHLD/ISH/SY, DSB ISH/SY, and ISB exact words **proved through Arm's Sail decoder**; exact Inner Shareable `TLBI VMALLS12E1IS` word (not plain `VMALLS12E1`) and named SYS call target **proved through the pinned Sail projection**; exact DAIFSet `#2` word and its conditional pure PSTATE.I/D/A/F transition **proved through the pinned Sail projection**; exact VTTBR_EL2/X1 word and conditional component update **proved through the pinned Sail projection** (`Oak.AArch64Encoding`, `spec/sail/lean/Bridge.lean`); the general decoder outside these subsets, access/trap admission, and TLBI effects remain open | silicon **differential** (181 bodies × 60 inputs on the host core) |
| linux/riscv64, freestanding/riscv64 | refined core + differential; RVWMO mapping proved | trusted (cc); every trusted-core helper translation-validated through the verifier (75 proven, 18 witnessed) | rv64: same verifier, RISC-V semantics (`Oak.RiscV`); loads, stores and the A extension's `lr`/`sc`/`amo*` through spans decided under the sequential model | **bridged to the Sail RISC-V model**: `spec/lean-sail` builds against the export itself (Sail from git, sail-riscv 497209b9) — 53 semantics theorems (every integer instruction the verifier decides, the pure parts of loads and stores) and 30 encoding theorems; `Oak.SailRiscVBridge` keeps the R/W/B subset checkable without the export; the memory monad stays audited | own encoder (`rv64_encodings_gen`, RV64IMAFD + the V and C subsets) checked against GNU `as`; RVC | `qemu-system-riscv64` where present |
| linux/amd64, darwin/amd64, freestanding/amd64 | refined core + differential | trusted (cc) | **none** (`Oak.Target.lane = none`) | **none**: no Oak semantics of x86-64 and no bridge to a machine-readable x86 specification | none | host execution (differential) |
| freestanding/arm (Cortex-M), freestanding/riscv32 | refined core + differential; ILP32 proved | trusted (cc) | none | none (Arm's M-profile ASL is not public; `docs/notes/oak-cortex-m-deferred`) | none | cross build only |

## 4. Where source-level proofs connect to the ISA

A theorem about an Oak program (`oak prove`, or the Lean extraction of
`95-extraction.md`) is a statement about Oak's semantics: the
interpreter's, and the shallow embedding's (fixed-width integers as Lean
`UInt`s with the same wrapping). For a function the native lane realizes,
the verifier proves the emitted instructions equal to *its own* lowering of
the Oak body into the term language of `Oak.AssemblerSemantics`, and that
language's instruction semantics are proved to Arm's ASL. Until 2026-09-13
the chain from a source theorem to the machine had one **unproved seam**:
nothing in Lean stated that the verifier's Oak lowering (Go,
`asm/verify.go`, "under Oak's total wrapping arithmetic") and the
extraction's embedding agree — both transliterated `20-types.md` §11.1 and
were held to it by tests.

`Oak.LoweringRefinement` closes it for the subset the two share. The
module states one typed expression language over a function's parameters
and the locals in scope — variables, checked literals, the wrapping
`+ - *`, the unsigned bitwise operators and shifts, `/` and `%` by a
constant power of two (a shift and a mask) and by any divisor (the
uninterpreted quotient `udiv`/`sdiv` and the remainder `a - (a / b) * b`,
`Term.uop`; the zero divisor is Oak's trap, so the theorem speaks where
the extraction has a value, and the signed remainder identity is proved at
every width, `srem_eq_sub_sdiv_mul`), negation and complement, the widening
and narrowing
conversions, comparisons, `&&`/`||`/`!`, Bool conditionals, block-scoped
locals and rebindings (`x: T = e`, `x = e`), statement-level conditionals
whose arms assign locals (`c ? { x = e } | { y = f }`), integer-constant
matches in value and statement position (`x ? | 0 => a | 1 => b | _ => c`),
counted loops (`while c { body }`) and data-dependent ones, span element
reads and lengths (`v[i]`,
`len(v)`), owned arrays (`a: [n]T`, `a[i]`, `a[i] = e`, array literals),
records (`r: R = R{…}`, `r.f`, `r.f = e`, record parameters), the nesting
of the two (`r.h[i]`, `a[i].x`), calls that borrow the caller's arrays
through span parameters and write them back, calls that return records,
tagged unions of scalar payloads (a variant, a variant match with its
binding, union parameters), and calls to program functions — and two
readings of it: `evalX`, the extraction's
(`UIntN`/`IntN` arithmetic as `BitVec` arithmetic, shift counts modulo the
width, `decide` of the signed or unsigned order, `toIntN`/`toUIntN` as
extension by the source's signedness or truncation, a local as its
`let`-bound value, a statement conditional as the taken arm's values for
the variables it assigns, a constant match as the if-chain `if x == k₁
then … else …`, a loop as the fuel-indexed recursion that returns `none`
when the fuel runs out — a data-dependent loop the same recursion, read
under assignments whose fresh symbols denote the exit values — an owned
array as its `Array` of elements, a
record as its `structure` fields, a union as its `inductive` and a variant
match as the `match`, and an index out of range as a trap — Oak's semantics, where the extraction's
own `getD`/`setIfInBounds` reads zero and drops the write, a modeling
choice `95-extraction.md` §3 already marks as its own, a span element as the memory cell
at the index — the span's contents padded with zeros, `v.getD i.toNat
zero` — a call as the callee's body under its parameters), and
`lowerT`, the verifier's (`oakLowering.lower` case by case, with
`truncate`, `zeroExtend`, `adaptWidth` and `extendTerm` spelled as the Go
spells them, shape cases included, a local lowered once and substituted
through `adaptWidth(local.value, width)`, a statement conditional as
`lowerConditionalStatement`'s select between the arms' terms for every
local an arm assigned, a constant match as `matchArms`' equality
conditions and `selectMatch`'s / `lowerMatchStatement`'s selects arm by
arm into the fallback, an owned array as its element leaves `x[k]`
(`oakValue.elems`, each under the name the verifier gives an element),
read through `elementUnderIndex`'s element-by-element select and written
through `assignUnderIndex`'s select at every element, a record as its
field leaves `r.f` (`paramAggregate`'s naming, a record literal binding
each field in the type's order), a nested aggregate as the same leaves
under longer names (`r.h[k]`, `a[k].x`, the array's leaf naming a
parameter of the model), a union as its `tag` leaf and payload
leaves with a variant match the constant match on the tag (`matchArms`'
`cmpTerm("eq", tag, index)`, the arm's binding an alias of the payload
leaf), a borrowing call as `enterCall`'s copy of the owner's leaves into
the callee's span leaves and their write-back on return with the results
— a scalar, or the leaves of the record `inlineCallValue` builds — bound
in the caller, a counted loop as `lowerWhile`'s unrolling, a data-dependent
loop as `loopEvent`'s summary — the carried locals as the fresh symbols
`loop<index>.<var>`, the condition and body over them the event's
one-iteration semantics `verifyLoops` matches against the asm side's — while the
folded condition is a non-zero constant and `none` when it is not constant
or the budget runs out — `none` throughout is the Go's "outside the
subset" — a span element as `selectTerm` over the index at width 32 — a
constant index the element parameter `v[k]`, the same cell under the same
name — a call bound through `enterCall`'s fresh scope and inlined, over
`Term.eval`, the executor — with the constructors folding
as the Go's `binaryTerm`, `cmpTerm`, `iteTerm` and `selectTerm` fold:
constant operands, `x + 0`, a constant condition, a constant index, each
proved to evaluate as the node it folds).
`lowerT_eval` proves that wherever both run — the lowering admits the
expression and the extraction computes a value under some fuel — the
lowered term evaluates to the embedding's value, for every expression,
every parameter assignment, and every agreeing scope (`Agree`: each
local's term has the local's width and evaluates to its value). Where the
extraction traps (an index out of range, a fuel run out) the lowering
carries the verifier's trap obligation instead, which `oak prove`
discharges separately; the comparison codes are related to the extraction's comparisons
through the flag lemmas of `Oak.AssemblerSemantics`, the signed ones
bit-blasted at 8, 16, 32 and 64 bits. Parameters and locals live in
separate value environments because the verifier's terms name parameters
only: a local shadowing a parameter changes what the source means by the
name, never what a term means. Two eval-preserving liberties of the Go
are approximated and named in the model: a comparison in an `ite`
condition keeps the operands' width where `lowerT` re-widths it to 1, and
the merges skip the select when both arms left the same term object,
where the model skips when they left the same term (`Term.selectArm`),
which differs only when two arms build equal terms separately. `asm/lowering_refinement_test.go` pins the Go lowering to `lowerT`:
the rendered terms of a table of Oak expressions must be the renders
stated as examples in the Lean file, so either side changing must visit
the other.

With it, on arm64, a theorem about an Oak function's extraction composes
with the verifier's verdict and `Oak.ArmASL` into one statement about the
machine for a body inside the shared subset: source theorem, `lowerT_eval`,
the verifier's equality, the ASL bridge. A local declared inside a loop
body or an arm is covered by pre-declaring it: its declaration binds the
initializer's term as an assignment does, so every later read sees the
same terms. A data-dependent loop is covered up to the meaning of its
fresh symbols: the theorem holds for every parameter assignment that
reads them as the exit values, which is what the symbols stand for, and
the event's condition and body are instances of the same theorem over any
iteration's values.

The first float seam is `Oak.FloatLoweringRefinement` (2026-09-15). Its
`lowerF_eval` proves, for every straight-line expression over `f32` parameters,
post-rounding bit-pattern literals, and local declarations or rebindings using
`+`, `-`, `*`, `/`, and ordered ternary `fma`, plus unary negation, `abs`, and
`copysign`, that the
extraction's operation reading equals the verifier term's matching
arithmetic or sign-bit reading. The generalized `lowerWith_eval` maintains
the agreement invariant while the verifier substitutes a local's lowered
initializer. The operation map, operand order, literal bits, and substitution
shapes are pinned to `oakLowering.lower` by
`asm/lowering_refinement_test.go`, including the non-contraction of
`a * b + c` and the sign-mask forms. `lowerCondition_eval` adds all six IEEE
comparisons over those expressions; the bit-level predicates make NaN
unordered and signed zeros equal, and the production render pins include the
verifier's complete `floatCompare` expansions. Its structural induction also
covers Boolean literals, `!`, `&&`, and `||` over pure condition leaves; in
that scope the verifier's strict bit operations equal Oak's short-circuit
value. `lowerValueConditional_eval` then composes that guard theorem with both
arm theorems for one value-position Bool conditional, matching the verifier's
`iteTerm` and extraction's Lean `if`. `lowerCall_eval` handles a pure `f32`
call with any ordered parameter list: its binding induction proves every
argument is read in the caller scope, the resulting callee source/term
environments agree, and the straight-line callee body therefore agrees when
inlined. `lowerFlow_eval` is the recursive closure of the value-position case:
every finite tree of pure guards and straight-line float leaves becomes the
same tree of verifier `iteTerm`s and extraction `if`s.
`lowerConditionalBlock_eval` closes finite scalar statement branches. It
executes every initializer and each arm's assignments sequentially, starts the
two arms from the same scope, derives every written name, and proves the
verifier's pointwise `iteTerm` merge agrees with the tuple returned by the
extraction's selected do-block. `lowerConditionalAssignment_eval` is its
one-local corollary. `lowerWiden_eval` covers explicit `f64(e)` when `e` is in
the proved straight-line `f32` slice: both sides apply `Float32.toFloat`, and
the production render retains `fcvt64` over the exact width-32 operand term.
The separate `lowerF64_eval` family proves ordered `Oak.FloatOps.fma64` over
binary64 parameters, already-rounded bit literals, and straight-line local
substitution. It does not yet compose with the widening family.
This is deliberately still a first slice: decimal parsing into the literal
bits, all other conversions, spans, effectful conditions, nested or effectful
statement arms, borrowing/recursive/effectful calls, other `f64` arithmetic,
and vector operations remain related to the extraction by tests rather than
this theorem. Division here proves operation identity and operand order through
Lean's `Float32.div`; it does not independently prove correctly-rounded IEEE
division or payload-observing NaN behavior.

For the C route (every function the native lane does not cover, and every
function on amd64 and the microcontrollers), the source-level proofs reach
the C text through the refinements of §2.3 and stop at the C compiler,
except for the trusted-core helpers §2.4 translation-validates.

## 5. What would extend the chain, in order of leverage

Done on 2026-09-13:

1. **The seam** (§4): `Oak.LoweringRefinement`, pinned by
   `asm/lowering_refinement_test.go`. Extending it means growing the
   shared expression language toward what the verifier lowers beyond
   scalars — block-scoped locals, inlined calls, span elements, counted
   loops — with the extraction's reading of each.
2. **Translation validation of the trusted core** (§2.4):
   `codegen/translation_validation_test.go`, arm64 through clang — at
   armv8.0, at armv8.1-a (LSE), and as the Apple cores' compilers build it
   (`-mcpu=apple-m1`: LSE atomics, `ldapr` for an acquire load) — and rv64
   through GCC. Every helper is decided on arm64 (73 proven, 20
   witnessed: the multiplications and the narrow and signed divisions);
   what it does not decide
   is the shift helpers under a variable count (Oak traps, the verifier
   refuses) — the constant-count specializations are proven. Every helper
   is decided on rv64 too (80 proven, 13 witnessed) since the unit
   language gained the A extension (GCC's `lr.w`/`sc.w` compare-exchange
   loop, the element address formed before the loop head).

Next, arm64 first (2026-09-13: every workload runs on arm64, so the lane
whose chain is proved end to end is the one to deepen; the others wait
for a workload):

3. **Widen the seam** (§4) from scalar expressions to what the verifier
   lowers for real native bodies. Done 2026-09-13: block-scoped locals and
   rebindings, inlined calls to program functions, statement-level Bool
   conditionals whose arms assign locals, integer-constant matches in
   value and statement position, span element reads and lengths, the
   constructors' constant folding, counted loops, owned arrays with
   literals, records, their nesting, and tagged unions of scalar payloads
   (`letIn`, `call`, `condSet`, `matchInt`, `matchSet`, `elem`, `len`,
   `whileLoop`, `arrDecl`, `arrLit`, `arrGet`, `arrSetE`, `recDecl`,
   `callX`, the `Agree` scope invariant; an array's leaves are named by a
   function, so `r.h[k]` and `a[k].x` are the same constructors under
   longer names; a borrowing call copies the owner's leaves into the
   callee's span leaves and writes them back, binding a scalar or record
   result in the caller;
   a union is the record of its tag and payload leaves and a variant match
   the constant match on the tag, so it needs no constructor of its own;
   `lowerConditionalStatement`'s select against the extraction's `let
   (vars) ← if c then … else …`; `selectTerm` against `getD` over a memory
   named as the verifier names it, `v[k]`; `lowerWhile`'s unrolling against
   the fuel-indexed recursion, the lowering `Option`-valued as the Go's
   `ok` is; an array local as its element leaves `x[k]`, in-range reads
   and writes against the extraction's `Array`, a trap where the index is
   out of range; a record as its field leaves `r.f`, bound by the same
   named binder a call uses; a local declared inside a loop body or an
   arm is a pre-declared local, its declaration the first assignment).
   What the native bodies use is covered, data-dependent loops included
   (`whileEvent`: the carried locals as fresh symbols after the loop, the
   theorem under assignments where the symbols denote the exit values);
   what remains is at the edges: most floats and vectors — so `lowerT_eval`
   covers the bodies `oak build -native` actually verifies rather than their
   arithmetic alone. This is the step that turns "source theorem implies
   machine behavior" from a statement about expressions into one about
   functions on arm64. **First float slice (2026-09-15):**
   `Oak.FloatLoweringRefinement.lowerF_eval` connects exact `f32` `+`, `-`,
   `*`, `/`, ordered ternary `fma`, unary negation, `abs`, and `copysign` over
   parameters, post-rounding
   literal bits, and straight-line local declaration/rebinding to the verifier's
   width-32 operation/sign-bit terms and local substitution; the production
   render pins cover those shapes and a multiply followed by an add.
   `lowerCondition_eval` covers `==`, `!=`, `<`, `<=`, `>`, and `>=` over the
   same expressions, pins the verifier's bit-level comparison expansion, and
   recursively composes pure Boolean literals/negation/conjunction/disjunction.
   `lowerValueConditional_eval` composes such a guard and two float arms for
   one value-position conditional; `lowerFlow_eval` closes arbitrary finite
   nesting of the same form. `lowerCall_eval` binds any ordered list of pure
   `f32` arguments in the caller scope and proves the inlined straight-line
   callee body. `lowerConditionalBlock_eval` proves any finite sequence of
   scalar initializers and sequential assignments in either statement arm,
   then the pointwise merge of the union write set; the one-local theorem is a
   corollary. `lowerWiden_eval` closes explicit `f32`-to-`f64` widening over
   that straight-line operand slice, pinned as `fcvt64(fadd32(a, b))` and
   `(Oak.FloatOps.add32 a b).toFloat`. The separate `lowerF64_eval` family
   closes ordered binary64 FMA over parameters, bit literals, and pure locals,
   pinned to `fma64` extraction and both native target verifiers. Decimal
   parsing, all other conversions,
   memory, effectful conditions, nested or effectful statement arms,
   borrowing/recursive/effectful calls, and the rest of the float/vector edge
   stay open.
4. **Widen translation validation** (§2.4) on arm64: landed for the
   checked shift helpers under constant-count specializations (1, 3,
   width − 1 at every unsigned width; the verifier admits a constant
   count, the helper's trap check folds away) and for `oak_index` against
   the guarded element read `v[i]` — proven on arm64 and, since the rv64
   checker admits GCC's shape (`bgeu i, len` on the raw widened `u32`
   pair, `slli 32; srli 32−s` zero-extending and scaling in one step, the
   address formed in the base register; `Oak.RiscV.index_guard_widened`,
   `widened_scale`), on rv64; and for `oak_store` against the guarded
   element write `v[i] = x`, proven on both lanes as the span memory the
   unit writes; and for the strong compare-exchange helper
   `__oak_cas_u32_acq_rel_acquire` on a cell reached through a guarded
   span element, proven against `atomic_compare_exchange_acq_rel_acquire`
   in both of clang's spellings — the exclusive loop (armv8.0) and `casal`
   (armv8.1-a, a second arm64 lane) — once the verifier's memory model
   reached the atomics under the sequential model (`65-machine-memory.md`
   §7a, `asm/atomics.go`: the exclusive store succeeds, so the retry is
   decided). GCC's rv64 `lr.w`/`sc.w` loop is outside the rv64 unit
   language and is reported so. **Item complete** for the helpers the
   prelude has.
5. **Finish the RISC-V bridge** (rv64 is dbs's second target): **landed
   2026-09-14** for the integer instructions. With Sail built from git
   (every package of the rems-project/sail checkout pinned in one opam
   switch, `sail_maker` included) the export of sail-riscv 497209b9
   (2026-08-19) generates in minutes and builds under lean-sail v5 in
   135 jobs (130 MB, not gigabytes); `spec/lean-sail` builds against it,
   53 semantics theorems and 30 encoding theorems checked against the
   export itself (`94-assembler.md` §9, `spec/lean-sail/README.md`), and
   `asm/rv64_sail_bridge_test.go` runs the build when the export is
   present. Two facts to keep: sail-riscv's current model does not export
   (`vmem_types.sail`'s type-level `root_level('v)` comes out with unbound
   `k_v`; upstream's own `compile-lean` workflow has been red since
   2026-09-04), so the checkout under `external/` is pinned to the last
   commit whose export compiles; and the model's `encdec` branch arm is
   defined only for even offsets, so the branch encoding theorems carry
   that hypothesis. Every integer instruction the verifier decides is
   bridged, and of the loads and stores the address, alignment guard,
   extension and truncation are; what stays audited rather than proved is
   the model's address translation and memory access in the monad, for
   which the checker's bounds and the verifier's flat element memory
   stand in. The rv64 verifier decides no atomics, so the AMOs the memory
   refinement pins at the C level have nothing to bridge yet. **Execute
   bodies and CI (2026-09-14):** `spec/lean-sail/OakSailBridge/Execute.lean`
   rewrites the generated `execute_RTYPEW`, `execute_RTYPE` and
   `execute_BTYPE` to their canonical monadic shape through the monad laws
   and the data theorems, so the register plumbing is checked too; and the
   `rv64-bridge` job of `formal-sail.yml` builds Sail from git, the export,
   and this bridge on every pull request, with the export required.
6. **An amd64 lane and an x86 semantics** — **deferred** (2026-09-13: no x86-64 workload exists; amd64 stays a C-only target until one does). The native backend's third lane,
   with instruction semantics bridged to a machine-readable x86-64
   specification. Scoped 2026-09-13, in the order that pays first:
   1. `Oak.X86`, the semantics of the integer subset the verifier would
      decide (`mov`, `add`, `sub`, `imul`, `and`, `or`, `xor`, `shl`,
      `shr`, `sar`, `neg`, `not`, `lea`, `movzx`, `movsx`, `cmp`, `test`,
      `setcc`, `cmovcc`, the conditional branches) as total `BitVec`
      operations with the CF/ZF/SF/OF flags, in the shape of `Oak.RiscV`,
      **bridged to ACL2's `x86isa`** (`acl2/books/projects/x86isa`, the
      Intel-validated model) by verbatim restatement of its instruction
      semantic functions, a Go test keeping the copies honest against the
      fetched sources — the RISC-V bridge's shape, since x86isa is in ACL2
      and has no Lean export. The REMS Sail x86 model is a Sail-1-era
      fragment with no published repository under `rems-project` today
      and no path to the Lean backend; it is not a candidate.
   2. The verifier's amd64 lane (`asm/x86_64_verify.go`): SysV AMD64 psABI
      binding (`rdi, rsi, rdx, rcx, r8, r9`; `rax` the result; a narrow
      argument's upper bits unspecified), a closed instruction table,
      `.amd64.oakasm` units, the checker's frame and clobber rules for the
      x86 calling convention. Its first user is `codegen/translation_validation_test.go`
      extended with clang `--target=x86_64-linux-gnu`: the trusted-core
      helpers checked on amd64 before any encoder exists, which is what
      the chain on amd64 lacks most.
   3. The encoder — ModRM/SIB/REX/prefixes generated from a table and
      **checked against Intel XED** (`intelxed/xed`, the decode/encode
      oracle in the role `llvm-mc` and Arm's XML play for arm64; note
      `/usr/bin/xed` on macOS is Xcode's editor launcher, not XED) and
      `llvm-mc`, and the ELF/Mach-O amd64 object writer.
   4. `nativegen`'s amd64 lane over the same IR, `Oak.Target.lane = amd64`,
      verified per function by the lane of step 2, silicon differential on
      an amd64 host in CI.
   Until step 2 lands amd64 is a C-only target and its chain ends at the
   compiler.
7. **The microcontrollers**: wait on Arm's M-profile ASL
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
