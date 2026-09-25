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
admitted. **Refined**: the type lattice (`Oak.TypeLatticeRefinement`), whose
formal opaque-atom premise is discharged for the current closed in-package
type universe by `Oak.TypeLatticeAtomIdentity`; a production
drift/correspondence gate holds the Go comparator to that model,
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
backward operands, and `WellFormedSequence`. `Oak.CNFDenseAllocation` then
checks a production-shaped nonnegative snapshot with explicit input and
memo-map projections: exact dense/injective ownership of `1..variables`,
ordered backward gates, no recorded folded shapes, and an exact unique-table
lookup for every gate. Acceptance supplies the same well-formed sequence and
proves each in-range variable has exactly one owner. Representative production
accept/refuse decisions are rendered as kernel-checked Lean examples;
arbitrary Go memory/map projection, signed conversion, builder history,
clauses, DIMACS, and verdict authority remain outside this bounded
correspondence. `Oak.CNFClauseTrace` now checks the actual signed builder and
emitted lists against those decoded gates and the supplied final edges. It
proves exact clause/literal order, positive-index signed decoding, and equality
with the initial RUP database, not just equisatisfiability. The production test
checks 72 fixed decisions and kernel-replays 71 projectable snapshots,
including shared builder/export corruption; this is bounded correspondence,
not a universal Go refinement or a test of the 50-million-clause limit.
`Oak.CNFClauseCertificate` discharges the native direct-word contract's
`cnf_complete` field at this checked trace boundary. Accepted RUP then implies
word equality under an explicit result-to-root equality premise. Source/root
provenance, DIMACS bytes, LRAT implementation refinement, and verdict authority
are still open. The next model layer now derives that root meaning for supplied
Boolean bit expressions: `Oak.CNFMemoWitness` supplies the converse exact
memo-to-gate witness, `Oak.CNFReplayApply` proves binary folds and memo replay,
and `Oak.CNFReplayMemo` discharges memo soundness from checked allocation.
`Oak.CNFReplayTerm` proves designated input slots survive gate evaluation and
connects recursive replay to the original-input semantics.
`Oak.CNFReplayCertificate.replayed_words_equal` then proves equality of the
words packed from supplied bit-expression pairs using accepted RUP and the
exact singleton obligation, without assumed root equality or CNF completeness.
Production apply decisions, the original one-bit corpus, and twelve word
fixtures are kernel-pinned. `TestNativeCNFReplayWordPairsMatchesLean` checks
1/8/16/32/64-bit roots, parameter and operand width adaptation (including
truncation followed by extension), shared subterms, interleaved input/gate
allocation, and exact direct-disequality roots. Concrete input/output pins
also check source-name/bit mapping and least-significant-bit-first packing.
The test-only syntax projector rejects malformed inputs, cycles, and excessive
depth/text expansion. These are bounded correspondence checks; arbitrary Go
name/bit/word projection, width adaptation, term-pointer memo/reachability
machinery, full admission policy, and remaining source/serialization/verdict
seams are not universally refined by that model theorem.
`Oak.CNFWordInput` now derives named input-bit binding through the exact
`parameter-count + 8` source stride and inverse checked allocation.
`Oak.CNFWordProjection` checks a supplied 1..64-bit parameter/constant/AND/OR/XOR
word grammar and proves its projection preserves independent bit semantics,
including declared-width masking, truncation, and zero extension.
`Oak.CNFWordCertificate.projected_words_equal` rejects incomplete/unequal result
pairing and derives equal widths and values using checked projection, replay,
singleton clauses, and RUP, without assumed model input-binding or word/root
equality. `TestNativeCNFReplayWordMatchesLean` kernel-pins raw Go word syntax,
complete replay roots, and typed-normalized sampled values over a bounded
1/8/16/32/64-bit corpus. This is the nonconstant certificate path. Arbitrary Go graph/table
projection, pointer memoization, full intermediate-root/reachability checks,
complete admission and settled-outcome policy, and the remaining
source/serialization/verdict seams are still outside the theorem.
The constant-false path now has its own model checker:
`Oak.CNFWordSettled.checkEqual` requires accepted dense allocation, complete
nonempty word projection, and replay of the exact difference to zero.
`checkEqual_sound` derives matching widths and equality for every typed input
without clauses or RUP, using the shared checked-replay and word-projection
lemmas. A true or nonconstant root refuses this equality-only checker; that
refusal is not an inequality theorem. `TestNativeCNFReplaySettledMatchesLean`
kernel-pins sixteen production outcomes, including alias/count/memo corruption
hidden behind false roots. Full Go admission/coverage refinement and compiler
verdict authority remain separate; this does not add a compiler consumer.

`Oak.CNFMetadataSettled.check` now gates settled equality with the complete
header check. Its returned ordered parameters are the ones used by word
projection; `check_sound` derives their validity, exact names, and equal word
widths/values for every typed input from one acceptance. Twenty-four production
fixtures kernel-pin the composition, including malformed unused metadata,
disabled modes, changed declared widths, allocation failures, and true/pending
roots. Recording coverage still needs binding to this same semantic snapshot;
this does not establish full Go admission or verdict authority.

The constructor metadata seam now has `Oak.CNFReplayHeader`: exact ordered
names, explicit index presence, widths, unique keys/counts, and disabled modes
yield valid parameters with no extra table keys. The Go check rejects missing
first indices rather than treating a missing map entry as zero.
`Oak.CNFMetadataCertificate.metadata_words_equal` uses these checked parameters
in the existing word-certificate chain; even constant-only projection must
pass the complete header check. Separately, `Oak.CNFReplayCoverage.finish_exact`
proves exact memo/input/gate domains and term root vectors from admitted
recordings against fixed producer contents plus matching completion counts.
The constructor and numeric `finish` decisions have bounded Go/Lean kernel
pins. Neither equal counts nor equal scalar snapshots establish content
integrity or producer immutability; same-size forged state is an explicit
accepted numeric counterexample. Universal Go trace/map/pointer/key projection,
full intermediate-root traversal and complete admission remain unrefined.
The production checked stores are now isolated as `recordTerm`, `inputEdge`
and `gateEdge`, with their original lookup/root/range checks and no trace
storage. `Oak.CNFReplayRecording` models their repeated-key updates and proves
an accepted event run from empty establishes the admitted-state invariant.
`Oak.CNFReplayRecordedCoverage.check_exact` derives exact term-root/input/gate
coverage from that executable run plus checked counts/finish, without assuming
reachability. Bounded actual helper sequences are kernel-pinned, and a source
structure regression confines replay-map writes to the checked helper sites.
This does not universally prove the Go walker's control flow, aliases, trace
projection or producer immutability; bookkeeping is not root semantics.
`Oak.CNFFinalObligation` proves
the exact four-way construction and that a pending decoded-root clause is
satisfied exactly when a trap fires or the claim is false. `Oak.CNFTermRoot`
proves evaluation preservation and pending counterexample semantics for a
supplied normalized one-bit Boolean term/root encoding under those gate
equations. `Oak.CNFBitwiseWordRoot` additionally proves that a low-to-high OR
of corresponding-result-bit XORs is true exactly when two fixed-width words
differ, and composes that exact obligation with accepted RUP. Independently,
the concrete exporter memo-replays the supplied trap
terms in slice order and the claim term, and checks the producer's root
filtering, order, polarity, and outcome before every successful return. A
pending snapshot additionally passes through
`validateCNFTrace` before serialization, checking the exact
gate-record/unique-table-memo bijection, allocator coverage/disjointness, exact
raw-clause order and multiplicity, and exact final-edge conversion; settled
outcomes run the dense, injective, input/gate-disjoint allocator and gate-memo
audit separately. Any mismatch among those checked
representations refuses export. A separate opaque
`ExportNativeBitwiseEqualityAudit` closes more of that concrete seam for the
strict parameter/constant/width-adaptation/AND/OR/XOR word grammar: an
independent walker reconstructs actual term roots, input allocations, exact
folds, gate-memo lookups, complete reachable coverage, and the direct final
disequality root. `prove.CheckNativeBitwiseEqualityCertificate` regenerates
that exact narrow audit and checks LRAT only against its DIMACS; both the Go
and Oak checkers accept fresh AArch64 and RV64 certificates, while changed
source, changed machine code, truncated proofs, malformed proofs, and
constant-settled obligations refuse. Mutated or broader terms refuse, and the
result has no conversion to `VerdictProven`, compiler consumer, or cache
authority. The Go checkers are not universally refined to
the Lean checkers; all other term operations, trap/claim provenance and source
ordering, DIMACS correspondence, symbolic execution, and Oak lowering remain
open.
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

The ordinary operandless `RET` emitted at every returning AArch64 epilogue has
a separate static encoding seam. `Oak.AArch64ReturnEncoding` pins the generated
`RET_64R_branch_reg` row, proves that `Rn[9:5]` round-trips while all fixed bits
are preserved, and proves the default `X30` word is `0xd65f03c0`. Generated
Sail Lean accepts that word as the ordinary non-PAC `RET` class with `Rn = 30`
and `BranchType_RET`; a corrupted fixed bit is rejected. Go drift gates pin the
generated encoding-table row/default, encoder bytes, official decoder clause
and dispatch, and the local Sail projection. This proves static
encode/decode/dispatch identity only—not X30 provenance, ABI/frame restoration,
target validity or mapping,
PAC behavior, `BranchTo` execution, object/link correctness, or observation.

Ordinary local `B <label>` now has the corresponding immediate-class seam.
`Oak.AArch64DirectBranchEncoding` pins `B_only_branch_imm`, proves exact fixed
bits and `imm26`, and proves its packer equals the existing Branch26 relocation
patch. Under the relocation model's individual four-byte alignment and signed
`[-2^27, 2^27)` byte range, decoding the emitted field reaches the modeled
target; `B +12` is exactly `0x14000003`. Generated Sail Lean selects
`BranchType_DIR` and the exact sign-extended scaled offset, while rejecting BL.
The production local-label encoder now refuses signed subtraction overflow and
jointly-but-not-individually-aligned addresses before mutation. This closes
static packing, bounded relocation arithmetic, and decode/dispatch identity,
not architectural PC/BranchTo execution, target validity, source-CFG label
selection, BL/X30, conditional branches, object/link correctness, or
observation.

Ordinary local `BL <label>` has the parallel call-class seam.
`Oak.AArch64CallBranchEncoding` pins `BL_only_branch_imm`, proves fixed bits,
exact `imm26`, equality with the Branch26 call patch, signed endpoints, and
target reachability. Generated Sail Lean selects `BranchType_DIRCALL` with the
exact sign-extended scaled offset and rejects `B`; Go gates pin the generated
row, local encoder, official decoder/dispatch route, overflow-safe subtraction,
and individual alignment. It does not prove architectural PC, the X30 write,
`PostDecode`, `BranchTo`, target mapping, source-CFG labels, object/link
correctness, or observation.

The 32-bit `CBZ W` guard has a separate partial seam.
`Oak.AArch64CompareBranchEncoding` proves its XML-row field packing, while
generated Sail Lean proves exact decode, signed displacement, and zero-test
equality with `Oak.AssemblerSemantics.cbz` on supplied register bits. The
BBM guard is `CBZ W1,+28`; its predicate tests only the supplied low-32-bit
length, independently of the upper X1 bits. WZR yields zero; CBNZ and CBZ X
are not admitted to this decoder. Complete official-source routes and Sail
regeneration are checked independently of the Go local-encoder cases. Dynamic
register/PC provenance, `PostDecode`/`BranchTo`, fall-through, trap execution,
and BBM memory effects are not proved by this slice.

The trailing `BRK #1` has a matching partial seam in
`Oak.AArch64BreakpointEncoding`: exact field packing and word, generated Sail
decode, and selected software-breakpoint argument components. Supplied EL2
stays EL2; the 25-bit syndrome carries immediate one, the supplied instruction
address is passed unchanged, and vector offset is zero. Go checks every
16-bit immediate and pins the complete official decoder/dispatch/exception
argument construction with mutation tests. The pure projection is not a full
exception record, ESR encoding, BTI/PostDecode execution, exception entry,
handler model, or proof of the runtime's non-resuming trap contract.

Separately, the native verifier's trap exclusion now requires a
symbolic implication from machine traps to collected source traps, without
assuming the machine-returning domain. This closes the unsampled-extra-trap
admission counterexamples at `b = 1234` and loop iteration 1234; unproved
obligations stay evidence and are refused by the strict profile.
`Oak.TrapDomainAdmission` proves the
logical admission rule under explicit collector-soundness and observation
equality premises, not the Go implementation or Arm exception execution.
Summarized loops retain separate header/body predicates and root traps:
header checks apply even on exit, body checks require source continuation,
and hypothetical nested states do not leak into parent scopes. Valid
peeled guards use only first-iteration source traps projected at exact
saved entry values/memories, guarded by source continuation; unknown
projections fail closed. After coupling, the gate
uses source-only reach conditions, never machine-return exclusions or loop
exit facts. Lean proves the phase rule and finite-prefix composition under
explicit collector/coupling and reachability assumptions; implementation
soundness and termination remain separate. This conservative gate is not
a complete source-to-ASL proof or a memory-ordering proof.
Explicit target-lane `.oakasm` verdicts now participate in that profile and
its callee-dependency closure; a unit without an Oak fallback remains
trusted and cannot pass strict admission.

Live stage-2 maintenance has a separate restricted proof layer.
`Oak.AArch64Stage2Maintenance` projects the pinned CAT `BBM` sequence for one
old descriptor event and proves that DSB ISH-classified occurrences around an
abstract TLBI construct two local projected edges corresponding to its
ordered-before operands. Those edges now enter CAT `ob` recursively through an
exact Lean projection of the unconditional full-DSB arm, including the ordered
source union, both `po` edges, `dsb.full`, and the complete destination
complement. Local-to-CAT `po`, endpoint/DSB membership, arm inclusion, and
`ob` transitivity remain explicit one-way premises. The CAT AST gate pins and
mutation-tests that exact arm, the seven-operand `BBM` definition, and the
`DSB-ob`/`ob` inclusion chain. It also pins the cacheable
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
fields are independent.

This DSB projection covers neither the ETS2/ETS3 conditional destination arm
nor `dsb.ld`/`dsb.st`. It proves ordering, not DSB completion, TLBI effect,
invalidation scope, visibility, publication, or a complete CAT execution.

The two pinned descriptor classifiers are now represented directly in Lean as
the membership formulas `TTDINV | TTDAF0` and
`(TTD & M) \ TLBUncacheableTTD`. An explicit one-way action-to-tag soundness
premise lets the exact store wrappers and `ProjectedBBMWitness` expose exactly
the old/break/make descriptor-filter facts. The CAT AST and lexically aware
Lean source-drift guards reject formula and operand-order drift; the latter
checks the projected definitions' spelling/lexical visibility, not command
elaboration. Three `Iff.rfl`
lemmas kernel-check the expanded DSB source, destination, and shared-event arm
formulas. Lean also states the complete seven-operand
`ProjectedCATBBM` predicate over supplied occurrence relations. A factored
one-way bridge separately maps descriptor tags, `coherenceAfter` to `ca`,
local `po`, decoded full-DSB and endpoint membership, destination exclusion,
full-arm inclusion in `ob`, `ob` transitivity, and local `invScope` to
`inv-scope`; under it the existing witness inhabits the exact projected
relation. The specialized warning theorem no longer needs a
monolithic `ProjectedBBM -> catBBM` premise. Primitive CAT predicates,
soundness of every bridge field, CAT event identity, reverse classification,
STR/value-to-tag derivation, and adequacy against an official execution remain
open; no completion, invalidation, or publication follows.

The Sail bridge conjoins the TLBI's named call-target theorem without
replacing that external premise. Dynamic instruction-trace extraction,
descriptor event classification, coherence-after, invalidation scope, concrete
IPA/VMID target selection, completion, and context synchronization remain
explicit obligations. Sail's coarse single-model-TLB reset implementation,
which ignores architectural target granularity, is not used to discharge them.

For the two STR occurrences, mechanically generated Sail Lean now proves the
exact STR64 unsigned-offset field decodes and the selected store arm's
address/data arguments immediately before `Mem`: explicit X0/X2 inputs yield `(X0, 0)` for the break
word and `(X0, X2)` for the make word. The source audit pins the unique
SEE-1277 clause, its historically misnamed `signed_postidx` decoder, fixed
normal eight-byte store parameters, X31-as-zero, and the final official
`Mem(address, 8, AccType_NORMAL) = data` call. These generated facts decorate,
but cannot create, each external descriptor occurrence/action witness.

The separate offset-form STP64 increment is deliberately not connected to
code generation or the semantic verifier. Production blocked zero fills use
four ordered scalar stores and the original scalar tail; they do not consume
this pair-store evidence. `Oak.AArch64Encoding` pins the
XML-generated `STP_64_ldstpair_off` base/mask and signed scaled `imm7` layout,
and computes `STP XZR, XZR, [X0]` and `[X0, #16]` as `0xa9007c1f` and
`0xa9017c1f`. The official-Sail source gate pins the corresponding 64-bit
normal-store decode and the instruction body's two `Mem` calls. Immediately
before those calls, the pure generated-Sail/`Oak.ArmASL` bridge exposes zero
request data at the effective address and at that address plus eight. This is
a pair of request arguments, not evidence that either request occurs and not
an observer-order relation between them. It proves no execution effect,
translation, fault freedom, atomicity or non-tearing, ordering, CAT event,
visibility, completion, or publication. Ordinary `STP` supplies no release or
barrier semantics; live PTE publication therefore remains scalar. Any future
blocked zero fill can reuse `Oak.BlockedFill.blocked_fill_eq` for final-state
algebraic grouping and its less-than-four tail bound. The checker refinement's
`span_element_then_pair64_store` proves that an admitted writable 16-byte
access covers two adjacent in-span u64 cells; synchronized examples admit
offsets 0 and 16 of a four-cell region and refuse offset 24 and a read-only
region. That is only byte bounds and writability metadata. It proves no
ordinary-memory, privacy, or unpublished custody, so generic and record-span
pair stores remain refused. The checker transports compiler-derived nominal
record identity through exact record elements and their nonnegative byte-tail
aliases; control-flow meets reject same-sized but differently named records,
and widened multi-record regions carry no single-record identity. This is
non-authoritative metadata only. Exact direct-`u64` field selection now narrows
indexed accesses to the field declaration, so following record fields cannot
extend the array bound. Unsupported layouts retain the original generic
checker behavior and yield no exact field fact. `Oak.RecordArrayRegion`
formalizes the selected geometry and four-cell loop decision, proves field and
record containment and nonwrapping 32-bit indices, and composes them with the
staged four-write final-state law. Declaration lookup/uniqueness itself remains
outside that theorem, and no instruction uses the quad predicate as permission.
A lowering still requires trap preservation, verifier support, scalar-tail lowering,
alias/observer exclusion, and private/unpublished ordinary-memory authority.
`Oak.PairStoreEffects` closes one later final-state edge in isolation: its log
uses the verifier's exact 32-bit modular indices, and under explicit no-wrap
premises applying one pair equals `storePair` while two adjacent zero pairs
equal four scalar writes. A synchronized Go helper builds those entries in
operand/address order, including the wrap case, but no instruction handler can
reference it; an AST gate permits only its declaration, and direct verifier
tests pin both existing pair-store refusals. It therefore proves neither
architectural occurrence nor component or observer order, and grants no
verifier or code-generation authority.

Generated static-protocol handles now have a sealed initial-constructor
designation carried through resolved resources, SemIR validation, and a
whole-program construction gate before resource flow. Direct initial literals,
uninitialized roots (including value aggregates/fixed arrays), and alternate
fresh/trusted result contracts cannot bypass the designated constructor;
checked same-resource transitions retain reconstruction permission only for
tail results, never independently bound local handles. Designated constructors
must have actual checked Oak bodies, with no foreign or assembly replacement.
Explicit-resource protocols keep their existing literal rules. The separate
`Oak.SealedTypestate` calculus proves that derivations retain an externally
supplied designated-mint premise and that transitions preserve resource/origin
identity. It is not a Go implementation refinement and establishes no actual
allocation, ordinary RAM, fault-free mapping, or CPU/DMA/external-observer
exclusion. Uncontracted/foreign typed return values can still have unknown
provenance; their origin is not established by this construction gate and no
fresh authority follows from their type alone. No native or asm admission
consumes this designation. Native lowering
currently precedes borrow/resource/effect gates and cannot consume such an
authority result; check-before-lowering and exact-region certificate transport
remain separate prerequisites. The explicit `ResourceSemIR` stage also checks
its injected declarations after `check(nil)` and needs its own ordering fix.
An eventual private-to-published transition must consume storage custody;
reclaiming published storage needs a separate completion/quiescence proof.

The next conditional Sail projection stops at the selected arguments of the
ordinary aligned size-eight `__WriteMemory` arm. For an externally supplied
translated 52-bit PA, generated Lean proves a 56-bit zero-extended call address
and post-endian data: break is zero under either endian, little-endian make is
X2, and big-endian make is X2 with its eight bytes reversed. The drift gate
pins complete official bodies from endian/alignment selection through
translation, fault, exclusive, MTE, trickbox/counter routing, `aset__Mem`, and
`__WriteMemory`, plus the exact `__defaultRAM : bits(56)` register declaration
and selected no-device forwarding wrapper. A further generated pure projection
selects `(56, 8, defaultRAM, ZeroExtend(PA), data)` at the external `write_ram`
boundary, retaining zero for break and the same endian-dependent make data.
This pure projection is not route/call-reachability or memory-effect evidence.
Occurrence-level decorators retain an external route predicate indexed by the
same event, virtual address, endian result, PA, and data; extraction returns it
and the original descriptor occurrence unchanged.

A separate effectful seam, `spec/sail/lean/MemoryBridge.lean`, now proves the
mechanically generated no-device `__WriteRAM` wrapper's normal return against
the pinned Sail Lean runtime's actual `write_ram`. For arbitrary prior memory,
it writes exactly eight consecutive bytes, least-significant byte first,
preserves memory outside that footprint, and leaves every non-memory state
field unchanged. A generic runtime theorem also covers arbitrary register and
choice-state types, beyond the generated fragment's RAM selector, GPR bank,
processor state, and load/store syndrome registers.
The selected break/make projections compose with this effect, including Arm's
pre-call endian conversion; a 52-bit PA plus seven cannot wrap the 56-bit call
address. This runtime ignores the RAM selector, as another theorem explicitly
records: the byte map provides no RAM-namespace provenance or storage custody.
Exact-source/mutation gates pin the external binding and forwarding body, plus
the separate Lem backend's `Write_plain` requests. Those requests are not
release writes, and no Lean-to-Lem/CAT refinement is established here.

The next effectful layer retains the exact `__WriteMemory` wrapper, the actual
`__defaultRAM : bits(56)` register, and the official no-device trace helper in
the generated Sail fragment. Its execution now has a complete sequential case
split: an initialized register entry yields the eight-byte update with the
same frame/state preservation; a missing entry returns Sail's `Unreachable`
runtime error with the entire state unchanged. Success is equivalent to the
presence of that entry. Thus the lower runtime's ignored selector does not
justify bypassing the wrapper's register read. The selected break/make
projections compose with this wrapper under both endian choices and an actual
register-lookup premise. No initialization is silently supplied, and this
RAM-selector interface is not the complete architectural register state. This error
is not an Arm Data Abort. Exact-source/mutation checks retain the register,
write/trace/return order, and no-op trace body, including its continuation
lines. A no-device trace is not architectural write-event evidence.

`RegisterBridge.lean` now covers an actual architectural accessor rather
than supplied register-value parameters. The exact `_R : vector(31, dec,
bits(64))` declaration and complete `aget_X` signature/body/overload are
copied from the pinned Arm sources and regenerated through Sail. The Lean
export indexes its 31-element vector directly by register number. For each
supported width (8/16/32/64), the bridge proves the selected low bits from
the actual initialized `_R` entry, with the complete state unchanged. Missing
bank initialization returns the unchanged-state runtime `Unreachable` error;
register 31 returns zero without reading the bank. Finite index types and an
explicit width predicate retain the source restrictions that appear only as
comments in the generated Lean signature. Bank-entry presence is not a reset,
architectural definedness, ABI-binding, or full-state initialization proof.

The explicitly **operand-only** `str64GPOperands` adapter composes two
generated reads, base before data, for non-SP bases and all GPR/XZR data
operands. Its result is proved equal to the existing audited pure STR64
request for every imm12 and initialized bank. A separate register relation
connects independent register observations to that bank. Thus the selected
X0/XZR and X0/X2 pairs now follow from actual generated reads; they do not
establish that the original instruction executes this adapter. The kernel
examples cover narrow/high-bit reads, X30/XZR, missing state, aliased operands,
the largest unsigned immediate, and 64-bit virtual-address wrap. No physical
address or RAM call is obtained by truncating the result. SP selection,
PostDecode, the instruction's syndrome call, `Mem`, translation, faults, architectural event
identity, and a Lean/Lem register-state refinement remain open. Exact-source
gates reject altered banks, accessors, continuation effects, and overloads in
both upstream and local copies; CI requires those gates and the new module.
Checked axiom reports admit only Lean's standard logical axioms, not `sorry`
or native-evaluation axioms, for the accessor and its main compositions.

`SyndromeBridge.lean` closes the next individual STR dependency: the original
`MakeLSInstructionSyndrome` and `AArch64_SetLSInstructionSyndrome`. The full
26-field `ProcState` record, `PSTATE`, `__LSISyndrome`, and the EL0/EL1 constants
are retained from the pinned Arm model, not replaced by a supplied privilege
flag. For all supported byte sizes (1/2/4/8), register numbers 0–31, and three
Boolean flags, the generated maker returns the exact ISV/SAS/SSE/SRT/SF/AR
fields with unchanged state. The original assertions and undefined size
initializer remain; this unchanged-state result uses the export's existing
trivial choice source, not a general nondeterministic-runtime refinement.
Out-of-domain size/register examples fail the retained assertions.

The generated setter reads the actual initialized `PSTATE` entry: EL0/EL1
write exactly the syndrome entry (including insertion when previously absent),
whereas EL2/EL3 preserve the complete state. Missing `PSTATE` returns the
unchanged-state runtime `Unreachable` error. All unrelated register lookups,
including their absence, and all non-register fields are preserved. Checked
STR64 examples give syndrome `0x77e` for XZR and `0x70a` for X2 at low EL;
they do not construct an ESR or prove exception handling. A clearly labeled
`str64GPDependencies` adapter composes the existing operand reads with the
actual generated setter, including exact EL2 no-op and missing-PSTATE results.
It is **not the original instruction body**: PostDecode, SP/MTE handling,
the call to this dependency from the instruction, `Mem`, translation/faults,
and architectural event/ordering semantics remain open. No RAM address is
derived by truncating its virtual operand address.

The required CI source gate checks complete upstream/local declarations and
rejects 41 mutation families, including altered privilege guards, field
layouts, assertions, register destinations, and appended effects. These are
source-audit mutants, not compiled runtime mutants. The default Sail Lean
build includes the new module; checked axiom reports contain only standard
logical axioms. Regeneration now invokes Sail on a temporary copy under a
stable relative filename so retained assertion messages are reproducible
across checkout locations, without rewriting generated output or weakening
the byte-for-byte freshness check. No compiler pin or verified-admission
boundary changes are part of this dependency proof.

`STRExecutionBridge.lean` now advances from those dependency adapters to the
**complete original instruction body**, in a separate generated slice. For
the non-SP, no-writeback STR64 case, its callee-parametric theorem factors the
generated body into the actual feature prefix, original register reads and
syndrome update, and an explicit arbitrary memory callback. Feature callbacks
may mutate state or fail; initialization premises apply to their resulting
state. Memory success or failure preserves the callback's exact resulting
state. The complete post-memory writeback tail is retained and discharged for
this no-writeback case, not silently omitted by extraction.

This is not yet real-callee or full-state refinement: the separate register
type contains only the bank, PSTATE, syndrome, SCTLR_EL2, and five version
configuration flags, and its full original
exception union differs from the earlier `Out` export. Real memory/feature
callees need a typed state lifting or larger export. Decoder/PostDecode, SP,
translation/faults, architectural events, and CAT/BBM ordering remain open.
The theorem fixes the erased width/count relation to 64 bits and eight bytes;
it does not certify all generic callback domains. Required whole-source,
callback-wiring, prelude-adaptation, and raw-output framing/freshness gates
guard the new export. See the [slice boundary and regeneration notes](../../spec/sail/STR_EXECUTION.md)
for the exact compatibility adaptations and outstanding composition work.

`STRMemoryBridge.lean` now composes that instruction with the complete original
`aset_Mem` body in the same generated state. An explicit width-checked binding
connects the instruction's callback to the concrete callee; the STR64 theorem
discharges its 64-bit/eight-byte check. The aligned normal path retains the
feature query, endian query/conversion, alignment check,
and final `MemSingle` callback in order, including all intermediate state
changes. Three exact generated Boolean expressions are explicitly repaired after
discovering that Sail 0.20.2's Lean output eagerly lifts effects from otherwise
short-circuiting operands. Normal access correctly skips SCTLR_EL2; a true
NV2-register endian branch skips BigEndian. The syndrome's EL0/EL1 condition
is similarly guarded, as is the concrete HasArchVersion query. The entire raw
function export is pinned and independent framing/mutation gates admit only
these three repairs. This is not a general
compiler-correctness or old/new-prelude proof.

The final memory callback remains arbitrary, with its exact success/error
state; earlier failures and an unaligned first-byte write-then-fail also have
checked rules. Thus this boundary supplies no transactional-failure assumption
for widening/reordering stores. `STRMemSingleBridge.lean` now composes through
the complete original MemSingle body under arbitrary deeper callbacks. It
retains the size/alignment assertions, full address/fault/access descriptors,
translation before abort handling, shareability-dependent ProcessorID then
exclusive clearing, the three distinct tag-path ZeroExtend actions, and the
final `_Mem` result. Abort/TagCheckFail callbacks that return normally permit
the original body to continue; no architectural non-return axiom is assumed.

Endian/alignment and deeper MemSingle implementations, real translation,
physical-memory routing, full-state refinement and events/CAT remain open.
Whole-source/type/alias/callback/framing mutation gates and standard-axiom
checks protect the conditional boundary. Original Sail bodies are unchanged;
the three generated Lean expression repairs are explicit compatibility changes.

`STRConcreteHelpers.lean` additionally binds the actual original HaveNV2Ext
and ZeroExtend__0 bodies. The feature closure retains all five configuration
declarations, which this exporter represents as mutable Boolean registers:
only the selected v8.4 flag is required for NV2, at the query state, with
true/false/missing cases distinguished. Default true values do not prove
hardware capabilities or old/new configuration correspondence. The binding
does not initialize or reset state. The 64-to-64 extension theorem discharges
the three tag-path extension actions without assuming arbitrary callbacks
pure; their full virtual address is retained. MTE/tag/translation/RAM and
architectural ordering remain open.

`SpanRefinement` in `MemoryBridge.lean` connects this sequential eight-byte effect to
the existing `Oak.SpanArguments.storeBytes` model used for owned-array/span
write-back. Every byte's optional lookup is exact, and the total byte view
commutes with the Oak store for any caller-supplied fallback. Byte presence is
tracked separately: the value view and presence together determine the
partial map, while a checked counterexample shows that an absent byte and an
explicit zero byte can have identical total views. Neither presence nor the
fallback grants allocation, ownership, or access authority. The actual
generated wrapper result, its selector-initialization premise, and pre-call
endian conversion compose with this correspondence. The existing Oak law
for disjoint eight-byte elements transports to the Sail map.

Two further checked limits matter for optimization: distinct starting
addresses one byte apart can overlap and make store order observable, while
successive stores at the same address leave only the last value in the final
map. The latter equation does not justify deleting a BBM break store. Even
the complete sequential byte map omits intermediate architectural events and
concurrent observers. These are width-eight model-to-model proofs, not a Go
executor/call-summary refinement, real frame/span placement, or permission to
reorder published memory. The strict BBM admission boundary is unchanged.

`SpanStateBridge.lean` strengthens the sequential connection with an
**independently supplied** Oak byte memory, rather than defining it as a view
of Sail's map. Its `Related` predicate requires the actual generated
RAM-selector entry and a present, equal byte at every address of a supplied
aligned span of 64-bit elements. The span has a u32 length and its full
extent fits in the 52-bit physical range. In-range element addresses are
proved aligned and representable before conversion to the wrapper's 56 bits.
`writeElement_simulates` connects an actual generated `__WriteMemory` call to
the existing Oak byte store and preserves this relation. By induction,
`writeElements_simulates` composes any finite list of in-range calls in the
same order, retaining selector initialization, every non-memory runtime
field, and exact optional lookups outside the span.

Kernel-checked examples exercise an initialized two-element span, repeated
and distinct indices, the last representable physical element, an empty
span, absent and mismatched bytes, and a wrong selector. Oversized and
misaligned span descriptions contradict the premises. A separate negative
example establishes that the raw generated wrapper still writes outside an
empty span: the supplied in-range indices are **not** a bounds check or
ownership certificate implemented by Sail. This relation does not derive
source guards, allocation, actual frame placement, address translation, or
the store list from native execution. Its values are already in the
wrapper's little-endian byte order. It only relates the pinned Lean runtime;
its Unit tags do not discharge Lem's real tag-map/undefined-bit gap. Neither
finite sequential composition nor preservation of final state supplies
architectural events or justifies BBM break elimination. The new module and
its examples are required by the existing Sail bridge CI build. Checked
axiom reports restrict the composition theorem and its concrete execution
examples to Lean's standard `propext`, `Classical.choice`, and `Quot.sound`;
no `sorry` or native-evaluation axiom is admitted by those reports.

Alignment, normal fault-free translation and PA/default-RAM provenance,
special-route exclusion, dynamic instruction-to-wrapper reachability, and
architectural RAM effects remain open. The sequential byte updates prove
neither atomicity/non-tearing nor architectural event count/identity, CAT
membership, visibility, completion, or publication. The C runtime and Arm's
concurrent memory model are outside this new theorem's semantics.

`TestSailLemRAMTraces` now executes the separate **Lem request interface**:
Lem translates the whole hash-pinned official `aarch64_extras.lem`, and an
OCaml harness links its actual `write_ram` to Sail 0.20.2's prompt runtime.
The event matcher, bind, byte conversions, and instruction-kind sources are
checksum-pinned in both Lem and installed generated OCaml form. CI installs
Lem 2026-05-01 and makes this oracle mandatory in its own job. The harness
checks exact plain-write address/data request order, little-endian bytes,
missing/reordered/duplicated/extra events, and mismatched kind/address/size/data.
Mutated wrappers must compile and then fail a trace assertion.

The results expose limits a future event bridge must preserve: the wrapper
discards the data-write Boolean acknowledgement, so either value returns
normally; `hasTrace` includes `Fail` and `Exception`, not just `Done`.
An undefined address fails before any event, while a non-byte-sized value
fails after its address request. Undefined data bits can remain in a byte
request, and this external interface does not itself require the payload's
byte count to equal its declared size. The RAM selector and address-width
argument are ignored. These malformed-input cases describe the external
interface, not well-typed Sail calls. Two sequential calls retain both request
pairs even when final RAM contents could discard the first value.

This is bounded executable regression evidence, not a kernel proof of Lem,
OCaml, or the runtime, nor a Lean-to-Lem or ASL-to-CAT refinement. An address
request plus a data request are not two architectural writes; even a normal
wrapper return is not evidence of architectural commitment or publication.
No new optimizer permission or strict-profile admission follows from this
oracle. Full instruction reachability and architectural event interpretation
remain open.

`TestSailLemWriteMemoryTraces` extends executable evidence one call boundary
up: the actual source-audited `__WriteMemory`, `__WriteRAM`,
`__TraceMemoryWrite`, and `__defaultRAM` declarations are generated by Sail's
**prompt**, not sequential, Lem backend. The test copies their contiguous
block from `arm_primitives.sail` unchanged, adding only the standard prelude
and decreasing bit order; it audits both the original official definitions
and the standalone generator input. The whole fragment exported from Sail,
but its unrelated `FPAdd` external prevented Lem-to-OCaml translation. This
memory-only extraction adds no floating-point or memory-effect stubs.
The two additional generated-code support modules are translated from their
checksum-pinned Lem sources rather than replaced by empty implementations.

The executable wrapper requests `Read_reg("__defaultRAM")` before its plain
write address and data requests. Missing, repeated, wrong-name, or reordered
responses do not form the expected normally returning trace. Two calls retain
two distinct read occurrences and both write-request pairs; different selector
responses and a false write acknowledgement remain possible. A wrong
register-value constructor fails the read before any RAM request. Importantly,
the generated conversion checks the `Regval_bitvector_56` constructor but not
the enclosed bit-list length: a malformed tagged selector is still accepted
and ignored downstream. An undefined address fails after the read; malformed
data can fail after the read and address request. Compiled Sail-source mutants
that bypass the read, duplicate the write, or change address/data must fail
trace assertions, not merely fail to build.

Prompt matching alone does not supply a register-state interpreter. An
unanswered Lem read is pending, unlike Lean's missing-register error; an
accepted response does not prove initialization, width, or state provenance.
This oracle adds neither a Lean/Lem refinement proof nor
instruction-to-wrapper reachability, architectural write commitment, CAT
events, atomicity, or BBM publication. The strict verified profile is unchanged.

`TestSailLemStateReplay` now exercises Sail's own `emitEventS` and `runTraceS`
with the **generated** `register_accessors` and a supplied generated register
state. Both original runtime files (`sail2_state_lifting.lem` and
`sail2_state_monad.lem`) are checksum-pinned. The general `liftState` function
cannot be translated to OCaml because it uses the unbounded `universal` set;
the test extracts only the original imports and independent trace-replay
definitions, unchanged, and translates the whole state-monad support file.
It neither substitutes a `Choose` implementation nor checks `liftState`.

The state oracle requires both `runTrace = Some (Done ())` and a successful
`runTraceS`. It checks exact little-endian byte-map contents and presence,
untouched bytes outside the write, register preservation, and generic runtime
tag updates. Runtime source mutations that ignore selector equality, accept
false write acknowledgements, drop bytes, or preserve tags must still compile,
pass the prompt checks, and then fail a state assertion. The tests expose why
neither replayer alone is sufficient: prompt matching accepts a state-inconsistent
selector or false acknowledgement; state replay accepts missing/reordered
address requests or an altered write kind. It also processes an injected
register write that the actual wrapper never requests. The conjunction rejects
these cases and an erased first write in a two-call trace, even though the
two-call and last-call-only replays have equal complete final model states.

The remaining state relation is deliberately not claimed. Lem's plain write
clears its **generic runtime tag map** to `B0` over the declared range; the
pinned Lean `SequentialState.tags` is just `Unit`. Lean's tag-preservation
footprint is not a proof of this Lem tag effect, and neither is an Arm MTE
allocation-tag model. Lem bytes can also contain undefined bits that Lean's
`BitVec 8` cannot directly represent. Even the generated Lem register record
can hold a malformed-length bit list: both replayers accept a matching
malformed selector. Consistency with supplied model state proves neither
well-formed initialization nor architectural provenance. This is executable
evidence for the selected wrapper/state interface, not a kernel-checked
Lean/Lem state refinement, allocation/ownership authority, dynamic ASL trace,
concurrent ordering, completion, or page-table publication.

`MemoryEventProjection.lean` adds a kernel-checked conditional projection of
a **supplied** prompt-event view. It recognizes exact selector-read/plain
EA/plain-data triples, checks lossless reconstruction, and retains absolute
source positions, selector responses, PA, size, payload, and acknowledgement.
Concatenation offsets the right-hand positions by the left trace's length;
even identical same-address writes remain distinct occurrences. A separate,
externally supplied expected-call list detects erased or reordered differing
calls. Swapping identical calls is not observable without further identity
evidence. A failed scan retains already matched triples and the next unmatched
position, not an invented architectural exception.

This is not a verified Lem importer or a proof that an instruction produced
the supplied trace. Selector and payload types are abstract: no width,
defined-bit, byte-count, or initialization check is implicit. False write
acknowledgements remain accepted by structural projection. A distinct
successful-replay contract requires both valid projection and caller-supplied
state replay evidence; it does not derive those premises. Architectural write
commitment, CAT W/TTD classification, coherence, translation/cacheability,
invalidation scope, and the Lean/Lem tag-state relation remain open. This
projection licenses no optimizer reordering.

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
the pre-`Mem` Sail request proves successful architectural memory execution,
PTE provenance/alignment beyond the source base fact, virtual-to-physical
translation, endianness, faults, permissions, tags, exclusives, MMIO, CAT `ca`/`inv-scope`
membership, TLBI effects, DSB completion, publication, or ISB synchronization.
The Darwin/ARM64 Mach-O oracle now requires the same complete BBM words, guard,
and trailing trap in a single-leaf instruction section, with its sole external
symbol at the start and no text relocations. It also pins the six barrier
leaves, TLBI leaf, context-sync slice, and both cold-entry examples. Metadata,
relocation, and instruction mutations must fail. The strict verified profile
still refuses the trusted BBM object on both ELF and Mach-O. This executable
source-to-object regression witness neither proves the final linked bytes nor
executes privileged code; a privileged Apple EL2 execution gate remains open.

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

`Oak.AArch64AddressRelocation` closes one additional two-word arithmetic seam
for the executable resolver's `adrl21`. It admits exactly an `ADRP` and
unshifted 64-bit `ADD` using one non-SP destination/base register, proves the
signed 21-bit page patch and low-12 patch preserve all fixed/register fields,
and proves decoding reaches the exact target. The production helper uses
uint64-safe directional arithmetic, requires the whole eight-byte pair to fit,
round-trips before mutation, and its boundary decisions are kernel-pinned.
This is not symbol/layout authority, relocation-record or file-format
correctness, loading, register execution, whole-resolver transactionality, or
a whole-link theorem.

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
The separate `lowerF64_eval` family proves binary64 `+`, `-`, `*`, `/`,
ordered `Oak.FloatOps.fma64`, negation, `abs`, and `copysign` over binary64
parameters, already-rounded bit literals, straight-line local substitution,
and leaves from the proved widening family. `lowerF64Condition_eval` adds all
six comparisons and recursive pure Boolean guards; `lowerF64Flow_eval` adds
arbitrary finite value-position condition trees. Thus
`f64(a + b) * x + y` retains and composes the exact
`fadd32`, `fcvt64`, `fmul64`, and `fadd64` nodes, while explicit FMA remains a
single ordered `fma64` node. The widened leaf starts in its own initial binary32
parameter scope; this is not arbitrary mixed-width local sequencing.
This is deliberately still a first slice: decimal parsing into the literal
bits, all other conversions, spans, effectful/statement conditions and arms,
borrowing/recursive/effectful calls, and vector operations remain related to
the extraction by tests rather than this theorem. The binary64 sign and
comparison results are carrier/shape refinements: they do not prove that the
verifier's xor/and/comparison expansion implements Lean Float, IEEE behavior,
hardware, or NaN-payload behavior. Division likewise proves operation identity
and operand order through the shared Lean carriers, not independently
correct-rounded IEEE division.

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
   closes binary64 `+`, `-`, `*`, `/`, ordered FMA, negation, `abs`, and
   `copysign` over parameters, bit literals, widened leaves, and pure locals.
   Its condition/flow theorems add all six comparisons, pure Boolean guards,
   and arbitrary finite value-condition trees, pinned to exact verifier
   renders and default/bits-mode extraction. These are carrier/shape
   refinements, not proofs that verifier bit expansions implement Lean Float,
   IEEE behavior, NaN payloads, or hardware. Decimal parsing, all other
   conversions, memory, effectful or statement conditions/arms,
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
   decided). GCC's rv64 `lr.w`/`sc.w` loop is likewise parsed, checked, and
   proved. GCC 13 prints that RTL template as semicolon-separated statements
   between two numeric labels on one physical line; the translation validator
   splits those statements and resolves both local-label directions before it
   builds the proof unit. **Item complete** for the helpers the prelude has.
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
