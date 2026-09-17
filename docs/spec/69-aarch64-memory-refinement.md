# AArch64 memory refinement: compiler and machine evidence

This chapter begins the refinement from Oak's language-level memory model
(chapters 65–68) to the AArch64 machine profile intended for the operating
system.

The governing rule is:

> A correct source memory model is useful only if the compiler and target
> preserve it.

This layer deliberately uses **several independent forms of evidence** rather
than treating one assembly snapshot as a proof of the entire Arm memory model.

## 1. Evidence layers

The current refinement stack is:

```text
Oak source atomics
        |
        v
C11 explicit atomics             executable backend mapping
        |
        v
Clang AArch64 assembly           implementation witness
        |
        +----> instruction-family admission checks
        |
Oak language execution model
        +----> SB / MP / LB / IRIW small-state litmus checks
        |
Lean AArch64 local-order model
        +----> kernel-checked instruction-class capability proofs
        |
Lean Arm ordered-before projection
        +----> inductive MP / SB / IRIW / DMB / full-DSB proofs
        +----> conditional per-old-event stage-2 BBM projection
        |
Pinned CAT sources + cat2lisp AST
        +----> byte identity + structural projection certificate
        |
Oak barrier words -> Arm Sail decoder
        +----> kernel-checked operation / domain / access type
        +----> fail-closed Oak capability + decoded DMB/DSB order classes
```

These layers make different claims.

- C11 lowering verifies Oak emits the requested C memory order exactly.
- Assembly inspection verifies the current compiler emits an admitted AArch64
  instruction family for that C operation.
- Lean proves the **abstract admitted instruction class** provides the local
  acquire/release/RCsc capabilities Oak requires.
- Litmus tests verify the language model permits and forbids the intended
  outcomes.
- Lean proves the corresponding machine outcomes from the `bob`, `DSB-ob`,
  `obs`, and irreflexive/transitive `ob` consequences of Arm's official
  A-profile model.
- Lean separately proves a BBM-shaped local skeleton from DSB ISH-classified
  occurrences and externally classified descriptor/TLBI events, corresponding
  to the ordered operands of stage-2 break-before-make.
- Herd's pinned parser structurally certifies that the exact CAT sources contain
  the restricted scalar consequences and their route into `ob`, and separately
  pins the syntax of the `BBM` relation.
- Lean generated from the Arm Sail fragment proves Oak's six barrier words
  decode to their intended DMB, DSB, or ISB operation and option. The decoded
  records refine fail-closed into Oak's capability classes; the three DMB
  records index the restricted `bob` theorem and both full DSB records index
  the restricted `DSB-ob` theorem.

No one of these alone is called a complete C/LLVM/Arm axiomatic refinement
proof.

## 2. AArch64 OS-profile acquire semantics

Oak's AArch64 OS profile requires RCsc acquire for ordinary acquire and seq-cst
loads.

The admitted scalar acquire load is:

```text
LDAR
```

`LDAPR` is **not** admitted as an interchangeable implementation of Oak acquire
in this profile. LDAPR has RCpc/AcquirePC semantics rather than the RCsc acquire
class tracked by Oak's machine contract.

This deliberately gives the privileged OS profile a simple, reviewable ordering
rule. A future weaker RCpc source operation can be added explicitly if there is
a demonstrated performance need and a separate semantic contract.

## 3. Baseline ARMv8-A scalar mapping

The assembly gate cross-compiles Oak-generated C with:

```text
clang --target=aarch64-none-elf -march=armv8-a -ffreestanding -O2
```

The admitted scalar families are:

| Oak operation | required baseline family |
| --- | --- |
| relaxed load | `LDR` |
| acquire load | `LDAR` |
| seq-cst load | `LDAR` |
| relaxed store | `STR` |
| release store | `STLR` |
| seq-cst store | `STLR` |
| acquire fence | `DMB ... ISHLD` |
| release fence | `DMB ... ISH` |
| acq-rel fence | `DMB ... ISH` |
| seq-cst fence | `DMB ... ISH` |

The gate rejects `LDAPR` for Oak acquire/seq-cst loads.

Sequential consistency is **not** reduced to one local instruction property.
The global SC relation and read-visibility constraints remain those of chapter
68; the table above records only the target's local operation component.

## 4. Baseline RMW and compare-exchange

Without LSE, the admitted baseline implementation is an exclusive loop.

Relaxed RMW/CAS must use the relaxed pair:

```text
LDXR
STXR
```

Acquire-release and seq-cst RMW/CAS must use:

```text
LDAXR
STLXR
```

The source CAS is strong. The generated loop therefore retries store-exclusive
failure as needed rather than exposing architecture-level exclusive failure as
an Oak CAS failure.

CAS retry count remains potentially unbounded under contention. Nothing in this
mapping changes the realtime rule that lock-free is not equivalent to bounded
WCET.

## 5. ARMv8.1-A + LSE performance profile

The same Oak source is separately cross-compiled for:

```text
-march=armv8.1-a+lse
```

The performance profile expects the compiler to use the single-instruction LSE
forms where available:

| Oak operation | admitted LSE family |
| --- | --- |
| relaxed fetch-add | `LDADD` |
| acq-rel / seq-cst fetch-add | `LDADDAL` |
| relaxed strong CAS | `CAS` |
| acq-rel / seq-cst strong CAS | `CASAL` |

This is both a correctness and performance regression gate: an unexpected
fallback to an out-of-line runtime or unnecessary generic dispatch is visible.

The language semantics do not require LSE. Baseline LL/SC and LSE are two
machine representations of the same Oak atomic operation.

## 6. Target lock-free admission

The cross-target compilation includes compile-time assertions that Oak's current
v1 atomic carriers are always lock-free for the AArch64 target profile:

```text
u8
u16
u32
u64
```

Signed carriers have the same widths/storage requirements.

This converts lock-freedom from an assumption into a target admission check for
the compiler/architecture tuple exercised by CI.

It does not imply arbitrary aggregate or pointer atomics are lock-free, and it
does not yet prove a cycle-level WCET bound.

## 7. Litmus outcomes

`semir/memory_litmus_test.go` exercises canonical small-state outcomes using the
same execution/HB/MO/SC validators that define Oak's language model.
`Oak.AArch64WeakMemory` proves the matching forbidden machine outcomes from the
ordered-before projection used by Arm's official `aarch64hwreqs.cat` and
`aarch64.cat` model.

The assembly litmus programs in `spec/litmus/aarch64` run with Herdtools7 and
that repository's official `aarch64.cat`, both fixed at commit
`76d5bd259d4c4b553a0f52158b9638559b79a5b5`.  The gate requires `Never` for
the MP stale-payload, STLR/LDAR SB both-zero, DMB ISH/SY SB both-zero, DSB
ISH/SY SB both-zero, load→DMB ISHLD→store cyclic, and LDAR IRIW split
observations. It requires `Sometimes` for LDAR/STLR LB both-zero,
store→DMB ISHLD→load SB both-zero, and store→ISB→load SB both-zero. Thus an
oracle that rejects every weak-looking execution, treats ISHLD as a full
barrier, or treats a bare ISB as a data fence cannot pass. There are eleven
scalar official-model cases. Two additional byte-pinned tests from the
official Herdtools7 AArch64-BBM catalogue exercise VMSA descriptor updates,
for thirteen total: `MP+tlbi-sync.ishsptev0pteoa.v1+pos` forbids its stale
result (`Never 0 9`, hash `3334f24571de5375d4587a1f8961673f`) without a BBM
warning, while `CoRR+PteOA.DB0` permits the unsynchronized result (`Sometimes
1 3`, hash `6be305e913d02515c5f0e3e4bc81ef26`) and emits exactly
`Flag Warning-BBM-expected`. The gate reads each source through `git show` at
the validated pin, requires its exact blob identity, and byte-compares the
checked-in copy before invoking Herd.

### 7.1 Message passing (MP)

Release/acquire publication establishes:

```text
payload write HB payload read
```

when the acquire observes the release flag publication.

### 7.2 Store buffering (SB)

For seq-cst stores followed by seq-cst loads, the both-zero outcome is forbidden.
The test exhausts every candidate global SC order and verifies none satisfies
the witness constraints.

For all-relaxed atomics, the both-zero outcome remains allowed and data-race-free.
This guards against accidentally making relaxed atomics stronger than specified.

### 7.3 IRIW

Two seq-cst readers cannot observe two seq-cst writers in contradictory orders.
The test exhausts all candidate global SC orders for the six-event execution
and verifies the split observation has no valid witness.

### 7.4 Load buffering (LB)

The seq-cst both-zero load-buffering outcome is allowed when both loads occur
before both stores in one valid global order.

This negative/positive pair matters: the checker must implement Oak's actual
memory contract rather than merely rejecting every weak-looking outcome.

## 8. Formal instruction-class and weak-memory models

`spec/lean/Oak/AArch64Memory.lean` models local ordering capabilities:

```text
acquire
release
RCsc acquire
```

and instruction classes for:

- `LDR`, `LDAR`, `LDAPR`;
- `STR`, `STLR`;
- `DMB ISHLD`, `DMB ISH`;
- baseline exclusive load/store pairs;
- LSE relaxed/acquire/release/acq-rel RMW classes.

Lean proves:

- baseline load mappings satisfy their required local order;
- baseline store mappings satisfy their required local order;
- baseline fence mappings satisfy their required local order;
- every baseline RMW order maps to a sufficient exclusive pair;
- every LSE RMW order maps to a sufficient LSE class;
- `LDAR` satisfies Oak's RCsc acquire requirement;
- `LDAPR` does **not** satisfy that profile requirement;
- seq-cst load/store/fence select the intended local instruction classes.

`spec/lean/Oak/AArch64WeakMemory.lean` defines the least transitive relation over
the exact global consequences used from Arm's model: `bob` edges for STLR,
LDAR, STLR-followed-by-LDAR, full DMB, and returning-load-before-DMB-LD;
full-DSB scalar ordering through `DSB-ob`; and external reads-from and
coherence-after edges through `obs`. A valid projected execution supplies only
Arm's external irreflexivity condition. Lean proves:

- release/acquire message passing orders the payload and forbids a stale
  initial-value observation;
- STLR/LDAR seq-cst store buffering cannot return both initial values;
- two LDAR seq-cst readers cannot make the IRIW split observation;
- a full DMB in each thread also excludes the store-buffering outcome;
- a full DSB in each thread excludes the same outcome through its distinct
  `DSB-ob` constructor, without making a completion claim;
- DMB ISHLD orders a returning load before following scalar memory, while
  neither a store nor a CAT `NoRet` load receives that edge;
- Oak's selected instruction classes are exactly STLR, LDAR, and DMB ISH for
  the corresponding source operations.

`semir/aarch64_cat_projection_test.go` mechanically ties that restricted
relation to the pinned model. It byte-compares all 156 tracked
`herd/libdir/*.cat` blobs (and rejects untracked CAT inputs), invokes the pinned
`cat2lisp` beside `herd7`, and checks the include-expanded AST for DMB ISH and
DMB SY in `dmb.full`, DMB ISHLD in `dmb.ld`, the five required scalar `bob`
arms, DSB ISH/SY membership and the full scalar `DSB-ob` arm, ISB membership
and both a dependency-sensitive `IFB-ob` arm and the exact
`DSB-ob; [IFB]; po` arm, the `bob/DSB-ob/IFB-ob -> lob -> local-hw-reqs ->
hw-reqs -> ob` and
`rf/ca -> Exp-obs -> obs -> ob` paths, `ob; ob`, and external
`irreflexive ob`. Exact AST hashes make any pin/model drift a reviewed change;
mutation checks show each required edge is fail-closed.

The full-DSB selector is now exact rather than name-based. It checks and
mutation-tests all five ordered operands of the unconditional arm:

```text
[M | DC.CVAU | IC | TLBI]; po; [dsb.full]; po;
[~(Imp & TTD & M | Imp & Instr & R)]
```

The ETS2/ETS3 conditional arm and the `dsb.ld`/`dsb.st` arms are deliberately
not folded into this projection.

The same certificate now pins CAT's exact `BBM` definition:

```text
[TLBCacheableTTD]; ca; [TLBUncacheableTTD]; ob; [TLBI];
(ob & inv-scope); [TLBCacheableTTD]
```

`Oak.AArch64Stage2Maintenance` gives those seven operands an
occurrence-indexed Lean projection. It proves that an explicit descriptor
break, DSB ISH, TLBI, DSB ISH, and explicit descriptor make construct two
local projected edges corresponding to CAT's `ob` operands for one old
cacheable TTD event, provided assumed projections of `ca` and `inv-scope` are
supplied by the architecture refinement. Those local edges now project through
the exact unconditional full-DSB arm: local `po`, decoded `dsb.full`, explicit
descriptor-write `M`, TLBI membership, and the complete destination filter are
separate one-way premises; exact-arm inclusion and CAT-`ob` transitivity finish
the recursive projection. A conditional theorem covers every make event
selected by an external `requiresBBM` predicate. It does not construct those
CAT predicates or an actual CAT execution.

Lean now also states an exact pulled-back `ProjectedCATBBM` predicate over
externally supplied occurrence sets and relations. It preserves `ca` from old
to break, `ob` from break to TLBI, TLBI membership at that same middle event,
and both `ob` and `inv-scope` from that TLBI to make before applying the final
cacheable-descriptor filter. `TraceToProjectedCATBBMSoundness` no longer takes
a monolithic local-`ProjectedOrderedBefore`-to-`ob` premise. It factors the
local-to-CAT obligation into descriptor and TLBI set membership, local-to-CAT
`po`, decoded full-DSB membership, destination exclusion, exact-arm inclusion,
CAT-`ob` transitivity, `coherenceAfter` to `ca`, and local `invScope` to CAT
`inv-scope`. Under those fields, `projected_bbm_witness_projects_exact_cat_bbm` proves the existing
indexed witness inhabits every operand of the exact projected relation. Three
`Iff.rfl` lemmas kernel-check the fully expanded DSB source, destination, and
shared-event arm formulas. A separate lexically aware Lean source-drift guard
pins the three projected definitions' spelling beside the already pinned
official CAT AST; it rejects
comments and literal/identifier hiding, but does not claim to decide Lean
command quotations, macros, conditional commands, or elaboration.

The CAT certificate separately pins the complete outer classification seam:
`TLBUncacheableTTD`, `TLBCacheableTTD`, all six arms of
`TTD-update-BBM-cand`, and the exact three-operand
`TTD-update-needsBBM`. It also pins
`flag ~empty (TTD-update-needsBBM \ BBM) as Warning-BBM-expected`, including
its flagged status. This is a diagnostic warning in the official CAT model,
not an execution-validity axiom.

`maintained_old_events_exclude_projected_cat_bbm_warning` mirrors that set
difference propositionally. It proves the warning shape empty if every old
event has a local maintenance witness, official-needs membership implies the
local `requiresBBM` predicate, and every `ProjectedBBM` witness implies
official `BBM` membership. Those three premises are explicit and remain
unproved refinement obligations; the theorem does not identify Oak events or
relations with the CAT execution.

For the exact pulled-back relation,
`maintained_old_events_exclude_exact_projected_cat_bbm_warning` removes the
monolithic `ProjectedBBM -> catBBM` premise: local maintenance uses the supplied
needs relation directly, and the factored one-way fields construct
`ProjectedCATBBM`. This is still conditional. It neither proves that the needs
relation is official `TTD-update-needsBBM` nor that any supplied predicate came
from an official CAT execution.

The concrete wrapper keeps an external instruction-word projection beside
that sequence. It requires the break index to carry exact `STR XZR,[X0]` word
`0xf900001f` and abstract uncacheable-descriptor action, both DSB ISH indices
to carry exact word `0xd5033b9f`/barrier-action witnesses, the TLBI index to
carry exact VMALLS12E1IS word `0xd50c83df` and `Action.tlbi target`, and the
make index to carry exact `STR X2,[X0]` word `0xf9000002` and abstract
cacheable-descriptor action. No word is used to derive its action. The
projection theorem preserves that same TLBI event and target through the BBM
projection, and a separate theorem exposes all five exact words at the same
indices as the ordering witness. The four `po` links make break, pre-DSB,
TLBI, post-DSB, and make pairwise distinct; the old event is excluded because
the abstract `coherenceAfter` relation has no irreflexivity premise.

The generated Arm Sail bridge now takes the two exact STR words one step
further. It proves their SEE-1277 STR64 unsigned-offset field decodes and the
selected store arm's address/data arguments immediately before `Mem`: with explicit
register inputs, `STR XZR,[X0]` requests `(X0, 0)` and `STR X2,[X0]` requests
`(X0, X2)`. The official-source gate pins the unexpectedly named
`signed_postidx` decoder route, its fixed normal 64-bit store parameters, X31's
zero behavior, and the final `Mem(address, 8, AccType_NORMAL) = data` call.
The Sail facts decorate the external descriptor occurrences by conjunction;
an extraction theorem returns each original word/action premise unchanged.

A second generated projection follows only the conditional argument flow of
the ordinary aligned size-eight route. Given an externally supplied 52-bit
physical address from a normally returning, nonfaulting translation, it proves
that the selected pre-`__WriteMemory` arguments are the address zero-extended
to 56 bits and the post-endian 64-bit data. Consequently the exact break store
selects `(ZeroExtend(PA), 0)` under either endian, the little-endian make store
selects `(ZeroExtend(PA), X2)`, and the big-endian make case selects the exact
eight-byte reversal of X2. A known-byte theorem fixes the reversal direction.
The next generated pure projection follows the pinned no-device wrappers and
selects the external `write_ram` arguments
`(56, 8, defaultRAM, ZeroExtend(PA), data)`, with `defaultRAM` explicit rather
than inferred from a runtime register state. Break data is still zero and make
data retains the same endian-dependent result.

The official-source oracle pins complete normalized bodies and exact
signatures for `BigEndianReverse`, `aset_Mem`,
`AArch64_aset_MemSingle`, `IsFault`, `aset__Mem`, `__WriteMemory`, and the
no-device `__WriteRAM` wrapper. It also pins the 52-bit `FullAddress` field,
the three overload routes, endian/aligned selection, translation/fault,
exclusive, MTE, trickbox, counter-register, size-16 split, direct-write, model
file-selection, exact `__defaultRAM : bits(56)` declaration, ordered wrapper
bodies, and external `write_ram` seam. These checks justify the conditional
argument projections only. Alignment and route/call reachability, translation
correctness, the supplied PA's or default-RAM value's provenance, wrapper or
external return, RAM mutation/byte placement/atomicity, and event creation are
not outputs of the pure functions.
The occurrence-level break/make decorators therefore require an opaque
`AlignedNormalWriteMemoryRoute` premise indexed by the same occurrence,
virtual address, endian result, physical address, and pre-endian data. Their
extraction theorems return that premise and the original descriptor occurrence
unchanged; adequacy of the route predicate against Arm execution remains open.

Lean now also spells out the two pinned CAT descriptor-set formulas as
occurrence predicates: uncacheable is `TTDINV | TTDAF0`, while cacheable is
`(TTD & M) \ TLBUncacheableTTD`. A one-way
`DescriptorActionCATTagSoundness` premise maps an already classified Oak
descriptor action into those projected predicates. Under that premise the
exact break/make occurrence wrappers and the old/break/make fields of a
`ProjectedBBMWitness` inhabit the three descriptor filters used by CAT's
`BBM` expression. The CAT AST/hash gate and a separate lexically aware Lean
source-drift guard pin both formulas and reject operator, atom, operand-order,
and set-difference direction drift. This source guard checks spelling and
lexical visibility, not command elaboration.

The primitive `TTD`, `M`, `TTDINV`, and `TTDAF0` tags and the one-way soundness
map are still external execution-refinement inputs. CAT `po`, full-DSB and
source/destination membership, exact-arm inclusion in `ob`, `ob` transitivity,
`ca`, TLBI, and `inv-scope` are likewise premises rather than derived relations.
There is no reverse classifier, no STR or descriptor-value derivation of a tag,
and no claim that an Oak occurrence is an official CAT event. In particular
this step does not establish address-to-slot/PTE provenance, adequacy of any
projected predicate against an official execution, completion, invalidation,
or publication.

The checked-in `stage2_bbm_ordering_slice` gives that shape a deliberately
incomplete Oak source witness. Its parameter carries `[* align 8]u64` and its
assertion establishes a nonempty span; those facts do not establish live PTE
provenance. The freestanding ELF/AAPCS64 symbol is pinned in full to eight words:
`CBZ w1`, the five exact store/system words above, `RET`, and the trap `BRK`.
The bootstrap C/Clang lane independently retains the same fall-through
store/system order and no ISB. The two local equalities are recorded in
`Oak.Forwarding` (`unsigned_lt_one_is_zero`, `zero_index_store`) and their
lowering/matcher cases are fail-closed tests, but DSB places this whole function outside the semantic
verifier's decided subset: its verdict remains **trusted**, not proven.
Dynamic PC/object trace extraction, reachability and effects of the official
ASL calls after the selected external `write_ram` arguments, and every
instruction-to-action classification remain
compiler/execution-refinement premises.

The Darwin/ARM64 Mach-O path now has an independent exact-object regression
gate in `compiler/e2e_native_macho_ordering_test.go`. It cross-emits eleven
single-leaf objects: the six barriers, VMALLS12E1IS, the context-sync and BBM
slices, and both cold-entry examples. Each whole instruction section must
match its expected words, including the BBM guard and trailing trap. The oracle
requires an ARM64 relocatable object, one external section-defined entry at
the section start, and no text relocations; it does not infer Mach-O function
lengths from `RET` or discard unexpected padding. Negative tests reject changed
metadata, extra symbols, relocations, and altered/missing/reordered instructions.
The BBM body remains trusted and the strict verified profile must refuse its
object on both freestanding ELF and Darwin Mach-O. These checks need neither
Clang nor an Apple host and never execute privileged instructions. They provide
source-to-relocatable-byte evidence, not final linked-image correctness or a
privileged Apple EL2 execution gate.

The BBM guard now has a narrow generated Sail bridge of its own.
`Oak.AArch64CompareBranchEncoding` proves the `CBZ W` field packer and exact
`CBZ W1,+28` word (`0x340000e1`); generated Lean recovers its register and
signed byte displacement. The generated zero predicate equals
`Oak.AssemblerSemantics.cbz` on the supplied register's low 32 bits, with
register 31 treated as WZR rather than SP. For arbitrary upper X1 bits and a
supplied 32-bit span length, the guard predicate is true exactly when the
length is zero. `CBNZ W`, `CBZ X`, and the zero word are rejected by this
restricted decoder. The source gate pins Arm's SEE-1176 clause, complete
compare-branch decode/execution bodies and signatures, `aget_X`/`X`, and
`IsZero`; the regeneration gate checks the committed Lean against Sail output.
This proves the pure predicate and displacement, not the runtime provenance of
X1 or PC, execution of `PostDecode`/`BranchTo`, fall-through, arrival at the
trap, or absence of memory effects along a dynamic trace. The whole BBM body
therefore remains outside the strict verified profile.

The trailing `BRK #1` now has a separate encoding and pure exception-argument
bridge. `Oak.AArch64BreakpointEncoding` proves the `BRK_EX_exception` field
packer and exact word `0xd4200020`; generated Sail Lean recovers immediate one
and proves the selected target EL, 25-bit syndrome, supplied preferred-return
address, and zero vector-offset argument. The immediate occupies precisely the
low 16 syndrome bits, with nine high zero bits. At supplied EL2 the selected
target remains EL2 regardless of the supplied routing controls; EL0/EL1
selection follows the pinned `EL2Enabled`, HCR bit 27, and MDCR bit 8 rule.
The source gate pins Arm's SEE-1747 clause, complete decode/dispatch/software-
breakpoint/exception-initializer signatures and bodies, EL constants, and
`ExceptionRecord` layout. All 65,536 immediate encodings are checked, and
mutations of routing, syndrome, return address, and source visibility must fail.
These are selected argument components, not a complete exception record or
packed ESR. BTI compatibility effects, `PostDecode`, state/address provenance,
actual `AArch64_TakeException`, and handler behavior remain outside the proof.
In particular, architectural BRK is not proved to be an irreversible halt:
Oak's non-resuming runtime trap contract is still needed. No BBM memory-ordering
or proof-admission claim follows from this slice.

The two official catalogue tests validate generic pinned CAT BBM ordering and
diagnostic behavior only. Their maintenance instruction is stage-1
`TLBI VAAE1IS`, not Oak's stage-2 `VMALLS12E1IS`. They establish no Oak
store-to-TTD classification, dynamic occurrence trace, `ca`, `inv-scope`,
IPA/VMID/regime/shareability suitability, invalidation effect, DSB completion,
ISB synchronization, Sail/ASL state change, or local-`ProjectedBBM` to
official-`BBM` refinement. The warning remains a diagnostic flag rather than
a validity axiom. Apple userland cannot execute this EL2 path; Apple relevance
here is still static zero-overhead word/order evidence pending a privileged
harness.

The separate `Vmalls12e1isDsbIsbInstructionSequence` records exact
DSB-ISH, VMALLS12E1IS, DSB-ISH, and ISB word/action occurrences plus their
three program-order directions. Its completed wrapper accepts two independent
execution-level propositions: the exact post-DSB completes the exact TLBI, and
the exact ISB synchronizes context. The module derives neither proposition from
words, decoder identities, or capability Booleans; if either supplied
proposition is refuted at the selected events, the corresponding refutation
theorem prevents construction of the completed wrapper. Adequacy and provenance
of both predicates remain external. This four-instruction slice contains no
descriptor break/make or `inv-scope` evidence and is not by itself a BBM
protocol.

The same exact events now construct a narrower local ordering projection
corresponding to the pinned CAT syntax. The post-TLBI DSB ISH places the exact
TLBI before the exact ISB in Oak's restricted shape for the first `DSB-ob` arm,
whose official source set explicitly includes `TLBI`. Given a separately
supplied occurrence after that ISB and its program-order edge, Oak also
constructs the local shape corresponding to `DSB-ob; [IFB]; po`. The CAT gate
pins and mutation-tests that complete official arm. `ProjectedTlbiDsbOb` and
`ProjectedTlbiIfbOb` retain the same instruction indices and exact word/action
witnesses, but prove local ordering only: `DSB-ob` is not DSB completion and
`IFB-ob` is not architectural context synchronization. Official CAT set
membership, including the DSB arm's destination filter and ISB membership in
`IFB`, remains an execution-refinement premise.

This is mechanical structural provenance for the restricted projection, not a
complete formal semantics of CAT. The local mapping, projection theorems, CAT
certificate, and `Oak.SequentialConsistency` remain separate proof layers so
none is silently substituted for another.

`spec/lean/Oak/AArch64Encoding.lean` and the regenerated Arm Sail bridge also
close the encoding/decoder seam for the barrier subset: the exact words for DMB
ISHLD/ISH/SY, DSB ISH/SY, and ISB are pinned to the generated encoder table and
proved to decode to the intended operation, shareability domain, and access
types. A fail-closed refinement maps only those six exact decoder records into
Oak's barrier capabilities. Sail-decoded DMB ISHLD/ISH/SY occurrences then
produce the load/full `bob` edges above, and decoded DSB ISH/SY occurrences
produce the full scalar `DSB-ob` edge. ISB is proved not to receive a DMB or
DSB data-order edge; the official CAT outcome confirms that a bare ISB is not a
data fence.

The first translation-maintenance encoding seam is separate from those barrier
capabilities and covers only the Inner Shareable spelling,
`TLBI VMALLS12E1IS`. It does not cover plain `TLBI VMALLS12E1`, whose
architectural spelling specifies local-PE invalidation and has a different
encoding.
`Oak.AArch64Encoding.tlbiVmalls12e1is` constructs the exact Inner Shareable
word (`0xd50c83df`) from the generated SYS field layout.
Generated Lean proves that exact word selects `TLBI_VMALLS12E1IS` in Oak's pure
Sail projection, while the zero word and plain `VMALLS12E1` word do not select
that target. Go gates tie the fields and nullary `Rt = 31` form to Oak's
generated Arm XML table, require the exact encoder word, independently require
plain `VMALLS12E1` to encode to the distinct `0xd50c87df`, and tie the
projection's field decode and named call target to the generic SYS clause and
nested dispatch in the pinned official Sail source.

This is syntactic call-target classification only. It does not prove EL2 access
admission, current-VMID selection, inner-shareable broadcast, invalidation of a
particular translation, absence of stale entries, or completion. The pinned
Sail target delegates to a coarse reset of its single modeled TLB; that model
effect is not used as architectural evidence. The closed source operation
`arm64.tlbi_vmalls12e1is()` now lowers through catalog-owned text, and an
independent direct-native object gate requires its complete body to be exactly
`0xd50c83df; RET`. This provides executable source-to-word occurrence evidence
for this leaf. The Sail-decorated stage-2 theorem now conditionally connects an
externally supplied exact-word/action occurrence to the BBM projection without
manufacturing that premise. A kernel-checked extraction of the dynamic
instruction occurrence and its `AArch64Stage2Maintenance.Action` classification
from the compiler/execution trace remains open.
The explicit context-sync example independently lowers to exactly
`DSB ISH; VMALLS12E1IS; DSB ISH; ISB; RET`; its Sail decorator adds only the
generated decoder and named call-target facts while returning the externally
supplied bare instruction sequence unchanged. The completed wrapper separately
retains the external completion and context-sync premises.
In particular, this result does not verify or refine the downstream OS
boot/revoke sequence, which currently emits plain `TLBI VMALLS12E1` between DSB
ISH operations.

The completion and instruction-synchronization fields are Oak profile
capabilities, not consequences of the extracted Sail artifact. Oak's pure Sail
fragment intentionally projects decoding to the operation/domain/access tuple
and omits architectural state changes and the final barrier execution call.
Therefore this bridge proves decode/dispatch identity and the selected CAT
ordering consequences, but not DSB completion or ISB context synchronization.
Those require an occurrence-indexed Arm execution rule; a positive `IFB-ob`
projection additionally requires the model's control/address or other admitted
dependency.

## 9. CI gate

The main CI workflow has an independent:

```text
AArch64 Memory Refinement
```

job. It:

1. requires Clang AArch64 freestanding cross-target support;
2. runs the Oak source -> C -> AArch64 assembly checks;
3. runs Oak's language-level memory-model litmus outcomes;
4. builds pinned Herdtools7 and runs the matching assembly cases against the
   official Arm CAT model from the same pinned checkout;
5. requires byte-identical CAT inputs and the parser-AST projection certificate.

The ordinary Go/race, Lean, and golden gates remain in place, so backend
refinement cannot replace source/compiler/formal regression coverage.

Local developers without Clang may skip the assembly tests. CI sets
`OAK_REQUIRE_AARCH64_CLANG=1`, turning absence of the cross compiler into a hard
failure rather than a skipped verification claim.
The Herd test similarly skips without `herd7` or `OAK_HERDTOOLS7_DIR` locally;
CI sets `OAK_REQUIRE_HERD7=1`, so absence, a checkout at the wrong commit, an
unparseable result, or an outcome drift is a hard failure.

## 10. What this does not yet prove

This chapter does **not** claim:

- a complete formal refinement of C11 through LLVM IR to the official Arm
  axiomatic model;
- a complete semantics-preserving translation of the CAT language or the full
  Arm model into Lean;
- a proof that STLR/LDAR/DMB executions generate the assumed Exp/W/R/L/A event
  tags, decoded barrier-occurrence relation, reads-from, and coherence-after relations;
- a proof of DSB completion or ISB context synchronization from an Arm
  execution model;
- a construction of CAT's primitive descriptor tags or the external one-way
  action-to-tag soundness premise from Oak descriptor values or STR execution,
  a proof that a concrete IPA/VMID/regime selects the required TLBI scope, or
  a proof that descriptor publication and invalidation have completed;
- a proof that the aligned, fault-free, tag-safe, non-trickbox/non-counter
  route is reached, that the supplied physical address is the translation of
  X0 or the descriptor slot, or that `__WriteMemory`/external `write_ram`
  returns and changes RAM;
- a complete live stage-2 remapping protocol or a kernel-checked compiler
  refinement proof for the TLBI occurrence beyond the executable regression
  witness;
- exhaustive compiler-version correctness;
- stochastic execution of weak-memory litmus tests on real AArch64 hardware;
- cache/coherency/DMA/device-memory correctness;
- cycle-level WCET for LL/SC retry loops;
- MMIO/barrier correctness for device registers.

The current result is stronger than source-only testing but deliberately weaker
than a full verified compiler/ISA stack.

## 11. Next steps

The next machine-memory work should add:

1. extend the mechanically pinned relation subset into a complete CAT semantics
   and construct the currently external instruction/action-to-event-tag and
   `rf`/`ca` generation seams;
2. retained assembly artifacts/version metadata so failures are diagnosable;
3. real AArch64 hardware litmus execution when a CI runner is available;
4. add the occurrence-indexed execution bridge needed for DSB completion and
   positive dependency-sensitive `IFB-ob`/ISB chains, then extend MMIO
   state/effect contracts;
5. DMA/coherency and interrupt-boundary ordering;
6. selective implementation-to-Lean refinement where the proof cost is
   justified.

Once this AArch64 refinement gate is stable, Oak has enough demonstrated
shared-memory machinery to begin `SpscRing[T, N]` as the first higher-level
lock-free proof consumer.

**Consumers (landed).** `stdlib/rings.oak` is that consumer: the SPSC,
MPSC, MPMC, and intrusive MPSC rings over caller-owned storage
(`65-machine-memory.md` §1). `compiler/e2e_rings_targets_test.go` compiles
their operations for `aarch64-none-elf -march=armv8-a` and requires the
families this chapter assigns — `stlr` (or `stlxr`) for every release
publication, `ldar` (or `ldaxr`) for every acquire observation, the
exclusive pairs or LSE forms for the claims, an exchange for the intrusive
push; the pthread harness of `compiler/e2e_rings_test.go` runs the same
rings on AArch64 hardware plain and under ThreadSanitizer, and the harness
cross-builds for `linux/arm64`. The happens-before facts they rely on are
`Oak.Rings`' instances of `Oak.HappensBefore`.

The RISC-V counterpart is `69-riscv-memory-refinement.md`.
