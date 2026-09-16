# Note: how complete is Oak's verification chain?

**Status: assessment, non-normative.** 2026-09-15, `specification` branch
at `afd2a663`. This note assesses how close Oak is to a whole-language,
source-to-linked-binary proof. It complements the artifact-by-artifact map in
`docs/spec/126-verification-chain.md`, the original audit in
`docs/notes/verification-chain-2026-09.md`, and the coverage matrix in
`docs/spec/STATUS.md`.

The percentages and scores below are judgments, not repository metrics. They
separate the existence of a verification architecture from coverage of a
particular fail-closed compilation profile and from complete closure of every
language and toolchain path.

| Scope | Assessment |
| --- | ---: |
| Verification architecture and major proof layers exist | **90–95%** |
| `-verified` native subset, source to ISA semantics | **80–90%** |
| Entire Oak language, every backend, and final executable formally closed | **55–65%** |

## 1. Summary

Oak has largely finished building the **verification system**. It has not yet
finished closing that system's trusted computing base or extending the proof
chain through every language construct, backend, object format, relocation,
and linked executable byte.

For the supported native subset, the chain is already unusually strong:

```text
Oak source and source theorem
        ↓
checked program
        ↓
source/lowering refinement
        ↓
native assembly candidate
        ↓
assembly seam checker
        ↓
semantic equivalence verifier
        ↓
Oak instruction semantics
        ↓
Arm ASL/Sail or RISC-V Sail semantics
```

The repository also labels each link as proved, refined, audited,
differential, evidenced, or trusted instead of calling the entire chain
"verified" because one model exists. That vocabulary is one of the system's
strongest design choices.

The remaining work is concentrated in six places:

1. whole-frontend implementation refinement;
2. float, SIMD, wider-integer, and remaining structural coverage in the
   source-to-verifier refinement;
3. certificate checking or refinement of the native semantic verifier itself;
4. object, executable, relocation, and linker correctness;
5. AArch64 encoding proofs comparable to the RV64 encoding bridge; and
6. paths that still rely on a system C compiler or have no native proof lane.

## 2. What is already strong

### 2.1 The proof system has the required kinds of mechanism

`oak prove` has several discharge rungs rather than one proof tactic:

- exhaustive checking over finite domains;
- bit-level decision procedures over the verifier term language;
- generated Lean statements and checked Lean proofs;
- protocol invariant and liveness exploration;
- SAT solving through Tseitin clauses; and
- LRAT certificates checked by both the Go checker and the checker written in
  Oak.

The Lean side proves the RUP, Tseitin, resolution, learned-clause, and solver
laws on which certificate acceptance relies. An external SAT solver remains
an untrusted search procedure: an UNSAT result counts only when its certificate
is accepted. Oak's own clause engine and solver can produce the same kind of
certificate.

This is a sound architectural split: expensive or complicated search may be
wrong without making a false theorem true, provided acceptance is reduced to
a sufficiently small checked relation.

### 2.2 The verified build profile is a real boundary

`oak build -verified` is not a synonym for enabling more tests. Every
reachable body must:

- lower through the native lane;
- pass the assembly seam checker; and
- receive a **proven** semantic-equivalence verdict.

A witnessed body, a trusted body, or a body left to the C backend rejects the
build and contributes to the reported burn-down list. This fail-closed policy
prevents a build from silently crossing from proved code into a weaker lane.

The policy is stronger than the current coverage. That is the right order:
unsupported programs fail instead of diluting the meaning of `-verified`.

### 2.3 Source semantics and verifier semantics substantially compose

`spec/lean/Oak/LoweringRefinement.lean` is the central source-to-native seam.
It relates:

- `evalX`, the Lean/extraction interpretation of Oak; and
- `lowerT`, the term lowering represented by `asm/verify.go`.

Its principal result, `lowerT_eval`, states that when the lowering admits an
expression and the source interpretation produces a value, evaluating the
lowered verifier term produces the same value under agreeing environments.
`asm/lowering_refinement_test.go` pins the Go lowering to the Lean
transliteration with rendered-term examples.

The covered subset is no longer a toy expression language. It includes:

- fixed-width integer arithmetic, division, remainder, shifts, and bitwise
  operations;
- integer conversions, comparisons, and Boolean operations;
- block-scoped locals, initialization, and reassignment;
- value and statement conditionals;
- integer-constant and scalar-payload-ADT matches;
- counted and data-dependent loops under the stated loop-summary reading;
- span element reads, writes, and lengths;
- owned arrays and array literals;
- records, arrays of records, records of arrays, and nested aggregate leaves;
- calls to program functions;
- calls borrowing arrays through span parameters with writeback; and
- record-returning calls.

This is enough for a source theorem, the source/verifier lowering theorem, a
native-body equivalence verdict, and an ISA bridge to compose for a substantial
native subset.

### 2.4 Native translation validation is broad

The native verifier is not limited to straight-line scalar arithmetic. Across
the two native lanes it handles substantial combinations of:

- branches and matches;
- coupled counted and data-dependent loops;
- calls and call summaries;
- aggregate state and record returns;
- span memory effects;
- atomics under the verifier's stated sequential model;
- floating-point operations; and
- SIMD operations and vector reductions.

Compiler optimizations can therefore remain proposal generators outside the
semantic trusted base. The optimizer may offer a candidate, but selection for
a verified build depends on the candidate proving equal to the stable Oak
body.

Commit `59a9ee08` is a representative example: four-vector reduction forms
for `u32` and `u64` have bit-level assembly proofs while the source rewrite is
backed by `Oak.Reduction.vector16_eq`. Later commits do not change the role of
that example; the current head is `afd2a663`.

Scalar `f32` stores through mutable spans inside loops provide another useful
boundary case. Correct stores are proven and a deliberately incorrect
operation is refuted, moving the operation from a trusted classification into
the proven native subset.

### 2.5 The ISA grounding is deep

For AArch64, Oak's instruction semantics are connected to Arm's ASL through
the generated Sail/Lean bridge. The instruction family emitted by the native
backend includes scalar, floating-point, and vector behavior, and silicon
differential testing supplies an independent execution oracle.

For RV64, the chain reaches the Sail RISC-V export. The current verification
map records:

- 53 instruction-semantics theorems; and
- 30 encoding theorems against Sail's `encdec` relation.

The RV64 bridge covers every integer instruction the verifier decides and the
pure address, alignment, extension, and truncation portions of loads and
stores. The complete Sail memory monad remains audited rather than fully
proved into Oak's flat span-memory model.

The supported subset is therefore much stronger than a proof against an
independent "RISC-V-like" model. There are explicit bridges to machine-readable
ISA artifacts.

## 3. What prevents a claim of whole-language completeness

### 3.1 The complete frontend implementation is not refined

Oak has many formalized language laws and a growing collection of
implementation-refinement theorems. It does not yet have one theorem saying
that the entire parser, resolver, type checker, borrow checker, resource
checker, effect checker, and lowering pipeline refine a complete formal
frontend.

`docs/spec/126-verification-chain.md` explicitly trusts:

- the parser;
- checker code outside the named refined decision procedures;
- parts of module loading outside `Oak.ModulesRefinement`; and
- the Go implementations of several syntax rewrites.

The distinction is visible in `STATUS.md`. Type lattices, pattern analysis,
literal fitting, record layout, selected borrow transitions, view/span rules,
alignment-fact normalization/flow/join, modules, arithmetic, and other
decisions carry implementation refinements. The alignment result is scoped:
the Lean model proves the production numeric order and weakest-fact join sound
for canonical power-of-two facts, while bounded executable examples pin the Go
helpers; shape identity and whole assignability remain outside that theorem.
Other features have models and proofs but no complete correspondence from the
production traversal and bookkeeping code to the model.

The type-lattice atom premise is now explicit rather than hidden behind the
broader compatibility relation. `Oak.TypeLatticeAtomIdentity` projects the 25
current in-package, pointer-receiver type constructors to canonical finite
keys and proves that its decision is reflexive, symmetric, and transitive;
the free-lattice soundness and completeness theorems are specialized to those
keys. A Go drift gate enumerates the complete current `Type` implementation
set, fields, and comparator cases and pins production decisions to Lean. This
is still an audited correspondence, not a theorem about arbitrary Go heap
graphs: cycles, implementations outside the package, and a universal
Go-to-key extraction remain open.

Resource checking illustrates the boundary:

- callable contracts and result identities have formal laws;
- borrowed-resource results have proved monotonicity and admission
  properties; but
- dependency tracking, suspension, provenance walking, aggregate traversal,
  and some body-validation paths are not one refined implementation.

The accurate description is therefore **formally substantial frontend**, not
yet **fully verified compiler frontend**.

### 3.2 `LoweringRefinement` has a type-coverage seam

The shared scalar universe in `Oak.LoweringRefinement.Ty` currently contains:

```text
Bool
u8 u16 u32 u64
i8 i16 i32 i64
```

It does not include `f32`, `f64`, SIMD vector types, `u128`, or all richer
language shapes.

This does not mean the native verifier cannot prove floating-point or SIMD
bodies. It can, and the native tests demonstrate that capability. It means
the clean formal composition theorem:

```text
source/extraction evaluation
        =
verifier Oak-body lowering
```

does not yet pass through `lowerT_eval` for every type the native verifier can
otherwise decide.

This is the largest remaining formal-composition gap inside the
source-to-native proof chain. Extending a verifier feature and extending the
shared refinement are separate completion conditions.

The current burn-down increments landed with this assessment:
`Oak.FloatLoweringRefinement.lowerF_eval` covers straight-line `f32` `+`, `-`,
`*`, `/`, and ordered ternary `fma` over parameters, post-rounding bit-pattern
literals, and local
declarations and rebindings. `lowerWith_eval` maintains an explicit agreement
invariant between the extraction scope and the verifier's substituted terms.
Production render tests pin the five operations, FMA operand order,
non-contraction of multiply-then-add, the literal bits, and both local forms.
`lowerWiden_eval` also composes explicit `f32`-to-`f64` widening over that
straight-line slice and pins the production `fcvt64` node and extraction's
`Float32.toFloat`. Decimal parsing into those bits, all other conversions,
memory, effectful control flow, borrowing/recursive/effectful calls, and SIMD
remain outside the theorem, so the
broader gap and score above remain. Ordered pure `f32` calls are included by
the existing call-environment refinement.
The separate `lowerF64_eval` family covers binary64 `+`, `-`, `*`, `/`,
ordered FMA, negation, `abs`, and `copysign` over parameters, already-rounded
literal bits, pure local substitution, and leaves from the widening family.
`lowerF64Condition_eval` adds all six comparisons and recursive pure Boolean
guards; `lowerF64Flow_eval` adds every finite tree of value conditionals.
Production pins preserve operation identity and order for explicit source
trees, including separate multiply/add and `fadd32`/`fcvt64` beneath binary64
arithmetic. This is carrier/shape correspondence, not proof that verifier bit
expansions implement Lean Float, IEEE behavior, hardware, or NaN payloads; it
also does not prove arbitrary mixed-width/effectful statement sequencing, the
Go evaluator, memory, calls, SIMD, or either ISA instruction.
The division case relates the extraction and verifier to the same
`Float32.div` operation and operand order; it is not a separate proof of IEEE
rounding or NaN-payload behavior. The FMA case similarly relates both sides to
the existing `Oak.FloatOps.fma32` carrier; it does not independently prove that
carrier or hardware rounding.

### 3.3 The native verifier remains materially inside the TCB

The theorem prover's SAT rung reduces an UNSAT claim to an LRAT certificate
that independent implementations check. The assembler semantic verifier has
a different acceptance path.

`asm.Verify` derives `VerdictProven` using its own term construction,
normalization, BDD and bit-level decisions, path reasoning, memory summaries,
loop coupling, and compositional rules. Those mechanisms are tested and many
underlying laws are formalized, but a proven native body does not generally
come with a compact proof object replayed by a small independent checker.

One checker-refinement debt identified in the 2026-09-16 audit is now closed:
`Oak.CheckerMeetRefinement.meetFact_sound` proves the new `meetIdx`
constant/register reconciliation sound on both incoming states, and
`asm/check_meet_test.go` pins the production decision table to the executable
Lean model. This removes one trusted decision procedure; it does not change
the broader assessment of `asm.Verify` below.

The current shape is:

```text
untrusted optimizer or lowering candidate
        ↓
asm.Verify
        ↓
VerdictProven
```

Translation validation keeps the optimizer outside the TCB, but the verifier
implementation remains inside it. The next assurance step is:

```text
complex verifier and search
        ↓
proof certificate
        ↓
small independently verified checker
        ↓
accept
```

Possible certificate families need not force every proof through one format.
Straight-line term equality, BDD equivalence, path coverage, loop simulation,
memory framing, and call-summary composition may use different proof objects
under one checked verdict format. The critical requirement is that
`VerdictProven` cease to depend solely on trusting the implementation that
found the proof.

Oak's LRAT, RUP, Tseitin, and self-hosted checker work provides much of the
architectural precedent for this step.

The first bounded native-equality audit has now landed. A closed scalar
AArch64/RV64 body with no calls, loops, external memory/effects, traps,
restricted domains, floats, or aggregates can be rerun through the machine
executor and Oak lowering to produce an exact result-disequality CNF. The
formula is regenerated when `prove.CheckNativeEqualityCertificate` checks its
LRAT proof, and an integration test requires the independent checker written
in Oak to accept that same formula and certificate. Tests also replay a valid
certificate against changed Oak and machine bodies and require refusal.

This is deliberately audit-only: it neither authorizes nor upgrades
`VerdictProven`. It removes the SAT solver from the bounded audit's TCB, but
not the symbolic executor, Oak lowering, clause generator, or checker
implementations. `Oak.NativeEqualityCertificate.accepted_implies_equal`
states the abstract composition and makes its missing implementation
refinements explicit. `Oak.TseitinCNF` now proves each raw Boolean gate's exact
signed-literal clause shape, supplied-list/final-clause composition, and the
exact 1-based initial RUP database model. The hardened Go checker kernel lives
in the dependency-leaf `internal/lrat` package. For every supplied sequence
satisfying `WellFormedFrom`, left-to-right evaluation constructs an assignment
satisfying all gate clauses, with the final-clause model correctly conditional.
`Oak.CNFBuilderTrace` derives that premise for an accepted supplied contiguous
allocation-event projection. `Oak.CNFDenseAllocation` additionally checks a
production-shaped nonnegative builder snapshot and proves dense/injective
shared ownership, ordered backward gates, exact memo witnesses, and the same
well-formed sequence. Representative Go accept/refuse decisions are
kernel-pinned; arbitrary Go memory/map projection, signed conversion, builder
history, clauses, DIMACS, and verdict authority remain open.
The next checked layer, `Oak.CNFClauseTrace`, now identifies the actual signed
builder/emitted lists with the decoded gates and supplied final obligation,
preserving literal order and rejecting zero. Its exact database theorem is
backed by 72 fixed production decisions, 71 of them kernel-replayed snapshots,
including shared producer/export corruptions. This is bounded correspondence;
the small fixtures do not test the 50-million-clause limit.
`Oak.CNFClauseCertificate` uses that database theorem to discharge the
direct-word contract's abstract CNF-completeness assumption. Accepted RUP gives
word equality only with an explicit result-to-root equality premise; arbitrary
Go/projection refinement, source/root provenance, DIMACS bytes, LRAT
implementation refinement, and compiler verdict authority remain open.
The bounded Boolean replay model now goes further: `Oak.CNFMemoWitness`
proves every accepted memo hit names its decoded gate, and
`Oak.CNFReplayApply`/`Oak.CNFReplayMemo` prove the exact binary folds and memo
semantics. `Oak.CNFReplayTerm` establishes input-slot stability and recursive
original-input semantics. `Oak.CNFReplayCertificate.replayed_words_equal`
therefore obtains equality of words packed from supplied paired bit
expressions using accepted RUP, without a separate root-equality or
CNF-completeness assumption. Apply decisions, the original one-bit corpus, and
twelve whole-word fixtures are kernel-pinned. The word checks cover
1/8/16/32/64-bit roots, parameter/operand truncation and zero extension,
truncation followed by extension, shared subterms, interleaved allocations,
and both equal and unequal words. Concrete values pin source-name/bit mapping
and result packing; malformed projections and cyclic or excessive syntax
expansion refuse. This advances bounded Go word/root correspondence, not
universal refinement of source-name/bit/word projection, width adaptation,
term-pointer memoization, reachable coverage, or the full native admission
policy. Native certificates remain audit-only; verdict authority is open.
The next word-model layer is now explicit: `Oak.CNFWordInput` derives named
input bits through the `parameter-count + 8` stride and inverse checked
allocation; `Oak.CNFWordProjection` checks 1..64-bit parameter/constant/AND/OR/XOR
syntax and proves its bit projection, including declared-width masking and
zero-extension/truncation. `Oak.CNFWordCertificate.projected_words_equal`
derives equal model-word widths and values from accepted projection, replay,
exact singleton clauses, and RUP without assuming input-binding or word/root
semantics. It rejects empty or unequal result pairing. This remains the
bounded production-correspondence layer: `TestNativeCNFReplayWordMatchesLean`
pins raw Go word syntax, replayed roots, and typed-normalized sampled values
across 1/8/16/32/64-bit fixtures. The theorem remains the
nonconstant certificate path over supplied model syntax, not universal Go
graph/table projection, pointer-memo or intermediate-root/reachability
refinement, complete admission/settled policy, or source-to-machine closure.
`Oak.CNFFinalObligation` proves the four total
decoded-root outcomes, exact trap/claim clause order, and pending
counterexample semantics. `Oak.CNFTermRoot` proves evaluation preservation and
pending database semantics for a supplied normalized one-bit Boolean term/root
encoding. The production exporter now memo-replays the
supplied trap terms in slice order and the claim, and independently checks
every outcome and the exact gate-record/unique-table-memo bijection before
performing the streaming audit of its actual shared allocation, raw-gate
clause sequence, and final edge conversion. The opaque bitwise-word audit now
independently replays actual Go term roots, input allocation, folds, exact gate
memo entries, complete reachable coverage, and the final OR-of-XOR
disequality root for parameters/constants/width adaptation and pointwise
AND/OR/XOR. `Oak.CNFBitwiseWordRoot` proves that root means word inequality.
`prove.CheckNativeBitwiseEqualityCertificate` regenerates that narrow audit
from the exact function and declaration and checks LRAT only against the
resulting DIMACS. Fresh certificates from Oak's solver are accepted by both
the Go and Oak LRAT checkers on AArch64 and RV64; replay after source or
machine changes, truncated or malformed proofs, and settled obligations are
refused. The API remains disconnected from compiler verdicts and caches.
This closes operation/fold selection only for that narrow grammar; general Go
satisfaction of the term/root relation, all other bit-blaster operations,
trap/claim provenance and source ordering, DIMACS, and formal Go-to-Lean
implementation refinement remain open. The next step remains expanding
bit-blaster and checker implementation refinement,
followed by requiring the leaf checker below compiler selection so certificate
acceptance can safely become verdict authority.

One narrow slice now follows this shape. Recursive OptIR scalar-call memory
summaries first pass through one checked CFG-order authority projection whose
accepted output feeds both summary construction and the deterministic
postorder trace. `Oak.OptIRMemoryAuthorityProjection` proves exact active
direct/call membership, exact non-root coverage, identity/shape inversion, and
composition with the exact summary fold. A small hash-free Go consumer then
checks exact child access claims, typed effect joins, closure, and root order;
`Oak.OptIRCallSummaryCertificate` proves those properties for the structural
trace model. Selected production decisions at both seams are pinned to Lean
examples. This does not yet remove the surrounding TCB: the models abstract
concrete CFG extraction and SSA verification, source and operation/type
validation, authority construction, SHA identity, callee-summary truth, and
source lowering. Static machine-callee occurrence identity is now closed for
the current scalar OptIR subset by a separate post-materialization gate:
nonzero SSA call-site IDs survive through final scheduling, and
`Oak.OptIRMachineCallIdentity` proves that acceptance contains exactly the
authorized `{site ID, callee}` occurrences, modulo physical order. The bounded
Go-to-Lean pins cover both native targets and all rejection shapes. Call
placement/control flow, dynamic counts, argument ABI, callee implementation
equivalence, and universal Go-to-Lean correspondence remain open.

The non-OptIR call-summary path now also closes its static
machine-symbol-to-Oak-body identity seam. One shared fail-closed resolver feeds
the verifier, loop analysis, outgoing-area calculation, and cache dependency
collection. It admits only a canonical scalar spelling or the active lane's
canonical suffix for a declaration with a fixed-vector signature, and rejects
map aliases, source/suffix collisions, the other lane's suffix, ABI-shape
mismatches, and ambiguity. `Oak.AssemblerCalleeIdentity.resolve_sound` proves
the small resolution model returns a declaration whose canonical native symbol
is exactly the queried symbol. Cross-target Go tables cover the decision
families, with representative live decisions serving as bounded Lean
correspondence pins. This does not prove dynamic call placement, ABI transport,
callee-summary truth, or the machine implementation of the callee.

### 3.4 Object, executable, relocation, and linking are not formally closed

`asm/object.go` and `asm/executable.go` compute ELF and Mach-O layouts, symbol
tables, relocations, section offsets, and program headers with run-time range
and consistency checks. The outputs are inspected by LLVM tools and executed
under QEMU or on host hardware where available.

The current verification-chain documents nevertheless classify the writers
as trusted. Three bounded seams are now closed. `Oak.ObjectLayout` proves that the
object writer's relocation-footprint admission keeps the complete four-byte
word, or both words of an eight-byte `adrl21`/RV64 PC-relative pair, inside
the defining function. The production decision table is pinned exhaustively
to the Lean model. `Oak.ObjectRelocation` proves the opcode, range, patch,
decode, and target-reachability laws for the AArch64 executable resolver's
direct `B`/`BL` word; production boundary pins and a final-ELF word check hold
that helper to the model on the exercised correspondence table, not by a
universal Go-refinement theorem. These are not section-layout,
symbol-resolution, or whole-link theorems. Object-to-binary linking is
otherwise explicitly trusted and generally runs through the C compiler's
driver.

`Oak.AArch64AddressRelocation` adds the two-word `ADRP+ADD` arithmetic seam:
exact instruction-pair/register admission, signed page and low-12 patching,
field preservation, and exact target reconstruction. Production uses
uint64-safe arithmetic, checks the complete pair's address range, round-trips
before pair-local mutation, and kernel-pins boundary decisions. Symbol and
section authority, relocation records, file formats, loading/register
execution, global transactionality, and the whole image remain trusted.

Consequently, even for a proven native body, the strict present claim is:

> The body is proved equal to its Oak specification down to modeled machine
> instructions, with target-dependent assurance for encoding; the AArch64
> direct-branch word and `ADRP+ADD` pair are proved at their arithmetic/bit
> seams, while the remaining object and executable construction and final
> linking stay trusted.

It is not yet:

> Every byte of the final ELF or Mach-O executable is a theorem consequence of
> the Oak source.

Closing this layer requires at least:

- a formal object-format subset for the exact ELF and Mach-O forms Oak emits;
- proofs of section and segment layout, alignment, non-overlap, bounds, and
  file/memory-size relationships;
- symbol-table and relocation application semantics;
- proofs connecting encoded function/data bytes to their placed addresses;
- entry-point and startup-stub correctness; and
- either a verified static linker for the closed subset or an explicit final
  trusted-linker boundary.

### 3.5 Encoding assurance is asymmetric

RV64 has 30 checked theorems connecting the decided instruction encodings to
Sail's `encdec` relation. Conditions represented by the ISA model, such as
even branch offsets, appear as hypotheses rather than being erased.

AArch64's encoding path is strong engineering evidence but not the same kind
of proof:

- tables are generated from Arm's machine-readable ISA material;
- operand and decode coverage are audited; and
- emitted encodings are checked against `llvm-mc`.

The ordinary epilogue `RET X30` is now one exact closed class within that larger
surface: its generated encoding-table row and default operand are pinned, its
fixed bits and Rn round-trip are proved, and generated Sail Lean establishes
the exact ordinary RET/`BranchType_RET` decode for `0xd65f03c0`. This is static instruction
identity, not a proof of LR provenance, target validity, or dynamic return.

Ordinary local `B <label>` is a second exact class. The Lean packer proves the
fixed bits, `imm26` extraction, signed endpoints, and equality with the proved
Branch26 relocation operation. Generated Sail Lean identifies ordinary DIR
decode and its sign-extended scaled offset; production tests pin local bytes,
overflow-safe displacement calculation, individual alignment, and refusal
without mutation at address extremes. This remains static encoding/relocation
arithmetic, not architectural PC/BranchTo or target-validity correctness.

Ordinary local `BL <label>` is the parallel call class. The exact fixed bits,
`imm26`, signed endpoints, Branch26 call-patch composition, and target
arithmetic are proved; generated Sail Lean selects `BranchType_DIRCALL` and
the exact scaled offset. Production gates pin the row, bytes, overflow and
individual-alignment refusals, and official decode route. Architectural PC,
X30, `PostDecode`, `BranchTo`, target/source-label authority, and object/link
correctness remain outside the theorem.

There is not yet a complete theorem for the emitted AArch64 subset of the
form `decode (encode instruction) = instruction` against the machine-readable
model. Until that lands, RV64 is closer to a formally closed
instruction-to-machine-word link than AArch64, even though the AArch64
semantic bridge is exceptionally strong.

### 3.6 The C route remains trusted

The system C compiler is a trusted boundary except for the growing set of
trusted-core helpers whose compiled machine code is independently translation
validated through Oak's assembler verifier.

The remaining C emitter is supported by differential testing and selected
refinements, not an end-to-end proof that arbitrary emitted C and the resulting
machine code implement the Oak program.

This affects:

- native-lane fallbacks outside `-verified`;
- every amd64 target, which currently has no Oak native lane;
- Cortex-M targets; and
- RV32 targets.

The fail-closed verified profile is important precisely because it refuses to
pretend this boundary is equivalent to the native proof lane.

## 4. Standard-library status

The standard library is well beyond a collection of informal Lean examples.
Packages including bytes, bitsets, endian values, buffers, array lists,
encodings, sorting, random generation, UUIDs, hashes, Unicode/text operations,
and protocol-oriented structures have substantial combinations of:

```text
normative specification
implementation
executable tests and differential checks
formal model or extraction
proved functional laws
```

Examples include universal round-trip, strictness, permutation, sortedness,
streaming, state-transition, and boundedness properties over extracted or
modeled functions.

The remaining distinction is implementation refinement. A theorem about the
extracted or modeled library implementation is not automatically a proof that
every production frontend/backend path realizes it. The `R` column in
`STATUS.md` correctly remains open for packages whose implementation-to-model
correspondence is not proved.

This is the appropriate next phase for mature library proofs: retain the
functional theorems, then connect the concrete compiler and backend artifacts
to the already-proved model instead of repeatedly proving parallel models.

## 5. Assessment by layer

| Verification layer | Assessment |
| --- | ---: |
| User theorem/proof system | **9/10** |
| Formal language laws and models | **9/10** |
| Type and borrow checker implementation refinement | **7/10** |
| Resource-system implementation refinement | **6/10** |
| Source → verifier lowering refinement | **7.5/10** |
| Native semantic verifier coverage | **9/10** |
| Native verifier TCB closure | **7.5/10** |
| AArch64 ISA semantic grounding | **9/10** |
| RV64 ISA semantic grounding | **9/10** |
| RV64 encoding proof | **8.5/10** |
| AArch64 encoding proof | **7/10** |
| Object and executable writer proof | **3/10** |
| Linker proof | **1–2/10** |
| C-backend end-to-end proof | **4/10** |
| `-verified` fail-closed policy | **9.5/10** |

The distinction between verifier **coverage** and verifier **TCB closure** is
essential. `asm.Verify` proves an impressive range of real native bodies, but
the proof engine has not yet been reduced to a small independently checked
certificate consumer.

These scores should not be aggregated into a single arithmetic percentage.
The weakest link determines the strongest end-to-end claim for a particular
artifact, and different targets take different paths.

## 6. Milestones for an end-to-end verified native compiler

The following milestones would materially change what Oak can claim.

### 1. Extend the shared lowering refinement

Extend the float slice through decimal-to-bit parsing, remaining conversions,
memory/effectful or statement control flow and calls, SIMD carriers,
`u128`, and every remaining native language shape to the source/verifier shared
semantics. Each addition needs:

- a source/extraction interpretation;
- the verifier-lowering interpretation;
- an agreement theorem;
- pinning against the production Go lowering; and
- composition with the existing ISA semantics.

### 2. Certificate-check or refine the assembler verifier

Define a proof-object boundary for every route that produces
`VerdictProven`. A small checker should validate term equivalence, path
coverage, loop relations, memory framing, and call-summary use independently
of the algorithms that discovered them.

The checker itself should be implemented twice or refined to Lean, following
the LRAT checker's pattern.

The OptIR authority projection and call-summary postorder checker are the first
composed model/proof slice. Their structural seam is closed and bounded Go
decisions are pinned, but the concrete CFG/validator implementation and
universal implementation-refinement seams remain before this can count as a
fully independently verified certificate checker.

### 3. Finish frontend and resource implementation refinements

Connect the production parser/checker traversals to one formal frontend model,
with priority on facts that affect native proof assumptions:

- type identity and generic substitution;
- ownership, aliasing, suspension, and result provenance;
- effect and callable-contract flow through every value position;
- representation and layout selection;
- pattern reachability and GADT facts; and
- syntax rewrites before checking.

### 4. Prove AArch64 encoding round trips

For every emitted instruction and operand form, prove the encoder agrees with
Arm's decode relation. Generated tables and external assembler differentials
should remain as drift and implementation checks after the theorem lands.

### 5. Prove object and executable construction

Specify and prove the exact ELF and Mach-O subsets Oak writes, including
relocations and startup layout. Connect instruction encoding theorems to the
bytes placed at linked virtual addresses. The AArch64 direct `B`/`BL`
direct-branch and AArch64 `ADRP+ADD` relocation arithmetic are the first proved
word-level slices; function/symbol layout, the remaining relocation families,
and file structure are next.

### 6. Close or explicitly terminate at linking

Either implement a small verified static linker for the closed native profile
or state the external linker as the final irreducible trusted boundary. The
claim made by `-verified` should identify which choice applies to its produced
artifact.

## 7. Claim discipline

Until those milestones land, the strongest accurate broad claim is:

> Oak has a fail-closed, proof-aware native compilation profile for AArch64
> and RV64 whose supported bodies are translation-validated against Oak
> semantics and connected to machine-readable ISA semantics, with explicitly
> labeled trusted boundaries in the frontend, verifier implementation,
> encoding by target, object/executable construction, and linking.

After milestones 1–5, it would be reasonable to say:

> Oak has an end-to-end verified native compiler for its closed AArch64 and
> RV64 profiles, from admitted Oak source to the bytes and relocations of the
> produced executable, with linking either proved or named as the final
> trusted boundary.

The difference between those claims is not the presence of more verification
features. It is the closure of the remaining TCB and artifact seams.
