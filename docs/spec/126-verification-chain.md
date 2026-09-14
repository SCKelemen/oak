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

### 2.6 Object → binary

Linking is the C compiler's driver (`compileC`), static for Linux cross
builds, with the manifests' `link`/`framework` inputs and the realization
shims. **Trusted**; **differential** through `oak run -target` under
QEMU where present.

## 3. Per target

| Target | Source → C | C → object | Asm/native lane | ISA semantics the lane is held to | Encoding | Execution check |
| --- | --- | --- | --- | --- | --- | --- |
| linux/arm64, darwin/arm64, freestanding/arm64 | refined core + differential | trusted (cc); the trusted-core helpers translation-validated through the verifier | arm64: verifier proof/evidence/trusted | **proved to Arm's ASL**: `Oak.ArmASL` transliterates the Sail Armv8.5-A primitives with the Sail text beside each, proved equal to `Oak.AssemblerSemantics`; the hand transliteration is proved against Sail's mechanically generated Lean (`spec/sail/lean/Out.lean`); the decode tree **audited** (`asm/sail_coverage_test.go`), operand forms audited against the A64 ISA XML | table **generated from the ISA XML**, checked against `llvm-mc` | silicon **differential** (181 bodies × 60 inputs on the host core) |
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
iteration's values. Outside the subset — floats and the vector operations
— the verifier's lowering is still the Go's alone, related to the
extraction by tests.

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
   what remains is at the edges: floats and vectors — so `lowerT_eval`
   covers the
   bodies `oak build -native` actually verifies rather than their
   arithmetic alone. This is the step that turns "source theorem implies
   machine behavior" from a statement about expressions into one about
   functions on arm64.
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
   refinement pins at the C level have nothing to bridge yet.
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
