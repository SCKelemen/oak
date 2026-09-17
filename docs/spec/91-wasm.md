# Experimental Core Wasm scalar profile

Status: implemented experimental subset with execution tests; not formally
verified. Design: [Wasm/WASI/browser roadmap](../notes/wasm-wasi-browser-2026-09.md).
Coverage: [target matrix](../targets.md).

## 1. Target and artifact

`core/wasm32` emits one import-free Core Wasm module directly from checked
structured OptIR bound to its canonical CFG projection. The target uses 32-bit
pointer/data-model metadata, but v1 does not admit
pointer or memory operations. It has no C fallback, host imports, memory, start
function, WASI ABI or Component Model output. All admitted functions are exported
by their checked names; exports are not a stable public component ABI.

`oak build -target core/wasm32 -o program.wasm program.oak` writes binary bytes.
Without `-o`, the single-package output is `out.wasm`. `Compilation.EmitWasm()`
selects this profile and returns bytes, typed export metadata, a profile identity
and `TranslationVerified=false`. `ByteValidation` records successful independent
decoding/type validation of the final bytes and their SHA-256; it is diagnostic,
not a certificate. Native/assembly/CPU options are incompatible;
the CLI also rejects native/C/link/optimization/extraction switches for this
target. `-verified` is unavailable and must fail, never fall back.

`EmitWasmWithReport()` additionally returns diagnostic target and artifact-DAG
provenance. A checked target description and owned structured-function and CFG
snapshots feed a materialization node; exact reprojection must match before the
structure can guide lowering. A separately revisioned admission node validates
actual bytes/manifest before anything is returned. `wasm.EncodeCandidate` and
`wasm.EncodeStructuredCandidate` are explicitly untrusted encoding APIs;
ordinary callers use the corresponding combined emit API. Neither a recipe key nor this graph grants
translation-verification authority. See the
[target pipeline boundary](../notes/target-pipeline-2026-09.md).

## 2. Admitted subset

- Concrete function declarations with direct calls and one Oak result.
- `u32`, `i32`, `u64`, `i64`, `Bool`, and Unit results/locals. Unit parameters
  are not admitted. Exported Bool inputs outside 0/1 trap.
- Constants, copies, negation, wrapping addition/subtraction/multiplication,
  unsigned bitwise AND/OR/XOR, Bool not, equality and signed/unsigned comparisons.
- Signed/unsigned division and remainder at 32 and 64 bits, with the trap and
  overflow behavior specified below.
- CFG branches, conditionals, loops and simultaneous edge argument assignment.

Global declarations, external bodies, dispatch, memory, aggregates, unresolved
generics, narrow integers, conversions, shifts, float, SIMD
and unknown operations/effects refuse the whole emission. No partial successful
module may hide a refused function. Calls must resolve within the emitted module
and match exact Oak parameter/result types, not just erased Wasm carrier types.

Integer exports use Wasm's signed JS carriers; hosts interpret the returned bits
using the retained Oak type. The playground displays unsigned results accordingly.
Execution resources are finite; no total-termination guarantee is made.

### Division and remainder (scalar v1)

Both operators trap on a zero divisor. Quotients truncate toward zero; signed
remainders have the dividend's sign. Oak defines `MIN / -1` as `MIN` and
`MIN % -1` as zero ([integer semantics](20-types.md#111-explicit-integer-conversions)).
The emitter uses Wasm's unsigned divide/remainder and signed remainder directly.
For signed division, it emits a typed `if`: when the divisor is `-1`, wrapping
`0 - dividend`; otherwise `div_s`. This avoids Wasm's signed-overflow trap
without suppressing the zero-divisor trap. See the
[Core numeric rules](https://webassembly.github.io/spec/core/exec/numerics.html#op-idiv).

Operands are already evaluated SSA locals: the guard neither duplicates nor
skips source calls. Division/remainder operations must carry exactly the
`Control.Trap` effect; absent, duplicate or unrelated effects and attributes
refuse emission. Unused results still execute; guarded/untaken branches and
zero-trip loops retain their source trap domain. No proof fact or SCCP result
is used to erase a trap or select an optimized CFG in this increment.

The expanded operation vocabulary is `oak.wasm.scalar.v1`, paired with
`oak.wasm.check.v1` and a revisioned encoding recipe. Older profile manifests
are refused, even when their bytes happen to fit the new subset. Reports are
still diagnostic, not formal translation certificates. This is an Oak profile
revision, not a change to the Core Wasm binary-version header.

## 3. Implementation and verification status

The emitter checks CFG/SSA structure and the existing closed scalar operation
typing rules, applies profile limits, and emits deterministic type/function/
export/code sections. A single-block CFG ending in return emits directly,
without a program-counter local or dispatch loop. The four-block loop and
conditional shapes below also emit directly. Other acyclic CFGs of at most 127
blocks use forward labels. A single pre-test loop may compose the same lowering
for an acyclic body of at most 124 blocks. When those raw-CFG paths do not match,
compiler-owned structured OptIR recursively lowers nested reducible loops and
conditionals. Raw CFGs without matching structure and irreducible cycles retain
dispatch.
Edge values are pushed before any phi local is
overwritten. These are bounded lowering improvements, not a mature
throughput-optimized backend. Shape recognition stays inside versioned
materialization; blocks do not become separate artifact-DAG nodes. Lookup,
operation admission, edge copies and return emission are shared across paths.
Except for the recursive structured-tree fallback, a local plan also emits
eligible pure single-use SSA trees directly on Wasm's operand stack and removes
their result locals.

### Direct returning-block emission

The direct path depends only on checked raw CFG shape: exactly one block, ending
in return. A one-block backedge still uses the dispatcher. It does not use SCCP
reachability, consume an optimized candidate, or remove effects and traps. Pure,
total definitions with exactly one static use in their defining block may move
to that use and emit as a stack expression. Shared values, cross-block values,
calls, memory-tagged operations, effectful operations, division/remainder and
values consumed by division/remainder remain locals. Bool argument checks remain
before the body, including for unused arguments; Unit results do not suppress
calls or traps. Returning a parameter does not skip preceding operations. The
function's final `end` returns its declared result.

The production encoding recipe is now `oak.wasm.encode.v9`; scalar/check profiles remain
v1 because neither the accepted vocabulary nor the byte-validation rules
changed. Independent final-byte admission is unchanged, and translation
verification remains false.

`TestWasmDirectEmissionSize` retains executable baseline bytes from specification
`ea3c3793` and gates the measured result. `TestWasmDirectEmissionExecution`
independently instantiates both versions and checks arithmetic, calls, Bool
guards, signed division overflow/traps, branches and loops against reference
results. Sizes below are whole modules; instruction counts include structural
Wasm instructions, not native JIT instructions or dynamic execution counts.

| Fixture | Module bytes, before → after | Wasm instructions, before → after |
| --- | ---: | ---: |
| i64 identity | 58 → 38 | 14 → 2 |
| u32 add | 68 → 42 | 18 → 4 |
| shared u64 multiply result | 77 → 51 | 22 → 8 |
| unused Bool argument with guard | 73 → 47 | 22 → 8 |
| Unit return | 60 → 34 | 15 → 1 |
| signed i64 division | 82 → 62 | 27 → 15 |
| caller plus add callee | 126 → 68 | 40 → 10 |

These are deterministic code-size gates, not a measured wall-clock speedup or
formal equivalence proof. The loop increment below adds a first, narrow runtime
comparison. General structurization, broader local allocation and representative
runtime benchmarks remain open.

### Four-block structured loops

The emitter recognizes exactly four distinct blocks: entry branches to header;
header conditionally branches to body or exit; body branches back to header;
exit returns. Either condition polarity and any block ordering/IDs work. It emits
`loop`/`if`/`else`, a direct backedge and a returning exit arm. No PC local,
dispatch comparison or dispatch update remains. The recognizer covers the whole
CFG and never uses constant reachability to discard blocks or operations.

Entry operations run once; header operations run on every test (including the
initial and final test); body operations run only on the selected body edge;
exit operations run on exit. All edge values are pushed before any destination
local is set, preserving cyclic phi assignments. Bool argument guards and all
operation/effect admission gates are shared with the other emission paths.
The compact recognizer still covers exactly this shape. Conditional bodies may
instead use the composed region-loop lowering below. Nested loops use recursive
structured-region lowering when the checked frontend retained their exact
structure; raw CFGs and irreducible bodies keep the dispatcher. A one-block
self-loop is not this shape.

Engine tests compare retained dispatcher bytes with current output and reference
results for sum, swap and GCD, including zero trips, u32 wraparound and full-width
u64 remainders. Additional tests exercise inverted polarity, shuffled block order,
header-parameter swap cycles, malformed effects in every region, header/body/exit
call traps, Unit returns and the raw-CFG nested-loop fallback.

| Loop fixture | Module bytes, before → after | Wasm instructions, before → after |
| --- | ---: | ---: |
| counter | 166 → 79 | 65 → 23 |
| sum | 203 → 104 | 79 → 33 |
| swap | 246 → 129 | 95 → 43 |
| GCD | 183 → 108 | 71 → 33 |

An opt-in warmed sum benchmark compares the exact old/new binaries, alternates
timing order and checks results. Four local Deno/V8 processes measured median
structured/dispatcher time ratios of 0.151–0.436. The shared Darwin/arm64 host
was noisy; this is one microbenchmark, not a browser/application performance
guarantee. [Raw samples and reproduction](../../benchmarks/wasm/README.md) retain
the engine version, protocol and limits. Timing is not a CI pass/fail threshold.
This lowering remains untrusted and execution-tested, not formally refined.

### Pre-test loops with acyclic bodies

The general loop path composes the target-independent region scheduler with
Wasm's structured `block`/`loop`/`if`. It recognizes one entry → header pre-test
loop, a common returning exit, and a body region whose remaining edges are
forward except for explicit transfers to the header or exit. The body may have
nested/sequential branches, shared joins, multiple latches, breaks and early
returns. Entry, header, body and exit must exhaust the whole checked CFG. Nested
or irreducible cycles do not match and retain dispatch.

`optir.AcyclicRegionOrder` validates the entire CFG before treating boundaries
as traversal stops. It returns no partial schedule for a residual cycle and does
not mutate the CFG or consult constant reachability. Wasm emits each body block
once; transfers use existing parallel phi copies and branch to explicit loop/
exit labels. A 124-body-block cap reserves the independent validator's control
depth for the function, exit block, loop, condition and operation-level `if`.
The 125-block boundary is executed through the dispatcher in tests.

| Region-loop fixture | Module bytes, before → after | Wasm instructions, before → after |
| --- | ---: | ---: |
| conditional loop body | 342 → 153 | 144 → 61 |
| nested-conditional loop body | 436 → 192 | 191 → 82 |

Executable baseline/current tests cover zero trips, wrapping results, lazy
traps, Unit calls, header/entry/tail operations, signed `MIN/-1`, Bool guards,
multiple latches, breaks, early returns, polarity, shuffled block storage and
the raw-CFG nested-loop fallback. Unsupported effects are checked in every region,
including a constant-zero-trip body. Stack-expression planning is shared with
the other raw-CFG paths and does not change the recognized control shape.

Six local warmed Deno/V8 runs of the nested-body kernel all favored the new
lowering, with median new/old ratios from 0.021 to 0.121, but individual samples
were extremely noisy. [All samples and protocol](../../benchmarks/wasm/README.md#pre-test-loops-with-acyclic-bodies)
are retained. They establish neither a general speedup nor Chrome behavior.

### Recursive structured-region lowering

Production materialization now retains the checked structured OptIR function as
well as its canonical CFG. Before structure can guide emission, the encoder
validates and snapshots both, independently reprojects the structured function,
and compares every canonical CFG field directly. Structured and CFG fingerprints
independently enter the typed artifact-DAG recipe. A mismatched pair fails
before byte materialization; neither representation is independent authority.

The recursive emitter is selected only after the established direct, compact
loop/diamond, forward-CFG and region-loop paths decline the CFG. This keeps all
existing fixture bytes stable. It emits structured `if/else` recursively and
pre-test loops as an exit `block` containing a `loop`; false conditions branch
to the exit and completed bodies branch back. Loop initial values, body yields
and conditional yields use parallel local copies: every source is pushed before
any destination is overwritten. Lexical condition/body arguments alias the
current carried-result locals, so retaining structure does not add unused Wasm
locals to functions handled by older paths.

The structured tree is bounded before recursive copying or projection. Shared
or cyclic Go control-node pointers, excessive node counts and excessive control
depth refuse. The independent final-byte checker still enforces its own module,
instruction, local, stack and 128-frame limits. Operations, calls, traps, Unit
values and Bool guards pass through the same admission helpers as raw CFG paths.

| Nested-loop fixture | Module bytes, dispatcher → structured | Wasm instructions, dispatcher → structured |
| --- | ---: | ---: |
| nested counters | 337 → 203 | 140 → 66 |
| nested loop with conditional body | 437 → 255 | 189 → 88 |

Engine tests execute both modules against independent reference loops through
zero-trip, ordinary and larger inputs. Additional tests cover lazy in-module
calls, division traps, Unit results and invalid Bool inputs in nested loops.
Three local Deno/V8 processes measured median structured/dispatcher ratios of
0.087–0.100 for the conditional nested-loop microbenchmark. The full samples
and method are retained in the [Wasm benchmark record](../../benchmarks/wasm/README.md#nested-structured-regions).
This is not a Chrome/application guarantee, a timing gate, or formal
source-to-Wasm refinement.

### Four-block conditionals with a join

A second four-block shape is entry → true/false arms → common merge → return.
Entry must conditionally branch; each arm must unconditionally branch to the
same returning merge block. All four blocks must be distinct and exhaust the
CFG. Arbitrary block IDs/order work. Shared arms, cross edges, backedges,
returning arms, conditional arms and extra blocks do not match.

Entry operations and the condition execute once. Wasm `if/else` evaluates only
the selected arm, with its incoming edge copies, operations and outgoing join
copies. The merge executes once after the conditional and returns. No eager
evaluation of untaken calls/division is introduced, and no operation is removed
because a constant condition predicts it will not execute. Unsupported effects
in a constant-untaken arm still refuse the whole module. This is not SSA
optimization-candidate admission and carries no new proof authority.

Tests cover retained dispatcher binaries versus reference results, both branch
polarities, shuffled blocks, multiple arm/join parameters, mixed i32/i64 locals,
Bool guards (including unused arguments), Unit calls, short-circuit operators,
condition/arm/merge traps, constant selectors and nested conditionals (now using
the general acyclic path below).

| Conditional fixture | Module bytes, before → after | Wasm instructions, before → after |
| --- | ---: | ---: |
| simple choice | 133 → 65 | 55 → 16 |
| guarded division | 154 → 68 | 61 → 16 |
| i64 arithmetic after join | 157 → 71 | 65 → 20 |
| loop plus conditional helper | 327 → 161 | 127 → 56 |

The opt-in helper-call benchmark retains a structured caller loop in both
versions. The initial noisy Deno/V8 process measured a median new/old time ratio
of 0.073; three repeated processes measured 0.134–0.136. [All raw samples and the
method](../../benchmarks/wasm/README.md#four-block-conditionals) are retained.
This single-kernel result is not a general browser/application speed claim, a
CI timing threshold or a formal translation proof.

### Acyclic forward-CFG lowering

Beyond the compact special cases, the emitter now handles arbitrary acyclic
CFGs with forward Wasm labels, including nested/sequential branches, shared
cross-joins, early returns and duplicate destinations with different arguments.
The target-independent `optir.AcyclicOrder` validates the CFG, reuses iterative
reverse postorder, and accepts an order only if every edge goes forward. Cycles
return no schedule; malformed CFGs return an error. Numeric block IDs and slice
order have no semantic significance. No constant-reachability pruning occurs.

Wasm nests empty `block` scopes around the scheduled blocks, emits each source
block once, and branches out to its destination label. Only unconditional
adjacent edges fall through. Conditional edges keep lazy `if/else` transfers;
all incoming phi values are captured before any destination local is written.
Calls, dead-result traps, signed division overflow behavior, and all entry Bool
guards remain. A 127-block cap reserves the byte validator's 128 control frames
for forward labels, the function, and an internal `if`. Larger accepted CFGs and
unmatched loops keep dispatch. Existing direct/loop/diamond fixtures are unchanged.

This is generic bounded lowering, not a new optimization candidate or DAG node
per block. The raw compatibility API consumes checked CFGs; production
materialization also retains exact structured identity. Both still gate actual
bytes with independent admission. Neither consumes optimized OptIR nor grants
formal translation verification.

| Forward fixture | Module bytes, before → after | Wasm instructions, before → after |
| --- | ---: | ---: |
| nested conditionals | 253 → 129 | 114 → 54 |
| sequential i64 conditionals | 248 → 130 | 112 → 54 |
| loop plus nested conditional helper | 421 → 214 | 174 → 86 |

Tests execute retained pre-change bytes and current output against reference
results. Another 64 generated graphs exercise 2,304 input pairs with shared
joins, edge arguments, early returns, inverted polarity and shuffled blocks.
Depth-boundary tests execute both the 127-block forward path and 128-block
fallback, including unused trapping signed division at maximum nesting.
Nested Unit calls also exposed a shared projection bug: structured DFS collected
memory metadata in a different order from CFG scanning. The projector now sorts
metadata by exact operation site before the unchanged authority comparison; it
does not move operations or weaken identity/effect checks.

Three local warmed Deno/V8 runs of the nested-helper kernel measured median
new/old execution ratios of 0.387–0.438. The caller loop is structured in both
versions. [Raw samples and method](../../benchmarks/wasm/README.md#acyclic-forward-cfgs)
are retained; this is not a representative browser performance claim.

### Pure single-use stack expressions

Before emitting any raw-CFG route, the backend records every SSA definition and
runtime use. A one-result definition may be deferred to its sole use only when
both are in the same block and the operation is total, pure, and carries no
memory access/call identity. Calls, division/remainder, effectful operations,
shared values and cross-block values remain explicit locals. Operands consumed
by division/remainder also remain locals because signed-division overflow
lowering may read them more than once.

Deferred definitions recursively emit through the same operation/type/effect
checks as ordinary definitions. Cycle and duplicate-consumption guards fail
closed. Edge copies evaluate all expression sources before writing any target
phi local. Local compaction preserves parameter indices and remaps every
retained SSA or structured lexical alias through its old physical local. The
recursive structured-tree fallback is deliberately excluded until it has
lexical-region use accounting; its existing bytes stay stable. A deferred pure
tree used only as Oak's Unit return is accounted for without a Wasm carrier;
ineligible calls, traps and effects still execute in their original positions.

`TestWasmStackExpressionExecution` retains executable recipe-v8 bytes for a
loop and conditional helper, independently executes both lanes, and checks
ordinary, boundary and large inputs. Recipe v9 shrinks that complete module
from 258 to 161 bytes and from 88 to 56 Wasm instructions. Three longer local
Deno/V8 timing processes were too variable to establish a runtime improvement:
their ratios of medians were 0.884, 0.937 and 1.519, with extreme outliers in
both lanes. The [raw record](../../benchmarks/wasm/stack-expression-2026-09-18.json)
therefore claims only deterministic static reduction, not faster execution.
Final bytes still pass independent admission and translation verification
remains false.

### Execution and proof coverage

Independent runtime tests decode, validate and execute final bytes, including
loop-carried swaps, zero-trip loops, overflow, signedness, Bool guards and calls.
Division tests compare actual engine results with independent BigInt arithmetic
on boundary and deterministic input pairs, including `MIN/-1`, zero divisors,
mixed signs, calls, branch guards, dead results and remainder-carrying loops.
An independent Go byte decoder/validator now runs before emission returns and
cross-checks the export names and carrier signatures against the manifest.
Malformed bytes are also checked by the runtime. These are implementations and
tests, not universal proofs or an independently **verified** Oak decoder.

The first formal slice is the LEB prefix model described below, not Wasm
execution or source-to-output refinement. No authoritative Wasm certificate
checker or verified browser runtime is claimed. `Oak.Target` currently models the
existing C/native targets only; its theorems do not cover `core/wasm32` yet.

## 4. Independent byte-validation boundary

`wasm/check.Validate(bytes)` depends only on Go's standard library, not OptIR or
the emitter. Its version is `oak.wasm.check.v1`. It snapshots input, consumes the
entire file and returns the exact byte hash, decoded exports, function count and
instruction count. Callers must not mutate input concurrently with snapshotting.
No external runtime or guest code is invoked by validation.

The reviewed Core rules are pinned to [WebAssembly/spec revision
779957d81feca2ec6a372c40a9130e28ef390645](https://github.com/WebAssembly/spec/tree/779957d81feca2ec6a372c40a9130e28ef390645).
This is a rules/reference pin, not a formal correspondence theorem.

The bounded binary profile requires type, function, export and code sections,
once each in that order. Other sections (including custom sections) are refused.
Types/functions number 1..128; exports number 0..128 with unique, nonempty UTF-8
names of at most 256 bytes. Signatures have at most 64 i32/i64 parameters and
one result. Section/body lengths, indices and exact byte coverage are checked.
LEB32/64 decoding accepts legal padding but rejects overlong encodings and
incorrect unsigned/sign-extension bits.

`Oak.WasmLEB` models the pinned integer prefix grammar independently of the
Go accumulator, using mathematical signed integers. `decode_sound` and
`decode_complete` establish agreement between the executable model decoder and
that grammar. `Encoding.range`, `Encoding.nonempty`, `Encoding.byte_budget`,
and `decode_append` prove numeric range, nonempty/bounded consumption and
preservation of trailing bytes. Legal nonminimal encodings remain admitted.
`decodeWord` projects a successful value to its sign-extended 64-bit word and
consumed length, matching the production reader's observable success interface.

`TestWasmLEBMatchesLean` generates kernel-checked `by decide` examples from
actual Go reader outcomes: all one-byte inputs; every final byte at the
32-/64-bit length boundary with zero/all-one preceding payloads; signed extrema,
padding, truncation, overlong inputs and suffixes. Formal CI requires this oracle
with `OAK_REQUIRE_WASM_LEAN=1`. These are **finite production correspondence
checks**, not a universal proof of the Go OR/shift accumulator, cursor/slice
mutation, failure offsets or module/type validation. The inductive theorems are
universal for the Lean prefix model only.

Instruction validation uses iterative operand/control stacks. It admits integer
constants, the emitter's arithmetic/comparison vocabulary, locals get/set/tee,
direct calls, nop/drop/unreachable, block/loop/if/else/end, br/br_if and return.
Blocks have no parameters and zero or one i32/i64 result; type-indexed blocks
and all unlisted opcodes are outside the profile. Unreachable code retains
concrete-type, index and syntax checks. Loop labels take inputs, not results;
branch depths, arm result agreement, frame-local stack heights and function
returns are checked independently of the emitter's dispatch-loop strategy.
The v1 additions are `i32/i64.div_s`, `div_u`, `rem_s`, and `rem_u`; each pops
two same-width integers and pushes one of that width. Type validation does not
prove a nonzero divisor or the presence of Oak's signed-overflow guard. A
well-typed division that will trap is still a structurally valid module.

Operational limits: 1 MiB module, 16,449 locals and local declaration groups per
function (locals include parameters), 65,536 locals across the module, 262,144
instructions, 128 control frames including the function frame, and 16,384
operand stack entries. These bound validation work, not guest runtime resources.

`Module.ValidateBytes()` rechecks bytes and carrier-level metadata; a saved
report cannot authorize modified bytes. Carrier validation cannot distinguish
Bool/u32/i32 or signed/unsigned i64, establish Bool guards, or associate an
export with the correct Oak body. Those remain source/translation obligations.
The browser still independently engine-validates output. There is no formally
refined decoder, source-to-Wasm proof, certificate authority, or separately
deployed small browser checker yet. Thus milestone W1 is **partial**, not closed.
