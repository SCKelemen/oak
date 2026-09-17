# Experimental Core Wasm scalar profile

Status: implemented experimental subset with execution tests; not formally
verified. Design: [Wasm/WASI/browser roadmap](../notes/wasm-wasi-browser-2026-09.md).
Coverage: [target matrix](../targets.md).

## 1. Target and artifact

`core/wasm32` emits one import-free Core Wasm module directly from checked raw
OptIR. The target uses 32-bit pointer/data-model metadata, but v1 does not admit
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
provenance. A checked target description and owned raw-CFG snapshots feed a
materialization node; a separately revisioned admission node validates its
actual bytes/manifest before anything is returned. `wasm.EncodeCandidate` is
the explicitly untrusted encoding API; ordinary callers use `wasm.Emit` for
combined encoding and admission. Neither a recipe key nor this graph grants
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
without a program-counter local or dispatch loop. All other accepted CFGs retain
the dispatch-loop baseline. Edge values are pushed before any phi local is
overwritten. This is a first bounded code-size optimization, not a mature
throughput-optimized backend.

### Direct returning-block emission

The direct path depends only on checked raw CFG shape: exactly one block, ending
in return. A one-block backedge still uses the dispatcher. It does not use SCCP
reachability to skip blocks, consume an optimized candidate, eliminate dead
operations, reorder calls, reuse locals or stackify expressions. Every operation
still passes the same effect/type/attribute gates and emits in source order.
Bool argument checks remain before the body, including for unused arguments;
Unit results do not suppress calls or traps. Returning a parameter does not skip
preceding operations. The function's final `end` returns its declared result.

The encoding recipe is now `oak.wasm.encode.v3`; scalar/check profiles remain
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
| u32 add | 68 → 48 | 18 → 6 |
| shared u64 multiply result | 77 → 57 | 22 → 10 |
| unused Bool argument with guard | 73 → 53 | 22 → 10 |
| Unit return | 60 → 40 | 15 → 3 |
| signed i64 division | 82 → 62 | 27 → 15 |
| caller plus add callee | 126 → 86 | 40 → 16 |
| conditional / loop fixtures | 133 / 166, unchanged | 55 / 65, unchanged |

These are deterministic code-size gates, not a measured wall-clock speedup or
formal equivalence proof. Multi-block structurization, stack expression emission,
local allocation and runtime benchmarks remain open.

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
