# Experimental Core Wasm scalar profile

Status: implemented experimental subset with execution tests; not formally
verified. Design: [Wasm/WASI/browser roadmap](../notes/wasm-wasi-browser-2026-09.md).
Coverage: [target matrix](../targets.md).

## 1. Target and artifact

`core/wasm32` emits one import-free Core Wasm module directly from checked raw
OptIR. The target uses 32-bit pointer/data-model metadata, but v0 does not admit
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

## 2. Admitted subset

- Concrete function declarations with direct calls and one Oak result.
- `u32`, `i32`, `u64`, `i64`, `Bool`, and Unit results/locals. Unit parameters
  are not admitted. Exported Bool inputs outside 0/1 trap.
- Constants, copies, negation, wrapping addition/subtraction/multiplication,
  unsigned bitwise AND/OR/XOR, Bool not, equality and signed/unsigned comparisons.
- CFG branches, conditionals, loops and simultaneous edge argument assignment.

Global declarations, external bodies, dispatch, memory, aggregates, unresolved
generics, narrow integers, conversions, division/remainder, shifts, float, SIMD
and unknown operations/effects refuse the whole emission. No partial successful
module may hide a refused function. Calls must resolve within the emitted module
and match exact Oak parameter/result types, not just erased Wasm carrier types.

Integer exports use Wasm's signed JS carriers; hosts interpret the returned bits
using the retained Oak type. The playground displays unsigned results accordingly.
Execution resources are finite; no total-termination guarantee is made.

## 3. Implementation and verification status

The emitter checks CFG/SSA structure and the existing closed scalar operation
typing rules, applies profile limits, and emits deterministic type/function/
export/code sections. A dispatch loop represents arbitrary accepted CFGs. Edge
values are pushed before any phi local is overwritten. This implementation is
not yet a size- or throughput-optimized backend.

Independent runtime tests decode, validate and execute final bytes, including
loop-carried swaps, zero-trip loops, overflow, signedness, Bool guards and calls.
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
the emitter. Its version is `oak.wasm.check.v0`. It snapshots input, consumes the
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
