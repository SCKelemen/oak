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
and `TranslationVerified=false`. Native/assembly/CPU options are incompatible;
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
Malformed bytes are checked independently by the runtime. These are tests,
not universal proofs or an independently verified Oak decoder.

No Oak Wasm semantics/refinement theorem, authoritative Wasm certificate checker
or verified browser runtime is claimed. `Oak.Target` currently models the
existing C/native targets only; its theorems do not cover `core/wasm32` yet.
