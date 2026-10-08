# Decoded scalar Wasm execution and structured control

`Oak.WasmExecution` adds a typed operand stack, local values, and incremental
byte execution for the straight-line part of the scalar profile. It connects
the [proved assembler output](91-wasm-assembler-proofs.md) to execution in this
model. `Oak.WasmControl` extends it with structured labels, branches, loops,
and returns. Neither is a complete Core interpreter or a source-to-Wasm compiler
proof.

## Reference and supported boundary

The reference rules are Core's [numeric operations](https://webassembly.github.io/spec/core/exec/numerics.html)
and [instruction execution](https://webassembly.github.io/spec/core/exec/instructions.html),
read as WebAssembly 3.0 (2026-10-03). The existing assembler's
[pinned binary profile](https://github.com/WebAssembly/spec/tree/779957d81feca2ec6a372c40a9130e28ef390645)
remains unchanged. The new semantics is a manually authored model of these
rules, checked against an independent engine; no machine-checked equivalence
to the complete official specification is claimed.

| Family | Forms | Behavior |
| --- | --- | --- |
| Integer constants | i32.const, i64.const | Validated signed immediates become fixed-width bit patterns |
| Arithmetic and bitwise | add, sub, mul, div_s, div_u, rem_s, rem_u, and, or, xor for i32/i64 | Wrapping bit-vector results; explicit division/remainder traps |
| Comparisons | eq, ne, signed/unsigned lt, gt, le, ge for i32/i64; i32.eqz | Always produce i32 zero or one |
| Locals | local.get, local.set, local.tee | Bounds and value-type checks; set consumes, tee retains the stack value |
| Stack and traps | drop, nop, unreachable | Pop, identity, or explicit unreachable trap |

These are 49 of the assembler's 58 opcode forms. The remaining nine are
`block`, `loop`, `if`, `else`, `end`, `br`, `br_if`, `return`, and `call`.
They explicitly produce `unsupported` in the straight-line `WasmExecution`
entry points; none is interpreted as a no-op. The `WasmControl` entry point below
handles the eight control forms and still refuses execution of `call`.
The same boundary excludes memory, globals, references, floating point, SIMD,
and instructions not admitted by the scalar assembler.

The head of `State.stack` is the top. A binary instruction consumes the right
operand first, then the left. Widths must agree. Both values and locals carry
explicit i32/i64 types. All arithmetic uses bit vectors or mathematical integers;
signed quotient/remainder use truncation toward zero. Core signed division
traps on zero and MIN / -1. Signed remainder traps only on zero and returns zero
for a divisor of -1. Oak's wrapping division lowering remains the separate
`WasmNumeric.loweredSignedDiv` model.

`Fault.trap` distinguishes unreachable, divide-by-zero and integer-overflow.
Malformed byte/token encodings, stack underflow, type mismatch, invalid local
indices, and unsupported operations have separate diagnostic constructors.
They are model diagnostics for invalid or unsupported input states, not added
Core runtime traps. This model does not prove the module validator prevents
invalid states. `step` checks the token's immediate before executing it, so a
negative local index cannot become zero through `Int.toNat`.

## Universal claims

| Theorem | Result |
| --- | --- |
| `straight_line_opcode_count`, `operation_admitted`, `control_unsupported` | Exhaustive finite opcode partition: 49 modeled forms, all in the scalar profile, with all nine control/call forms excluded |
| `runBytes_assemble` | For every accepted instruction list, initial typed-value/local state and byte suffix, incremental decoded execution equals token execution, including faults; successful execution returns the untouched suffix |
| `assembled_execution` | The actual output of the mechanically extracted Oak assembler has that same execution result, using the established exact-byte theorem and its representable/disjoint-span preconditions |
| `applyBinary_words` | Correct left/right operand order, with arbitrary deeper stack values and all locals preserved |
| `compare_boolean` | Every comparison result is i32 zero or one, including i64 comparisons |
| `signed_division_traps`, `signed_remainder_neg_one` | Exact Core signed-division trap conditions and nontrapping remainder-by-minus-one |
| `core_signed_division_agrees` | The new division operation agrees with the existing Core signed-division model |
| `localWrite_preserves_types` | Successful set/tee preserve local-array length and every slot's value type; the success path requires an existing local slot |

`runBytes` consumes a syntactic instruction count, not a runtime control-flow
fuel. It decodes one token, executes it, and stops immediately on a fault.
It does not first decode an arbitrary suffix, and it does not execute a module's
function delimiter. A byte sequence may encode valid tokens while still being
ill-typed or containing control forms outside this model.

The assembler-to-execution theorem quantifies over every state. It establishes
agreement with this named model, including its diagnostics; it does not imply
that every assembled token sequence is a valid or trap-free program. Existing
compiler/extractor correspondence boundaries remain explicit.

## Production evidence

`compiler/wasm_execution_test.go` supplies one shared corpus of 1,983 cases.
A Go `math/big` oracle computes expected arithmetic and comparisons independently
of Lean's opcode dispatch. Both widths cover zero, one, two, 63, all-ones,
signed MIN, and signed MAX, with the full pair matrix for each binary/comparison
operation. The corpus also composes local.set/get/tee, drop and nop, and checks
all three runtime trap categories.

- `TestWasmExecutionEngine` builds modules from the production Go assembler,
  validates each with Oak's independent module checker, and executes all cases
  in Node or Deno. It checks result bits and whether a runtime trap occurred;
  engine exception messages are not used to classify trap reasons.
- `TestWasmExecutionLean` checks the same bodies through the independent byte
  decoder and Lean executor with `decide +kernel`. It adds a deeper stack
  sentinel and an undecodable suffix, and checks complete final local arrays.
  Ten additional malformed/invalid-state cases bring the total to 1,993 claims.
- `TestE2ESelfHostedWasmDecodedExecution` compiles Oak's assembler, obtains its
  actual output for 55 representative operation/trap cases, compares the bytes,
  and executes those output bytes in the independent engine. The test supplies
  the module envelope and final function delimiter.

Formal CI requires both Lean and the independent engine for the new gate.
The universal proofs use only Lean's standard `propext`, `Classical.choice`
and `Quot.sound` axioms where needed. Finite engine agreement is evidence for the
model, not a universal proof of the engine, Go implementation, or Oak compiler.

## Structured control

`Oak.WasmControl` adds execution of `block`, `loop`, `if`, `else`, `end`, `br`,
`br_if`, and `return` to the 49 scalar forms. This follows the assembler's
existing zero-parameter block profile: empty, i32, or i64 results, with no type
indices or multi-value block signatures. The reference is Core's
[instruction execution](https://webassembly.github.io/spec/core/exec/instructions.html)
and [label structure](https://webassembly.github.io/spec/core/exec/runtime.html).

A frame records its kind, result types, saved outer operands, continuation,
and loop restart body. Entering a block isolates its operand stack; scalar
instructions cannot consume values below that label. Normal fallthrough requires
exactly the declared results, restores the saved operands, and removes the frame.
A loop falls through once unless a branch explicitly restarts it.

Branching selects a relative label depth. Block/function targets carry their
result values and discard all intermediate operands and labels through the
target. Loop targets have zero branch arity in this profile, retain the target
frame, and restart its body. Their normal result arity may still be one.
`br_if` consumes an i32 condition: zero preserves the remaining operands and
labels; any nonzero bit pattern takes the branch. `return` unwinds to the
implicit function label. Locals remain shared within this single function.

`execute` accepts a function body **without its final function end token**,
caller-supplied local values, and result types in top-of-stack order. The tests
exercise empty and single-result signatures. It checks token encodings and all
control delimiters before running, including delimiters in unexecuted arms.
`splitBody` finds the matching outer end/else and retains nested delimiters in
the selected arm. This is not full module validation: unexecuted arms are not
type-checked and function/local/branch index validity is not established by a
validator proof. Direct `tick`, `enter`, `jump`, and `leave` are internal model
operations; their callers can construct states the public entry would not create.

`executeBytes` first decodes the selected syntactic instruction count, then
executes with separate runtime fuel. It preserves an external byte suffix on
success. Each machine transition consumes fuel, including frame exit; exhaustion
has its own `Error.exhausted` result, never a Core trap. Exhaustion neither proves
divergence nor imposes a production execution limit. Control diagnostics are
separate from scalar runtime traps. Executing `call` remains `unsupported`.

| Theorem | Result |
| --- | --- |
| `executeBytes_assemble` | Universal token/byte correspondence for all runtime fuels, locals, function results, and external suffixes, including errors and exhaustion |
| `assembled_execution` | Composes the actual extracted assembler's exact bytes with structured execution, retaining the assembler's span, capacity, and fuel preconditions |
| `takeResults_typed`, `takeResults_prefix` | Carried operands have the exact requested types/arity; arbitrary intermediate values are discarded |
| `branch_exit` | Exiting any non-loop target discards the selected inner labels and operands, restores the target's saved stack, and preserves locals |
| `loop_branch` | A loop branch restarts with an empty operand stack and retains the loop label even when normal completion returns a value |
| `leave_results` | Normal completion restores saved operands and removes the frame, including for loops |
| `br_if_zero`, `br_if_nonzero` | Exact untaken/taken conditional-branch transitions for all i32 condition bit patterns |
| `run_more` | A successful execution remains identical with any additional runtime fuel |

These are proofs about this named model. They do not establish equivalence to
the full official semantics, complete parser/validator correctness, absence of
model diagnostics on every valid module, or compiler control-flow refinement.

`compiler/wasm_control_test.go` provides 190 shared execution scenarios across
both integer widths. These include block/loop fallthrough, nesting depths through
eight, returns and branches to the function label, zero and nonzero conditions,
selected and skipped traps, summation loops, result-bearing loops with zero-arity
restart, and outer-loop branches through up to five inner blocks. Expected
results come from the scenario arithmetic rather than another label interpreter.

- `TestWasmControlEngine` checks production Go assembler bytes with the independent
  module checker and Node/Deno, comparing result bits and trap occurrence.
- `TestE2ESelfHostedWasmControl` executes all 190 bodies actually emitted by the
  compiled Oak assembler, after comparing their bytes to the Go assembler.
- `TestWasmControlLean` checks those same 190 bodies, complete local arrays, and
  suffix preservation with `decide +kernel`. Another 22 cases check malformed
  nesting, invalid states, call refusal, and fuel boundaries: 212 kernel claims.

Formal CI requires both new engine and Lean checks and includes the compiled
Oak test in its existing self-hosted gate. Universal proofs use only standard
Lean axioms where needed; no admitted proof or native decision oracle is added.

## Next boundary

Add direct calls and isolated call frames, argument/result transfer, and module
instantiation. Connect the module validator to typed execution and prove the
compiler's structured/dispatch control and selected instructions refine source
semantics. `TranslationVerified` remains false; the existing verified-mode
refusal is unchanged.
