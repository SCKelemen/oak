# Decoded Wasm execution, control and direct calls

`Oak.WasmExecution` adds a typed operand stack, local values, and incremental
byte execution for the straight-line part of the scalar profile. It connects
the [proved assembler output](91-wasm-assembler-proofs.md) to execution in this
model. `Oak.WasmControl` extends it with structured labels, branches, loops,
and returns. `Oak.WasmCalls` adds isolated direct calls in a closed function
table. These are not a complete Core interpreter or a source-to-Wasm compiler
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
`WasmCalls` handles direct calls while reusing the scalar/control transitions.
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

## Restricted successful u32 bitwise function composition

`Oak.BitwiseFunction` adds a separate, deliberately restricted function-body
boundary. The grammar is **exactly** `op(parameter 0, parameter 1)` for AND,
OR or XOR, with exactly two u32 parameters and one u32 result. It does not yet
include constants, arbitrary expression trees, casts, control, calls, memory,
traps, or explicit `return`. `WasmExecution.step` still rejects all nine
control/call forms; the new boundary consumes only the final function `end`.

The common meaning is `Oak.BitwiseFunction.eval` over two `BitVec 32` inputs.
For each operator, bytes are exactly `20 00 20 01 OP 0b` in hexadecimal, with
`OP` equal to `71`, `72`, or `73`. These are instruction bytes including the
final `end`, excluding the module envelope, code-entry length and local
declarations. Parameters are supplied as typed locals 0 and 1.

| Theorem | Concrete obligation established |
| --- | --- |
| `exact_encoding` | The independent instruction assembler emits the exact five body bytes |
| `body_success` | Token execution succeeds for every pair of u32 inputs and preserves locals |
| `assembled_function` | Successful typed token execution composes with exact decoded bytes and a final end; equal faults do not suffice |
| `function_success` | The exact six bytes return the common word result for every pair of inputs |
| `assemblyPlan_encoding` | The concrete extracted-assembler plan includes the exact body and end |
| `emitted_function_success` | The mechanically extracted Oak assembler terminates with success and six bytes, and its actual emitted span executes successfully for all u32 inputs |
| `accepts_iff`, `accepted_execution` | Exact target/ABI/signature/operator/whole-byte admission implies successful execution for every input |

The extracted-assembler theorem requires a destination length below 2^32,
sufficient room at the u32 offset, and at least 15 units of extraction fuel.
It inherits the existing disjoint-array/extraction modeling boundary. It
executes precisely the six-byte emitted span, not the unused destination
suffix. The function boundary rejects missing/wrong end, trailing bytes, an
empty or multi-value result stack, i64 results and ill-typed/missing locals.
Kernel-checked mutation examples also reject wrong native target/ABI, parameter
count/width, result width, changed operator/immediate/opcode, and truncation.
All new proofs use kernel reduction or existing proved lemmas, without `sorry`,
additional axioms, or native-decision shortcuts.

### Minimal named-module loading

`Oak.BitwiseModule` composes the function theorem with an independently
implemented binary loader for a single exported `(i32,i32)->i32` function.
It decodes LEB lengths and indices, checks every type/function/export/code
field, consumes each section payload exactly, requires the requested nonempty
ASCII export name (at most 256 bytes), and requires zero additional locals.
Extra types, functions, exports, sections, imports, start functions, memory,
custom sections and trailing bytes are outside this profile and refuse.
The only admitted type and function indices are zero.

`admitted_module_success` quantifies over **every admitted concrete module**,
its requested entry, target/ABI/signature/operator, and all u32 input pairs.
It concludes successful named-entry invocation with the common word result.
It does not merely compare the input with a fixture: the loader parses the
binary structure, and `padded_type_length_admitted` demonstrates acceptance
of a legal noncanonical LEB section length. Function instruction bytes remain
bound to the exact bitwise profile. Wrong lengths/indices/type/name/locals,
operator bytes and trailing sections cannot be ignored to reach the success
path. `canonical_loaded`, `canonical_admitted` and `canonical_success` give
constructive instances for the real emitter's three 45-byte modules.

`single_bit_mutations_refused` kernel-checks all 360 single-bit changes per
operator (1,080 total), in addition to truncation, extra-section, wrong-entry,
width, target, ABI and operator regressions. These finite regressions support
the universal admission theorem; they do not prove arbitrary mutation coverage.

`compiler/wasm_bitwise_module_test.go` compiles three actual Oak source files
through the production compiler, checks source-level export signatures and
exact module bytes, and asserts `TranslationVerified` remains false. Node
independently validates, instantiates and executes the emitted modules on a
72-by-72 input grid per operator (15,552 executions). The existing required
`TestWasmExecutionLean` lane additionally builds the module proof and generates
all-input Lean success theorems for the **actual emitted byte literals**.
This is concrete-artifact proof plus production correspondence testing, not a
universal Go parser/lowering/emission refinement or an external-engine theorem.

The loader and invocation are named Lean models. Their relation to the Go
module checker and the complete external Core Wasm semantics remains open.
There is no production admission consumer, no source-text identity theorem,
and no new authority for `-verified`.

### Source-to-bytecode completion checklist

The checked boxes describe only this restricted slice. An unchecked link is
an unmet obligation, not a premise silently discharged by the existing model.

- [x] Explicit two-parameter u32 AND/OR/XOR meaning and exact Wasm-local signature
- [x] Successful, all-input execution rather than agreement that could preserve a fault
- [x] Exact instruction bytes, final end consumption and single-i32 result boundary
- [x] Mechanically extracted Oak assembler termination, emitted byte span and execution composition
- [x] Fail-closed target/ABI/width/operator/byte admission and kernel mutation regressions
- [ ] Source text/parser and checked AST provenance connected to this expression and parameter order
- [ ] Production Go lowering/selection/emission connected to the proved plan and bytes
- [ ] Constants and arbitrary expression-tree compilation to the same word meaning
- [x] Restricted independent-model section/type/export/index/local loading connected to named invocation
- [ ] Production Wasm loader/validator and external Core semantics refined to that model
- [ ] RV64 emitted bytes, ABI boundary and pinned external Sail execution connected to this common meaning
- [ ] ARM64 emitted bytes, ABI boundary and pinned external ISA execution connected to this common meaning
- [ ] Concrete Go graph/root/CNF/LRAT provenance and certificate freshness/source identity
- [ ] Full core-formal and cross-backend CI for the final integrated revision
- [ ] Production certificate-backed verdict authority, only after all required concrete soundness links

There is no certificate consumer in this module; stale-certificate and source
identity rejection are not claimed. `VerdictProven` and `TranslationVerified`
behavior is unchanged. A native internal-decoder theorem alone does not check
the external ISA semantics. These component results do not establish complete
source-to-bytecode parity for any backend.
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
separate from scalar runtime traps. Executing `call` through this single-function
entry remains `unsupported`; use `WasmCalls.invoke` for function tables.

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

## Direct calls and isolated frames

`Oak.WasmCalls` models a closed array of defined functions. Each `Function`
contains parameter/result types, declared local types, and an instruction body
without the final function end token. Parameter and result lists use declaration
order; the operand stack remains top-first. `invoke` checks external arguments
exactly and installs the entry function. The behavioral reference is Core's
[function invocation and return rules](https://webassembly.github.io/spec/core/exec/instructions.html).

`call` resolves the unsigned function index, checks/pops arguments in reverse
parameter order, then reverses them into local-index order. Extra declared locals
are fresh typed zeros on every activation. It suspends the caller after the call
instruction, including its remaining operands, locals, and labels. The callee
starts with an empty operand stack and only its own function label.

Normal fallthrough, `return`, and branches to the function label first use the
existing control model's result checks. `resume` prepends the returned operands
to the saved caller stack and restores the caller locals, labels, and continuation.
Callee local writes cannot change caller locals, and a callee branch cannot name
a caller label. Traps propagate through the entire invocation. Direct and mutual
recursion use the same transitions and explicit runtime fuel. Exhaustion is a
model bound, not a Core trap or a claim of divergence.

| Theorem | Result |
| --- | --- |
| `activate_arguments` | Exact declaration-order parameters, fresh zero locals, empty operand stack, and an isolated function label for any typed arguments and deeper stack |
| `call_arguments` | Consumes exactly the argument prefix and suspends the remaining caller state and all older callers |
| `resume_caller` | Returns values above saved operands while restoring caller locals, labels, and code exactly |
| `decodeFunction_assemble` | Decoding an assembled body recovers that body and the untouched suffix, retaining supplied metadata |
| `decoded_invocation` | Replacing an in-bounds table slot with its decoded assembled body preserves every invocation at every runtime fuel, including recursive calls |
| `assembled_function` | Actual extracted assembler output recovers the intended function body under the existing span/capacity/fuel preconditions; composes with invocation correspondence |
| `run_more` | Successful whole-table invocation execution remains identical with additional fuel |

The function table and signatures are supplied directly, not recovered from a
proved module parser/instantiator. Every activated body receives encoding and
nesting checks, but unused functions and untaken branches are not fully validated.
These checks do not replace static module validation or prove that valid modules
avoid all model diagnostics. Internal machine operations assume properly formed
call/control states; theorems state their actual premises. Full Core refinement
and preservation/progress for all valid modules remain open.

`compiler/wasm_calls_test.go` supplies 133 shared scenarios: both integer widths,
noncommutative argument order, caller operand/local/label preservation, nested
calls, recursive factorial, mutual recursion, repeated fresh locals, mixed-width
parameters, void calls, early returns/branches, and three propagated trap kinds.
Expected values are computed from each scenario, independently of the call model.
Tests exercise empty and single-result function signatures; generic list-based
transfer laws do not claim independently tested multi-result module support.

- `TestWasmCallsEngine` builds complete multi-function modules from production
  assembler bytes, validates them with the independent checker, and executes them
  in Node/Deno, comparing result bits and trap occurrence.
- `TestE2ESelfHostedWasmCalls` runs the same 133 modules using every function body
  actually emitted by the compiled Oak assembler, with exact-byte comparisons.
- `TestWasmCallsLean` decodes each production body (checking an untouched suffix)
  before invoking it with `decide +kernel`. Eleven additional diagnostics cover
  invalid indices/arguments/results/locals/nesting, caller-label isolation, and
  recursive exhaustion: 144 kernel claims.

Formal CI requires the new engine and Lean corpus. As with the earlier layers,
these finite comparisons support the model but do not prove the Go encoder,
compiler, engine, module writer, or the complete official semantics correct.

## Next boundary

Connect binary modules, index resolution, and instantiation to the function-table
model. Prove validator correspondence and typed execution preservation/progress,
then compiler structured/dispatch control and instruction selection refinement.
Imports, memory/globals, and the wider target profile also remain open.
`TranslationVerified` remains false; verified-mode refusal is unchanged.
