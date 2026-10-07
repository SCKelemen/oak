# Decoded scalar Wasm execution

`Oak.WasmExecution` adds a typed operand stack, local values, and incremental
byte execution for the straight-line part of the scalar profile. It connects
the [proved assembler output](91-wasm-assembler-proofs.md) to execution in this
model. It is not a complete Core interpreter or a source-to-Wasm compiler proof.

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
They explicitly produce `unsupported`; none is interpreted as a no-op.
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

## Next boundary

Add label/control stacks and structured blocks, loops and branches, then call
frames, returns and module instantiation. Connect the module validator to typed
execution and the compiler's selected instructions/control structure to source
semantics. `TranslationVerified` remains false; the existing verified-mode
refusal is unchanged.
