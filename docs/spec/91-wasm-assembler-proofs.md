# Wasm assembler and proof parity

Wasm has the same evidence obligations as the ARM64 and RV64 lanes: a named
profile, real encoding and decoding implementations, universal model laws,
production correspondence checks, and independent execution of output bytes.
The existing scalar profile has an instruction-encoding model and exact-byte
refinement of its mechanically extracted Oak instruction and sequence writers. It does not close source-to-module verification or full target parity.

## Implemented boundary

`wasm/encoding` is the Go scalar instruction assembler. `Instruction` contains
an opcode and an `int64` immediate. `Assemble` emits an ordered sequence, or
returns an error and no partial bytes. `AppendInstruction` rejects before
changing either the destination prefix or its spare backing storage.

| Instruction family | Immediate domain |
| --- | --- |
| block, loop, if | Exactly `0x40`, `0x7f`, or `0x7e`; no type-indexed blocks |
| br, br_if, call, local.get, local.set, local.tee | Unsigned 32-bit index |
| i32.const | Signed 32-bit carrier; reinterpret unsigned Oak constants first |
| i64.const | Signed 64-bit carrier, including MIN and MAX |
| Scalar-v1 numeric instructions and delimiters | No immediate; the field must be zero |

This is 58 opcode forms in total. All other opcodes refuse. Numeric instructions are the scalar-v1 comparisons,
add/subtract/multiply, divide/remainder and bitwise operations; `i64.eqz`, shifts,
memory, floating point, SIMD and extension prefixes are not silently admitted.
`else` and `end` are tokens, not standalone well-typed programs. The assembler
does not claim index resolution, control nesting, stack typing, or trap freedom.

`AppendUnsigned` and `AppendSigned` are the production emitter's LEB routines.
They emit canonical minimal encodings, including full-width uint64/int64 values.
The scalar profile only uses unsigned 32-bit lengths and indices. Existing
module bytes, scalar/check profile identities, and encoding recipe remain
unchanged by this extraction.

`wasm/check.DecodeInstruction` independently decodes one instruction prefix.
It returns the opcode, mathematical immediate and consumed length, leaving
trailing bytes unconsumed. It accepts legal padded LEBs but rejects truncation,
overlong encodings, wrong extension bits, unknown opcodes and block types.
Failure returns zero consumption and no instruction. The full module validator
uses this decoder and still checks every instruction's stack and control context.
The checker does not import the assembler or its opcode table.

## Oak implementation

`asm/selfhost/wasm.oak` implements unsigned/signed LEB sizing and writing,
scalar instruction classification/sizing/writing, and complete-sequence
assembly. No allocation or external assembler is used. The caller supplies
mutable destination storage and an immutable, disjoint instruction plan.

The instruction opcode is a `u32`, so values above 255 are explicitly refused
without truncating them. Signed LEB uses floor division by 128; Oak's
truncating division is corrected for negative remainders. Public writers
preflight the entire footprint with subtraction-based bounds checks. A writer
returns zero on failure, or its exact nonzero byte count. `wasm_assemble`
returns `{status, size}`; an empty plan succeeds with zero size. It validates
the complete plan and total capacity before writing, so a late malformed
instruction preserves the destination. Successful writes preserve bytes before
the offset and after the returned extent. Source/destination disjointness and
the runtime's span bounds are explicit preconditions.

These routines run through the Go compiler seed, as do the native bootstrap
assembler kernels. They are not yet the production driver, a WAT parser,
`.oakasm` integration, module linker, or a self-hosted compiler.

## Machine-checked claims

The binary rules retain the [pinned Core reference](https://github.com/WebAssembly/spec/tree/779957d81feca2ec6a372c40a9130e28ef390645).

| Model | Universal result |
| --- | --- |
| `Oak.WasmEncoding.encode_grammar` | Every in-range positive-width signed/unsigned input encodes to the independent `WasmLEB.Encoding` grammar |
| `decode_encode` | Decoding an encoded integer recovers its exact mathematical value and preserves any suffix |
| `encode_nonempty`, `encode_byte_budget` | Encoding consumes at least one byte and no more than the width budget |
| `Oak.WasmInstruction.decode_encode` | Every accepted opcode/immediate family decodes to the original pair and exact suffix |
| `encoding_injective` | Equal accepted instruction bytes identify equal opcode/immediate pairs |
| `decode_assemble` | Complete instruction sequences round-trip with their order, values and suffix preserved |
| `Oak.WasmNumeric.signed_division_refines`, `signed_division_traps_iff` | The signed-division guard implements Oak wrapping semantics for every input pair and traps exactly on zero; fixed-width corollaries cover both MIN / -1 cases |
| `Oak.Target` | Wasm32 is supported only with Core; its metadata is ILP32, container Wasm, native lane absent, and external C driver resolution refused even with an explicit compiler |
| `Oak.WasmAssembler.signed_next_floor` | The extracted Oak signed step computes mathematical floor division by 128 for every i64, including MIN |
| `range_guard_iff`, `admitted_store`, `reserve_no_wrap` | The actual subtraction guard admits exactly a mathematical in-bounds range; loop addresses and preflight additions do not wrap |
| `preflight_bound`, `assemble_success_bound` | The extracted first pass maintains its total-capacity invariant, and every successful assembly reports an extent within the original span |
| `write_uleb_refuses`, `write_sleb_refuses`, `write_instruction_refuses`, `assemble_failure_atomic` | Rejected footprints and every returned whole-plan failure preserve the complete destination, including late invalid instructions |
| `write_uleb_frame`, `write_sleb_frame` | Every returning extracted LEB writer preserves the array length and all bytes outside its reported extent |
| `uleb_size_exact`, `sleb_size_exact` | The extracted sizing loops terminate with the canonical encoding length for every u64/i64; ten guard evaluations suffice |
| `write_uleb_exact`, `write_sleb_exact` | The extracted public LEB writers terminate with exactly `WasmEncoding.encode` bytes and count when the footprint fits, or zero and the original storage otherwise; eleven guard evaluations suffice |
| `writeBytes_get`, `writeBytes_suffix` | Pointwise buffer contents are exactly the encoding inside the admitted window and the original bytes outside; reading from the offset yields the encoding followed by the untouched suffix |
| `write_uleb_decode`, `write_sleb_decode` | The independent `WasmLEB` decoder recovers every u64/i64 from the actual written buffer and returns the original suffix beyond the encoding |
| `instruction_kind_exact`, `instruction_size_exact` | Opcode dispatch matches the independent grammar, including rejection above 255; every instruction size terminates within ten fuel units and equals the accepted encoding length or zero on rejection |
| `write_instruction_exact`, `write_instruction_decode` | Every instruction write terminates within eleven fuel units, writes exact canonical bytes when valid and fitting, preserves the entire destination otherwise, and decodes from the actual buffer |
| `assemble_preflight_exact`, `assemble_emit_exact`, `assemble_admitted_exact` | Both extracted passes terminate for every valid fitting plan with `plan.size + 11` fuel, compute the exact size, and write the independent instruction sequence's bytes without wrapped addresses or counts |
| `assemble_decode`, `assemble_success_bytes` | Actual assembled output decodes to the original instruction tokens in order with the original suffix; array length and every byte outside the exact window are preserved |

Encoding recursion decreases the bit-width budget; it is not an execution-fuel
assumption. Sequence decoding uses a syntactic instruction count. The numeric law assumes already-evaluated integer operands; it does not prove
local selection or the emitted control structure. The encoding, numeric and
target models do not execute general control flow or prove guest memory safety.
The extracted LEB and instruction writers, and valid fitting plans, have the
bounded termination proofs described below.
The target model also corrects the existing RISC-V default CPU names
and places unsupported-target refusal before explicit C-driver selection, as
the current Go implementation does.

`WasmAssemblerExtracted.lean` is mechanically generated from the entire
`asm/selfhost/wasm.oak` through the normal type-checked Lean extractor.
`WasmAssemblerLaws.lean` proves properties of those generated definitions,
subject to the compiler/extractor correspondence and modeling choices in
[Lean extraction](95-extraction.md). The source is not duplicated by hand.
Mutable spans become threaded arrays; the plan and destination must be disjoint.
The original writer/frame and preflight laws quantify over arbitrary extraction
fuel and returning runs. `none` denotes fuel exhaustion, not assembler failure.

`WasmAssemblerBytes.lean` closes the LEB sizing and byte-content obligations.
For every u64/i64, the sizing loops compute the length of `WasmEncoding.encode`
with at least ten fuel units. With at least eleven units, each public LEB writer
returns its complete result for every representable span length and every u32
offset, including refusals. These bounds count guard evaluations in each
extracted loop; they are not processor instruction counts or a sufficient
budget for an entire assembly plan.

The byte proof relates both extracted writers to one integer-based sequence,
then proves that sequence equal to the canonical encoding. The public contract
requires `dst.size < 2^32`; it proves the exact footprint admission check,
returned byte count, complete buffer contents and unchanged-on-refusal result.
In-bounds readback and the independent decoder then establish value recovery
and preservation of the original suffix. The `admitted_store` law discharges
the nonwrapping address obligation; the readback proof requires the full window
to fit. No dropped out-of-range store is used to justify runtime safety.

`WasmAssemblerInstruction.lean` relates the complete extracted opcode dispatch
and operand checks to the independent scalar grammar. Canonical LEB bytes are
proved independent of width when a value fits both widths, connecting the
implementation's 64-bit helpers to the grammar's 32-bit operands. Instruction
sizing needs ten fuel units; writing needs eleven, including invalid inputs and
capacity refusals. No returned-run assumption is needed for these contracts.

`WasmAssemblerSequence.lean` composes these results through both extracted
assembly loops. For every valid fitting plan with `plan.size < 2^32`,
`dst.size < 2^32`, and fuel at least `plan.size + 11`, assembly returns success
with the exact independent byte sequence and count. Readback recovers every
opcode/immediate pair in order and the untouched original suffix. The pointwise
success frame covers every array index. The plan and destination remain disjoint.
These are extraction-loop budgets, not CPU instruction counts or a complexity
claim about generated code.

Whole-plan bounded termination for invalid or non-fitting plans remains open;
every returned whole-plan refusal already has a universal failure-atomicity law.
None of these byte proofs authorizes a source-to-module verification claim.

## Production evidence and gates

- `TestWasmEncodingMatchesLean`: Go encoder acceptance/refusal and actual bytes,
  independent decoder outcomes, every opcode, immediate boundaries, every bit
  transition, uint64/int64 endpoints, suffixes, padding and malformed bytes are
  rendered as kernel-checked Lean claims. It also exhausts target/architecture
  combinations for membership, pointer width and native lane.
- `TestWasmLEBMatchesLean`: retained independent reader/grammar correspondence.
- `TestInstructionRoundTrip`, known-byte and refusal tests: all opcode values,
  signed extrema, deterministic random constants, truncations, exact consumption,
  unchanged spare capacity on error and no partial assembly result.
- `TestE2ESelfHostedWasmAssembler`: compiled Oak is compared with the production
  Go assembler, including every opcode, out-of-byte-range opcodes, bounds,
  signed extrema, short destinations and complete destination preservation.
- `TestE2ESelfHostedWasmLEB`: full-width unsigned/signed encoders are compared
  at every bit transition, including extrema, suffix frames and short-buffer refusal.
- `TestLeanWasmAssemblerExtract`: regenerates the complete Oak assembler
  extraction and requires byte-for-byte agreement with the committed module.
- `TestLeanWasmAssemblerFaithful`: evaluates the extracted size, writer and
  assembly routines with kernel-checked `decide` claims. It shares instruction,
  full-width LEB and transaction corpora with the compiled-Oak tests, comparing
  complete buffers and returned counts/status against the Go encoder. Fuel
  exhaustion is explicitly distinct from ordinary refusal. The LEB corpus uses
  the proved bounds of ten sizing guards and eleven writer guards, including
  instruction operations. Plan checks use `instruction count + 11`, with a
  maximum-width operand late in a long plan and an explicit insufficient-fuel
  case. Refusing plans are also tested at that budget, without claiming their
  universal termination theorem.
- `TestE2ESelfHostedWasmTransactions`: the shared whole-plan corpus covers empty
  and mixed plans, exact fits, short storage, out-of-range offsets and late bad
  opcodes/immediates; every destination byte is checked.
- `TestE2ESelfHostedWasmExecution`: an instruction body assembled by compiled
  Oak is placed in a test module, independently validated, and executed by a
  JavaScript Wasm engine on full-width arithmetic inputs. The module envelope
  is supplied by the test; an Oak module writer is not claimed.
- The existing full Wasm/compiler suite retains exact output-size fixtures,
  branch/loop/call/Bool/trap cases and independent engine validation.

Formal CI requires both Lean production oracles, extraction drift and
correspondence checks, and the Oak execution tests;
missing Lean or the independent engine must fail the corresponding gate.
Axiom inspection of the new universal theorems reports only Lean’s standard
`propext`, `Classical.choice` and `Quot.sound` where used; there are no proof
holes or custom axioms. Finite Go/Oak/Lean agreement is not universal implementation
refinement. The universal claims are for the named models and, where stated,
the mechanically extracted Oak definitions under the extraction boundary above.

## Remaining parity obligations

| Boundary | Required next work |
| --- | --- |
| Implementation refinement | Prove bounded termination of whole-plan refusal; prove Go encoder and exact module parser/type-validator correspondence |
| Decoded semantics | Model values, operand/local/control stacks, calls, traps and module instantiation; connect every admitted numeric/control form |
| Compiler correctness | Source/OptIR-to-decoded-Wasm refinement, edge-copy and structured/dispatch control proofs, certificate identity and authoritative admission |
| Language/library coverage | Narrow integers, conversions and checked shifts; memory/aggregates/globals; explicit float/SIMD/atomic profiles; corresponding stdlib coverage |
| Modules and environment | Oak module writer and symbolic linking, layout/index/section-length proofs, declared browser/WASI imports and runtime contracts |
| Self-hosting | Compile and run the complete Oak compiler/prover/assembler on Wasm and independently check the exact resulting module artifacts |

`TranslationVerified` remains false and `-verified` continues to refuse. ARM64
or RV64 theorems cannot discharge these Wasm obligations; instruction encoding
theorems cannot authorize a source-to-module claim.
