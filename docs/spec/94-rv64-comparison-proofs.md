# RV64 comparison-to-successor proofs

`Oak.RiscVComparison` connects register-resident i64/u64 comparison producers
in `machine/optir_rv64.go` to the existing selector routing certificate. It
removes the assumption that the condition register already agrees with the
source Boolean for this producer subset.

## Instruction execution and composition

| Source operation | Selected instructions |
| --- | --- |
| `==` | `sub; seqz` (`sltiu rd,rd,1`) |
| `!=` | `sub; snez` (`sltu rd,x0,rd`) |
| `<` | `slt` or `sltu` |
| `>` | `slt` or `sltu` with reversed operands |
| `<=` | reversed `slt` or `sltu`, then `xori rd,rd,1` |
| `>=` | `slt` or `sltu`, then `xori rd,rd,1` |

`decode_encode` proves the instruction fields and opcode decoding for all
registers. `execute_plan` proves every comparison plan produces exactly zero
or one according to the original signed or unsigned 64-bit comparison. The
result may reuse either input register, including when both inputs and the
result share a register. The instruction reads happen before the write.
`result_preserves` states that other nonzero registers retain their values;
the architectural write always restores x0 to zero.

`checkProducer` accepts exactly the selected words with a nonzero destination.
`checked_producer` proves execution of every accepted producer for every
initial state. `checked_comparison_successor` composes it with
`RiscVControlFlow.checked_successor`: the producer runs first, the terminator
starts at its resulting PC, and the trace reaches the true or false successor
according to the **original operand values**. The resulting register file is
also specified. No initial condition-register agreement assumption is needed.

## Production evidence

`machine/rv64_comparison_lean_test.go` invokes the actual register-operation
selector, terminator selector, and `asm.EncodeFunction`. It covers:

- Six operators, both signedness choices, and six register assignments.
- All five routing shapes, backward targets, and a final block with no next
  block: 432 comparison/layout cases.
- Twelve boundary values per operand (restricted to equal values when inputs
  share a physical register): 43,200 independent Go executions checking the
  canonical result, register preservation, and successor address.
- 4,176 Lean declarations: 432 accepted producer certificates, 432 all-state
  composed theorem applications, and 3,312 rejected mutations.

Mutations change the destination or opcode of every producer word, truncate
at every prefix, append an extra instruction, request x0 as destination, or
flip the signedness of an ordered comparison. Equal-successor layouts still
require a valid producer even though the routing ignores its value.

```sh
cd spec/lean
lake build Oak.RiscVComparison
cd ../..
OAK_REQUIRE_RV64_LEAN=1 go test ./machine -run '^TestRV64(ControlFlow|Comparison)Selector' -count=1
```

The formal workflow requires both proof modules and the production certificate
tests. Ordinary Go-only jobs retain the independent byte-execution checks.

## Scope and trust

The Lean theorem is universal over states and admitted certificates; the Go
selector/assembler correspondence corpus is finite. Opcode/field and arithmetic
lemmas use Lean 4.33.1 `bv_decide`, retaining its native proof dependencies, as
do underlying ordinary branch encodings. This is not an axiom-free claim or a
universal refinement of the Go implementation.

The slice uses ordinary four-byte instructions, modular 64-bit PC arithmetic,
and the existing IALIGN=16 control model. It assumes the operand registers
represent the source i64/u64 values. Narrow integer canonicalization, other Bool
producers, allocation correctness, spills, SSA edge copies, compressed layouts,
instruction fetch, traps, and whole-program execution remain separate work.
It changes no production behavior.
