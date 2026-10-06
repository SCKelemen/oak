# RV64 compressed control-transfer encoding proofs

This supplements [the assembler specification](94-assembler.md) and
`Oak.RiscVBranchEncoding`, which covers the 32-bit B and J forms.
`Oak.RiscVCompressedBranchEncoding` covers C.BEQZ, C.BNEZ, and C.J.

## Model and guarantees

The model pins the three rows from `asm/rv64_encodings_gen.go`, uses the generic
table field placement from `Oak.RiscV.Enc`, and transcribes the immediate
permutations from `rvcForm`. Independent decoders concatenate the encoded bits
in significance order. The [RISC-V C extension](https://docs.riscv.org/reference/isa/unpriv/c-st-ext.html)
defines these control-transfer formats and their signed, halfword-scaled
displacements.

| Form | Operand admission | Accepted byte displacement |
| --- | --- | --- |
| C.BEQZ / C.BNEZ | `rs1` is x8–x15 and `rs2` is x0, in that order | Even, −256 through +254 |
| C.J | JAL with `rd` = x0 | Even, −2048 through +2046 |

RV64 has no C.JAL. A local JAL writing x1 remains a 32-bit instruction.

The module proves:

- Every representable compressed displacement decodes to its original value.
- Encoding preserves the fixed opcode bits and the compressed source register.
- Successful local encoding is equivalent to the stated register, range, and
  displacement-alignment conditions.
- For every accepted local encoding, `place + decoded displacement = target`
  in unbounded integer arithmetic. Subtraction overflow cannot create acceptance.
- An accepted compressed branch decodes to the original architectural source
  register, including the x8 bias.
- Reassembling the emitted low byte followed by the high byte recovers the word.

The two field theorems quantify over finite bitvector domains and use `decide`
with kernel reduction. The other proofs use ordinary arithmetic and bitvector
lemmas. These theorems do not depend on native-evaluation or `bv_decide` axioms.
This does not change the trust boundary of other RV64 modules that use
`bv_decide`.

## Production evidence and checks

`asm/rv64_compressed_branch_lean_test.go` checks the pinned rows against the
generated opcode table. It exhausts all 6,144 combinations of opcode,
compressed source register, and representable displacement through the actual
encoder, plus all 2,080 architectural register admission combinations.

The Lean correspondence test turns 345 actual production acceptance/refusal
decisions into `by decide` claims. Cases include both range endpoints, just
outside the range, odd displacements, jointly odd addresses, invalid registers,
nonzero JAL destination registers, and signed host-integer subtraction overflow.
Missing labels are also rejected in Go.

A mixed-width function adds four byte-list claims from the actual function
writer. Its first branch initially sees displacement +256 and cannot compress.
Shrinking the next jump brings that displacement to +254 on the next pass;
shrinking the first branch then leaves a final target at +252. The test also
checks updated backward references, intervening 32-bit instructions, a JAL x1
that must remain uncompressed, and a compressed arithmetic tail.

Run the proof and production checks with:

```sh
cd spec/lean
lake build Oak.RiscVCompressedBranchEncoding
cd ../..
OAK_REQUIRE_RV64_LEAN=1 go test ./asm -run '^TestRV64CompressedBranch' -count=1
```

The formal workflow imports the module and requires the production Lean oracle.
Go-only environments skip that oracle if Lake is unavailable; the exhaustive
encoding and layout tests still run.

## Remaining boundary

These are encoding and exact-target proofs. They do not prove branch-condition
execution, instruction-address validity, an external Sail bridge for these
compressed rows, linker relocations, or a universal refinement of Go code.
The mixed-width layout case is regression evidence, not a proof of the whole
relaxation algorithm. A subsequent increment can formalize why shrinking
instructions preserves admitted displacements and why relaxation terminates.
