# ARM64 control-flow proofs

`Oak.AArch64ControlFlow` connects a scoped OptIR conditional terminator to
decoded AArch64 branch transitions. It imports the existing imm19 relocation
and execution proofs and the ordinary B/imm26 encoding proof. The new file
contains nine theorems with no admitted proofs or added axioms.

## Proved slice

The production entry is `machine/optir_aarch64.go`,
`optIRArm64Selector.terminator`, with a register-resident Bool condition and
no edge-copy instructions required on either successor. Its cases are:

| CFG layout | Emitted terminator |
|---|---|
| Both successors equal the next block | No instruction |
| Both successors equal, placed elsewhere | B to that block |
| True successor is next | CBZ W to the false successor |
| False successor is next | CBNZ W to the true successor |
| Neither successor is next | CBNZ W to true; B to false |

`selectPlan` models those choices. `select_destination` proves that each
choice selects the address of the source terminator's true or false edge,
provided the next block's address agrees with the physical end of the
emitted plan. Block IDs are independent of byte addresses. Targets may be
forward or backward, and the two successor IDs may be equal.

`stepControl` extends the existing no-fault conditional transition with
ordinary B. `jumpWord_step` proves the direct branch's target using signed
imm26 arithmetic and 64-bit PC addition. `localWord_step` composes the
previous conditional-branch proof. Both preserve registers and NZCV.

`assemble_sound` proves that the emitted zero-, one-, or two-instruction
plan reaches its selected destination. The finite `run` follows consecutive
words on fall-through and stops at the first taken transfer or the end of
the terminator. `check` compares the plan's assembled words with supplied
production words and checks physical fall-through layout. `checked_successor`
proves that every accepted certificate reaches:

```
if boolValue regs rt then address(true successor) else address(false successor)
```

for every register file and NZCV state, preserving both. `boolValue` reads
the low 32 bits of the selected register and tests nonzero; register 31 has
the existing zero-register interpretation. Relating that register value to
the source Bool is an explicit precondition of compiler-level composition.

For full-width register comparisons, that precondition is now established by
[comparison condition provenance](94-arm64-condition-provenance.md): the
decoded CMP/CSET prefix computes the Bool before this routing theorem runs.

## Production correspondence

`machine/aarch64_control_flow_lean_test.go` calls the actual terminator
selector, embeds its output in laid-out functions, and takes the words from
`asm.EncodeFunction`. The corpus covers all 24 orders of four blocks, equal
and distinct successors, four register placements, unequal block sizes,
and all five emission shapes. Lean checks 192 successful certificates and
288 negative cases: replaced branch words, misplaced omitted-branch
fall-through, and swapped true/false successors. These certificates inherit
`checked_successor` for all register/flag states, not just sampled Bool values.

`compiler/aarch64_control_flow_lean_test.go` also compiles actual 32- and
64-bit Oak loop bodies for ARM64, requires their existing translation
validation verdicts, lifts the selected assembly into the machine CFG, and
extracts branch words from the emitted ELF function symbols. Every witnessed
local branch gets a Lean theorem that its decoded transition reaches the
label address selected by the emitted assembly, for all register/flag states.
Forward and backward edges are both required. This test does not require an
ARM64 host or a cross assembler.

The machine CFG's target classification now treats B.AL and B.NV as
unconditional, matching the checker and executor. Regression tests check
both internal B.cond spellings across all sixteen condition fields; ordinary
conditions retain their fall-through edge.

The ARM64 conditional-proof workflow builds the new module and requires
Lean for both correspondence tests. Local runs may skip the Lean oracle if
`lake` is unavailable; `OAK_REQUIRE_ARM64_COND19_LEAN=1` turns that into a
failure in the required-oracle workflow.

## Remaining obligations

This is not a universal proof of the Go compiler. The model theorem is
universal; the correspondence between production and model is checked on
the stated finite corpus. Compiler transformations, general condition computation,
register allocation, spill loads, edge copies, body effects, block-address
uniqueness, and general whole-CFG simulation remain separate obligations.
The theorem addresses empty-copy Boolean terminators; it does not claim
equivalent coverage for every native lowering path.

The execution model remains a supplied-state, no-fault PC/register/NZCV
projection. Its finite terminator boundary is not an architectural fetch
loop. Padding execution, fetch/address/alignment faults, Arm's complete
PostDecode/BranchTo machinery, link-time layout changes, and whole-executable
correctness are not discharged here.
