# RV64 selector routing certificates

`Oak.RiscVControlFlow` proves the register-resident, empty-edge-copy portion
of `machine/optir_rv64.go:optIRRV64Selector.terminator`. It connects the selected
plan and physical layout to execution of the actual branch words, using the
existing `Oak.RiscVDirectControl` decoder and execution proofs.

## Selected plans

| Successor layout | Emitted plan |
| --- | --- |
| Equal successors, target next | Fall through |
| Equal successors, target elsewhere | `j target` |
| True successor next | `beqz condition, false` |
| False successor next | `bnez condition, true` |
| Neither successor next | `bnez condition, true; j false` |

`assemble_sound` proves that executing each assembled plan reaches its selected
destination. The trace stops on a taken transfer, including when the numeric
target equals the next instruction address. `layoutAgrees` binds fall-through
to the actual end of the emitted plan; an instruction count alone cannot stand
in for that address check.

`checked_successor` states that every accepted certificate routes to the true
successor exactly when the condition register is nonzero, otherwise to the false
successor. It quantifies over every register state with x0 initially zero and
proves preservation of the register file. The source-level Bool is assumed to
agree with that register's zero/nonzero value.
`Oak.RiscVComparison` discharges this assumption for register-resident i64/u64
comparison producers; see [comparison proofs](94-rv64-comparison-proofs.md).

The module uses ordinary four-byte instructions, modular 64-bit PC arithmetic,
and IALIGN=16. It retains the underlying B/J encoding proofs' native
`bv_decide` dependencies. This is not an axiom-free claim or universal Go
implementation refinement.

## Production coverage

`machine/rv64_control_flow_lean_test.go` invokes the actual selector and
`asm.EncodeFunction` across all 24 orders of four blocks, equal and distinct
successors, and four condition registers: 192 layouts. Different block lengths
exercise forward/backward addresses independently of block IDs. All five
selected shapes must occur.

The corpus produces 672 Lean declarations:

- 192 accepted certificates over the actual emitted words and addresses.
- 192 applications of `checked_successor`, each valid for every register state.
- 96 rejected swapped-successor certificates.
- 192 rejected NOP substitutions or shifted empty-plan fall-through addresses.

An independent Go decoder also executes all 192 terminators with five register
values (zero, one, bit 32, bit 63, and all ones): 960 routing checks. It checks
that conditional instructions read the intended register and x0, and that jumps
discard their link. These checks run without Lean; the formal workflow requires
the Lean certificate checks as well.

```sh
cd spec/lean
lake build Oak.RiscVControlFlow
cd ../..
OAK_REQUIRE_RV64_LEAN=1 go test ./machine -run '^TestRV64ControlFlowSelector' -count=1
```

## Remaining obligations

Bool provenance beyond the i64/u64 comparison subset, register allocation
correctness, spilled conditions,
edge arguments/copies, compressed terminator layouts, block bodies, instruction
fetch, architectural traps, and whole-program execution remain separate work.
This slice proves the Lean routing model universally and supplies bounded
production certificates; it does not prove the complete compiler. It changes
no production behavior.
