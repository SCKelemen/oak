# ARM64 SSA edge-copy proofs

`Oak.AArch64EdgeCopies` extends the register-resident control-flow slice to
SSA edges with parallel copies. It adds eight Lean theorems with no admitted
proofs or added axioms. The result certifies an actual emitted schedule;
it does not prove the Go scheduling algorithm correct for every input.

## Execution and certificate

The independent decoder accepts only MOV W/X register aliases of unshifted
ORR with a zero-register first operand. W moves zero-extend the low 32 bits;
X moves preserve all 64 bits. Reads from ZR return zero and writes to ZR are
ignored. The projected state canonicalizes ZR's unused backing slot to zero.
PC advances four bytes per copy and NZCV is unchanged.

A symbolic register stores an original source register and whether its upper
32 bits have been cleared. `execute_eval` proves that symbolic execution
commutes with concrete execution for every original register file.
`checkCopies` compares the resulting symbols with simultaneous SSA
assignments, checking all registers except reserved scratch X17. It refuses
source/destination use of X17, destination ZR, and duplicate destinations.

The expected assignments read original values, so swaps, longer cycles,
fan-out and overlapping chains cannot pass merely by executing moves in
source order. The real selector saves cycle values in X17 at full width.
Mixed W/X schedules are supported. A self-copy is omitted by the selector;
the certificate therefore requires preservation, including upper bits,
instead of promising normalization for an instruction that was not emitted.

`checked_copies` proves the copy result and preservation of other registers
for every accepted certificate and initial state. `checked_edge` composes
it with the previous decoded routing theorem for both unconditional jumps
and physical fall-through. `checked_conditional` follows decoded dispatch
to distinct edge-stub addresses, executes that stub's copies and final branch,
and reaches the selected source successor with the selected simultaneous
assignment. Copying over the condition register is permitted after dispatch.

## Production evidence

`machine/aarch64_edge_copies_lean_test.go` calls the actual `terminator`,
`edgeMoves`, and `emitEdgeCopies` routines and reads bytes from
`asm.EncodeFunction`. Expected moves are built from SSA arguments and target
parameter locations before scheduling.

- 432 accepted unconditional-edge certificates: nine assignment patterns,
  all 16 W/X width combinations for four destinations, and forward,
  backward, or fall-through layouts.
- 773 rejected mutations/contracts: deleted initial moves, non-MOV opcodes,
  a naive sequential swap, reserved-register misuse, and duplicate destinations.
- Eight conditional-edge certificates, each also instantiating the universal
  `checked_conditional` theorem for arbitrary register/NZCV states. These
  cover W/X moves, forward/backward successor placement, and a condition
  register that is either preserved or overwritten by the selected copies.

The ARM64 workflow builds this module and requires these production checks
under `OAK_REQUIRE_ARM64_COND19_LEAN=1` alongside the existing proof gates.

## Remaining boundary

This is a no-fault PC/register/NZCV projection. The decoded MOV semantics are
a local projection; this module does not establish a full Arm fetch-loop
refinement. Source values are assumed to occupy the supplied locations.
Allocation correctness, spills, memory, rematerialization, ABI obligations,
whole-CFG simulation, architectural faults, and a universal proof of the Go
scheduler remain separate work. The finite production checks do not establish
universal compiler correspondence. No new source-to-ELF coverage is claimed.
