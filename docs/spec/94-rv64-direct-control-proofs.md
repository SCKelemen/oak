# RV64 direct branch and jump execution

`Oak.RiscVDirectControl` connects the B/J and compressed CB/CJ encoding proofs
to instruction execution. It uses the six existing `Oak.RiscV.Br.holds`
predicates and the register/PC state from `Oak.RiscVCallExecution`.

## Universal statements

For every admitted field value and every initial state:

- Executing an encoded BEQ/BNE/BLT/BGE/BLTU/BGEU performs the corresponding
  comparison on the decoded source registers. Reads of x0 yield zero.
- A taken branch adds the signed displacement to its own PC. An untaken
  ordinary branch advances by four; an untaken compressed branch advances by two.
- Conditional branches preserve the register file, including an initially zero x0.
- Executing encoded JAL reaches the decoded target and writes PC+4 to a nonzero
  destination. Other registers are preserved and writes to x0 are discarded.
- C.BEQZ/C.BNEZ use registers x8–x15 and compare against zero. C.J writes no link
  and preserves nonzero registers. RV64's C.ADDIW encoding is not treated as C.JAL.

The `execute_encoded_branch`, `execute_encoded_jump`, `execute_encoded_cb`, and
`execute_encoded_cj` theorems connect the executable decoders to the existing
encoders, rather than assuming a decoded instruction already has the desired
fields. The PC and register lemmas specify the resulting effects. PC arithmetic
wraps at 64 bits.

The compressed execution theorems inherit kernel-reduced encoding proofs.
The ordinary B/J proofs retain the native `bv_decide` dependency of their
encoding proofs, plus the fixed-opcode exclusion fact used by the decoder.
This difference is visible in the axiom audit.

## Production evidence

`asm/rv64_direct_control_lean_test.go` checks 5,724 actual instruction streams:

- Every register number for all six B conditions and JAL.
- Negative/positive displacement endpoints and zero, with PC wrap.
- Equal, zero, sign-bit, all-ones, and 32/64-bit boundary operand values.
- Equal-source alias cases, including x0.
- Full function layout for beqz/bnez/bgez/bltz/blez/bgtz/j, with forward and
  backward labels and RVC both enabled and disabled.

An independent Go decoder executes each instruction and checks all registers.
For conditional branches, the actual production `branchCondition` result must
also agree. The corpus becomes 5,724 Lean `decide` declarations that execute the
same emitted bytes. The byte oracle accepts exactly one two- or four-byte
instruction, rejecting truncated streams and reserved condition encodings.

```sh
cd spec/lean
lake build Oak.RiscVDirectControl
cd ../..
OAK_REQUIRE_RV64_LEAN=1 go test ./asm -run '^TestRV64DirectControl' -count=1
```

Formal CI requires this oracle; Go-only environments retain the independent
byte and verifier checks. The slice changes no production behavior.

## Boundary

The semantics assume IALIGN=16 and do not model instruction fetch, memory,
traps, or privilege. These are universal proofs of the Lean encoding/execution
model, with bounded production correspondence. They do not universally refine
Go, compiler CFG lowering, full path execution, or whole-program linking.
