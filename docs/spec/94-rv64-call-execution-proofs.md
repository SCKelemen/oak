# RV64 call, address, and indirect-jump execution proofs

`Oak.RiscVCallExecution` connects the existing `Oak.RV64Relocation` displacement
proof to instruction execution. It models modular 64-bit PC/register values,
x0 reads and discarded writes, AUIPC, ADDI, and JALR. The independent decoder
also covers C.JR and C.JALR. The model assumes IALIGN=16; it does not model
instruction fetch, memory, privilege, exceptions, or alignment traps.

The semantics follow the [RISC-V unprivileged ISA](https://docs.riscv.org/reference/isa/unpriv/rv32.html).
AUIPC adds the signed upper immediate to its own PC. JALR reads its source
before writing its destination, adds the signed immediate, and clears bit zero
of the target. Ordinary JALR writes PC+4; C.JALR writes PC+2. Register writes
and PC additions wrap at 64 bits.

## Universal statements

- JALR uses the old source even when the destination aliases it.
- Writes leave other nonzero registers unchanged and keep x0 zero.
- A call pair writes the AUIPC address plus eight as its return address.
- An address pair loads the decoded displacement plus the AUIPC address and
  falls through by eight bytes.
- `wide_pair` connects the executable decoder to pair semantics for every
  admitted pair shape. `patch_shape` proves relocation preserves that shape.
- `relocated_words` proves execution of every accepted relocation's patched
  words reaches the admitted call target and writes the return address, or
  loads the admitted data address and advances PC by eight.

The last theorem uses the existing displacement and range proofs, including
sign extension of the 20-bit upper and 12-bit lower fields. It covers negative
displacements and modular intermediate arithmetic. An accepted pair at the
top of the address space may have a return/fallthrough address wrapping to zero;
that is register arithmetic, not a claim that the return address is executable.

The proofs use standard Lean reasoning and `bv_decide` for fixed-field facts,
as does the imported relocation module. In the pinned Lean version the axiom
audit therefore includes the native bitvector decision dependency. This is not
a claim to remove that dependency from the existing proof chain.

## Production correspondence

`asm/rv64_call_execution_lean_test.go` checks 5,414 streams. Pair tests obtain
bytes and relocation metadata from `encodeRV64Function`, then apply the real
`resolveRelocations` symbol resolver. A leading NOP exercises nonzero relocation
offsets, including the two-byte compressed prefix. Pair instructions must stay
four bytes each under RVC, and relocation must preserve the prefix.

The corpus exercises both ends of the displacement range, rounding boundaries,
high addresses, all JALR source registers, zero/link/aliased/other destinations,
signed immediate endpoints, odd targets, modular wrap, and compressed and
ordinary forms of `ret` and `jr`. An independent Go decoder executes each stream
and checks all 32 registers. The same production bytes and expected observations
produce 5,414 Lean declarations checked with `decide`.

The byte oracle consumes a straight-line sequence ending at an indirect jump;
it refuses trailing instructions after JALR/C.JR/C.JALR, truncated instructions,
and the reserved/C.EBREAK zero-source compressed encodings. It is not a general
fetch loop or whole-program interpreter.

```sh
cd spec/lean
lake build Oak.RiscVCallExecution
cd ../..
OAK_REQUIRE_RV64_LEAN=1 go test ./asm -run '^TestRV64CallExecution' -count=1
```

The formal workflow requires the Lean correspondence check. Go-only jobs still
run the independent byte execution checks. The Go implementation, ELF serialization,
symbol resolution, and compiler lowering are not universally refined by these
proofs; the production connection remains bounded evidence. No production behavior
changes are introduced by this increment.
