# Source-bound execution from the actual RV64 ELF entry

`OakSailEntrySource.accepted_typed_entry_clocked_prefix` starts at the checked
ELF `e_entry`, executes the emitted startup call pair, and composes the existing
nine-instruction source-bound body. It proves eleven successful bounded
iterations of the kernel-identified generated platform callback, including five
actual clock ticks, for every pair of u32 arguments. No caller-supplied return
address or function-entry PC premise remains.

## Exact compiler artifact and startup

The production fixture reuses the full-image pipeline: compile the original
single-declaration AND/OR/XOR source, extract the complete relocation-free
`oak_mix` body, and call production `asm.WriteExecutable`. It does not invent a
`main` declaration or prove arbitrary Go compiler correctness. All 4,680 original
ELF bytes are retained in the kernel-evaluated literal. The current RX segment
starts at file offset `0x1000`, virtual address and entry `0x10000`, and contains
64 bytes. The 36-byte body starts at `0x10010`.

The two fetched startup words are:

- `0x00000097`: `auipc x1, 0`, setting x1 to `e_entry`.
- `0x010080e7`: `jalr x1, x1, 16`, reading old x1, jumping to `e_entry+16`,
  then setting x1 to the already prepared sequential link `e_entry+8`.

The proof uses unchanged generated `encdec_backwards`, `execute_UTYPE`,
`execute_JALR`, `fetch`, `try_step`, and the actual platform callback, rather
than extending a simplified supported-instruction interpreter. Each step's
physical reads and RX permission derive from the explicit loader's RAM and PMA
state. No fetch-success assumption is introduced.

`acceptsEntry` checks both the complete source-bound body at `e_entry+16` and
these exact eight startup bytes at the same ELF's entry. Existing full ELF,
segment bounds, permissions, overflow and stack-disjointness checks apply.
The explicit load/PMA installation semantics remain those in [IMAGE.md](IMAGE.md).
`entryState` additionally initializes PC and nextPC to the checked entry and
sets `minstret_increment` false. Those are stated initialization operations,
not effects attributed to ELF flags or a generated reset.

## Result and remaining initialization

AUIPC/JALR preserve RAM, SP, arguments, callee saves and all other registers
except x1 and the stated PC/retirement bookkeeping. The phase sequence for
the pair is 0 → 1 → 0; its second callback executes a clock tick. The existing
nine body callbacks then end in phase 1, with the callback step cursor unchanged.
Total counters are `mcycle+5` and `mtime+5`; the cycle value is modular. The
timer premise is strictly `mtime.toNat+5 < mtimecmp.toNat`, preventing wrap and
pending timer interrupts. `fifth_tick_at_deadline` checks actual CLINT behavior
at equality: MTIP is set, so the unchanged below-deadline state is false.

Final PC and nextPC equal `e_entry+8`, x1 retains that derived return address,
x10 is the widened typed source result, and SP/x9/x18 are restored. Only the
two saved eight-byte frame words change during execution. The full state
identity and preservation projections account for all other registers, RAM,
tags, output, choice state and the separate interpreter `cycleCount` field.

The initial Machine/Bare/open-PMP, active-hart, RV64I, masking, interrupt,
retirement, mapped CSR and timer profiles remain explicit, as do SP, u32 ABI
arguments and saved registers. `initialized_entry_clocked_prefix` constructs
them together from arbitrary state. It leaves initial x1 untouched and proves
all u32 inputs work even if x1 was absent. Its counter starts at `2^64-2` and
ends at 3, with timer 0 → 5 and deadline 100. This is nonvacuity, not reset,
firmware or OS reachability.

The return lands on the emitted `addi x17,x0,93`; the following word is `ecall`.
Neither instruction is executed by this theorem. Machine-mode ECALL would need
its own trap/ABI analysis; no Linux exit, termination of the opaque platform
loop, arbitrary ELF loader, or universal compiler correctness is inferred.

## Checks and trust

The production startup certificate checks all three complete original images,
entry/body/file offsets, the derived return value, mutated opcode/destination/
base/immediate instructions, changed ELF entry, changed source/claim/body, and
an accepted image whose excluded post-return ADDI/ECALL words alone change.
The discarded-link (`rd=x0`) mutant is rejected. Cheap interface applications
run before the complete-image certificate. The earlier 98-claim full ELF gate
remains mandatory; the startup gate does not replace or repeat those claims.

`entry-audit.py` audits every new theorem and fails on missing or unlisted
axioms. Both source-entry execution corollaries must retain exactly the existing
77-name source-clocked closure. AUIPC's body needs only standard Lean axioms;
JALR additionally retains the existing experimental-extension opaque parameter.
The finite generated dispatch carries its already audited configuration and
unselected full-dispatch dependencies. No new opaque declaration, native
reduction axiom, or `sorryAx` is admitted. Pinned generated source/exporter
faithfulness remains an external boundary.

From the pinned Lean 4.29 project:

    lake build OakSailEntryInstructions OakSailEntrySource OakSailEntryChecks
    python3 entry-audit.py

From the repository root:

    OAK_REQUIRE_RV64_LEAN=1 go test ./compiler -run '^TestRV64EntryBitwiseCompilerMatchesLean$' -count=1 -timeout=30m -v

The required hosted RV64 job builds/audits these modules and runs the startup
fixture alongside all existing fetched, stepped, clocked and full-image gates.
