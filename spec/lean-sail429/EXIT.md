# Machine-side readiness at the RV64 exit instruction

`OakSailExitSource.accepted_typed_exit_ready` extends the checked ELF-entry
prefix by one actual fetched ADDI instruction. It proves twelve iterations of
the existing generated platform callback, ending in phase 0 with unchanged step
cursor and six actual clock ticks. It then proves real fetch and decode of the
ECALL word at that PC. It does not execute ECALL.

## Exact bytes and result

The stronger `acceptsExit` retains the original restricted source, complete
ELF image, call pair, framed body, explicit loader/PMA installation and stack
checks. It additionally checks these exact eight bytes at `e_entry+8`:

- `93 08 d0 05`: `addi x17,x0,93`, the emitted `li a7,93`.
- `73 00 00 00`: ECALL at `e_entry+12`.

The earlier entry theorem deliberately accepted modifications to these excluded
exit words. Its scope and tests remain unchanged. The stronger readiness gate
rejects them. All three actual 4,680-byte AND/OR/XOR compiler-writer ELF images
are retained as complete kernel-checked literals; no synthetic main declaration
or silently different executable pipeline is substituted.

The twelve-callback state has PC=nextPC=`e_entry+12`, a7=93, and a0 equal to
`Oak.RiscV.widen 32 false (Oak.BitwiseFunction.eval op left right)`. The existing
RV64 integer ABI sign-extends the final 32-bit value to 64 bits even for u32:
for example, result `0x80000000` is represented as `0xffffffff80000000`, not
`0x0000000080000000`. High-bit controls check this representation. No initial
a7 mapping is required or secretly supplied by the constructive witness.

Actual generated `fetch ()` produces `F_Base 0x00000073` without changing state;
actual `ext_decode` produces `ECALL ()`, also without changing state. These are
readiness facts, not an assumed fetch, a simplified syscall interpreter, or a
claim that a host accepted a request.

The callback counter/timer result is `mcycle+6`, `mtime+6`, with the cycle value
modular and the strict natural timer premise `mtime.toNat+6 < mtimecmp.toNat`.
The witness starts its cycle counter at `2^64-2` and reaches 4; timer 0 reaches
6. The sixth-tick equality control proves the real CLINT dispatcher sets MTIP,
so the strict premise cannot be silently weakened. SP and saved registers remain
restored. ADDI and its tick do not modify the two saved frame words or any other
RAM. General register and nonregister preservation statements list the exact
intentional changes, including installed PMA regions and startup-derived x1.

`OakSailBoundedAppend.bounded_append` composes successful bounded runs without
assuming every callback yielded: a `done` branch is proved absorbing. It does
not give an unfolding or termination rule for the original opaque platform loop.

## Runtime boundary

This theorem retains the explicit Machine/Bare/open-PMP, initialized CSR,
interrupt, timer and ABI profiles. The production fixture selects the Linux
writer stub, but that does not make this initialized Sail state a Linux process.
Generated Machine-mode ECALL selects `E_M_EnvCall`, not User ECALL. A full
architectural trap-handling step would additionally need mapped trap CSRs;
no such handler, reset path or Linux loader/kernel is proved here.

The production freestanding RV64 writer uses a different stack-initializing
stub and the sifive_test MMIO finisher. This proof does not reinterpret the
Linux stub as that runtime. The source/symbol-extraction/ELF writer test boundary
is unchanged from [IMAGE.md](IMAGE.md) and [ENTRY.md](ENTRY.md).

A future User-mode proof must establish User fetch/data access, XLEN, SATP,
PMP, masking, decoder, interrupt and counter profiles throughout; it cannot
change privilege between the proved prefix and the exit boundary without a
justified transition. Linux/QEMU handling remains a separate external contract.
In the reference Linux ABI, 93 is thread `exit`, whereas `exit_group` is 94;
observable exit status uses only the low eight result bits. A process-termination
claim would need an appropriate single-thread or whole-process host contract.
These facts document a future interface and are not conclusions of this theorem:

- [Linux v6.12 syscall numbers](https://github.com/torvalds/linux/blob/v6.12/include/uapi/asm-generic/unistd.h#L245-L248)
- [Linux v6.12 exit implementation](https://github.com/torvalds/linux/blob/v6.12/kernel/exit.c#L992-L995)
- [QEMU v9.2 User ECALL dispatch](https://github.com/qemu/qemu/blob/v9.2.0/linux-user/riscv/cpu_loop.c#L45-L61)

## Validation and reproduction

The focused complete-ELF certificate checks all three real compiler artifacts,
exact suffix offsets, changed ADDI number/register/base, changed or moved ECALL,
source/claim/body/entry changes, the old-prefix/new-readiness acceptance
contrast, and high-bit ABI controls. A cheap full-signature interface preflight
runs first. Previous image/entry gates remain mandatory and unchanged.

`exit-audit.py` checks every new public theorem and both execution closures.
Private composition helpers are included transitively. Both source/readiness
corollaries must retain exactly the existing 77-name source-clocked closure;
no new opaque declaration, native-evaluation or sorry axiom is admitted.
Generated exporter faithfulness remains an external boundary.

From this pinned Lean 4.29 project:

    lake build OakSailBoundedAppend OakSailExitInstructions OakSailExitSource OakSailExitChecks
    python3 exit-audit.py

From the repository root:

    OAK_REQUIRE_RV64_LEAN=1 go test ./compiler -run '^TestRV64ExitReadyCompilerMatchesLean$' -count=1 -timeout=30m -v
