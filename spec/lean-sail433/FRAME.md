# Complete RV64 framed execution boundary

The new result is restricted to a **freestanding Machine/Bare state profile**.
It does not prove an arbitrary Linux user-mode virtual-memory environment.
QEMU user-mode smoke tests are complementary tests; they do not discharge these
Sail state premises.

`OakSailFramedComposition.accepted_typed_frame` checks the restricted original
source declaration, its existing typed-expression meaning, and all 36 bytes of
the actual production function. The pinned external decoder decodes all nine
words, then unchanged generated instruction bodies execute in their original
order. The result is successful retirement for every pair of u32 inputs, with
LP64D sign extension preserved in x10. `accepted_typed_full_frame` in
`OakSailFramedFullDispatch` proves the same result through generated `execute`.
The full-dispatch selection equality is proved by kernel reduction.

## Concrete state premises

- x2, x9, x18, x10, x11, x1 and nextPC have explicit mapped values. x10/x11
  contain the sign-extended u32 arguments. x1 is the return address.
- `cur_privilege=Machine`, `mstatus=0` (MPRV off), `mseccfg=0` (pointer masking
  and landing-pad enforcement off), and misa is RV64I with compressed
  instructions disabled. The bit-cleared return address satisfies IALIGN=32.
- Original SP is at least 96 and is 16-byte aligned. Thus subtracting 96 does not
  wrap. `saved_slots_bounds` proves both stores fit within the reserved frame.
- `pmpcfg_n` is the 64-entry vector of 0x1f; `pmpaddr_n` is the 64-entry vector
  of 0xffffffffffffffff. The actual first NAPOT entry matches and permits the
  accesses. No PMP success oracle is assumed.
- `pma_regions` has an explicit list. At each of SP−96 and SP−88, the actual pure
  region search finds an explicit readable/writable region containing all eight
  bytes, and the access is aligned. `RAMRegion` records these configuration
  predicates; actual `pmaCheck` success is proved from them.
- Both eight-byte accesses end at or below 0x02000000; `htif_tohost_base=none`.
  Actual MMIO dispatch therefore bypasses fixed CLINT/signature windows and HTIF.

Only the 16 bytes actually accessed need permission. No prior stack-byte
membership is required: the unchanged Sail sequential store inserts all eight
bytes into `SequentialState.mem : Std.ExtHashMap Nat (BitVec 8)`. The later loads
read those concrete entries. Successful reads are proved from byte membership,
not assumed. The remaining 80 reserved bytes are untouched.

## Exact effects and boundaries

`frame_instructions_run` returns `finalFrameState`: the initial state with two
little-endian saved words at SP−96 and SP−88, x10 set to the bitwise result,
and nextPC set to x1 with bit0 cleared. Original SP, s1/x9 and s2/x18 are restored.
All other register mappings are preserved, including PC and x1. Memory entries
outside those 16 addresses preserve their original values or absence. Choice
state, cycle count and output are unchanged. The helper theorems in
`FramedRestoration.lean` expose each observation and the exact state equality.

The driver supplies bytes and decodes the complete sequence before invoking
its nine bodies. It does not fetch instructions from memory, tick PC, execute
interrupts or the generated step loop, initialize this platform, load an ELF,
prove hardware-cache behavior, or perform Linux syscalls. Because code fetch is
outside this driver, no code/data separation claim is inferred. It proves the
u32 function result, not an OS process's eight-bit exit status. These limits
remain even though all stack instruction bodies now execute externally.

The earlier flat-memory framing theorem is retained. No unproved universal
mapping from that total memory function to Sail's finite byte map is asserted;
the new chain directly proves source meaning against the concrete Sail result.

## Opaque declarations and kernel audit

`audit.py` checks the framed closure separately from earlier narrow and full
claims. It admits no `sorryAx`, `native_decide`, `bv_decide` native-evaluation
axioms, or unlisted dependencies. Concrete byte, PMP, restoration and footprint
lemmas use only propext, Classical.choice and Quot.sound.

The bounded framed closure also references the following unchanged declarations
from pinned `LeanRV64D/RiscvExtras.lean`:

- Line 31: `plat_term_write.{u} : {α : Sort u} → α → LeanRV64D.SailM Unit`
- Line 35: `load_reservation : [Sail.ConcurrencyInterfaceV1.Arch] → Arch.pa → Nat → LeanRV64D.SailM Unit`
- Line 36: `match_reservation : [Sail.ConcurrencyInterfaceV1.Arch] → Arch.pa → Bool`
- Line 41: `sys_enable_experimental_extensions : Unit → Bool`

In this RV64 model, the physical address type is BitVec 64. The terminal and
load-reservation declarations are opaque effectful model operations, not
propositions asserting execution correctness. The match/configuration
parameters return Boolean values. No value or successful effect is assumed.
Non-MMIO proofs exclude the terminal-I/O path; reservation flags are false, so
reservation branches are not taken and the pure match result is irrelevant.
The experimental-extension value does not affect the supported normalized path.
Lean's transitive axiom report still includes references in those unused branches.

The unrestricted generated dispatcher retains its previously enumerated 76
axioms/parameters, including unused floating-point and other instruction
primitives. The narrower framed driver retains 7 total dependencies. File
separation does not remove broader dependencies from claims using the full
selection agreement. Exact names and the new typed signatures are recorded in
`axiom-allowlist.json`.

## Reproduce and provenance

Use the committed default Lake configuration and the preparation instructions
in README.md. The required graph uses unchanged provenance-checked model/Sail
sources compiled with Lean 4.33.1 alongside the Oak source proofs. It excludes
optional RvfiDii and does not consume 4.29 compiled proof objects. Existing global
pins, compiler output and production verification authority remain unchanged.

Run `lake build` and `python3 audit.py` in this directory. The existing required
Sail workflow explicitly builds both new public modules before that audit.
Malformed length, changed prologue byte, stack underflow, misalignment and
non-writable-region checks are kernel-checked examples in the composition file.
