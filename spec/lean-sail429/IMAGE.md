# Source-bound ELF loading into the clocked RV64 frame

`OakSailImageSource.accepted_typed_image_clocked_prefix` connects the exact
restricted source declaration and admitted ELF image to nine bounded iterations
of the existing kernel-identified generated Sail platform callback. Every code
byte, fetch permission, frame permission, alignment, RAM bound and code/stack
separation fact is derived from the image admission and explicit load operation.
The original clocked theorem's `BytesAt`, `ExecutableRegion`, `LowCodeRAM`,
`FrameAccess` and `CodeStackDisjoint` assumptions are not repeated at this layer.

## Checked file and explicit load

`Oak.MinimalELF` checks ELF64 little endian, RV64 `ET_EXEC`, uncompressed LP64D
flags, one RX `PT_LOAD`, header/program-header locations and sizes, 4 KiB
page-congruent segment alignment, positive wholly file-backed segment extent,
entry at segment start, file bounds and nonwrapping 64-bit virtual addresses.
The complete 36-byte function must occur at the checked aligned virtual address
inside that exact segment. Section and symbol metadata are not parsed by Lean;
the production test extracts and checks the function symbol's address and size.
The load operation uses `p_vaddr`, not `p_paddr`, and does not interpret OS ABI
metadata, sections, relocations or a zero-fill tail.

`ImageLayout` additionally checks the whole loaded segment lies below the fixed
CLINT MMIO window, the selected stack pointer is 16-byte aligned and reserves a
nonwrapping 96-byte low-RAM frame, and the whole segment and frame are disjoint.
Both address orderings and touching, nonoverlapping boundaries are supported.

`checkedLoad` rejects invalid admission with `none`. On success it explicitly
copies every file-backed `PT_LOAD` byte into Sail's concrete sequential RAM and
installs two PMA regions: RX code and RW, non-executable stack. PMA installation
is a specified initialization operation, not a claim that an ELF flag configures
hardware automatically. It replaces `pma_regions`; all other registers, tags,
choice state, output and the separate `cycleCount` field are preserved. RAM
outside the loaded segment, including the reserved stack, is unchanged. The
loader does not execute instructions or initialize PC, ABI arguments or CSRs.

## Invocation and trust boundary

The execution theorem starts at the separately checked function address, not
at ELF `e_entry`. Callers explicitly supply PC/nextPC, ABI inputs, saved registers,
return address, the existing Machine/Bare/open-PMP/active-hart profile and mapped
CSR/timer state. A deadline beyond four ticks is required. The all-u32 result,
saved-register/frame behavior, nine generated `try_step` calls and four actual
clock ticks come from the existing theorem. The final cycle counter is modular.

`OakSailImageChecks.initialized_image_clocked_prefix` constructs these invocation
and platform hypotheses together, for arbitrary initial RAM, all u32 operands,
and arbitrary saved registers. Its cycle counter wraps from `2^64-2` to `2`.
This rules out contradictory initialization assumptions; it does not establish
that generated Sail reset, ELF startup, firmware or an OS reaches that state.

No universal correctness claim is made about the Go compiler, ELF writer,
symbol extraction, a host loader, opaque full platform iteration or termination.
The finite callback driver remains the scope of the execution claim.

## Actual compiler artifacts and negative controls

`TestRV64ImageBitwiseCompilerMatchesLean` compiles each exact single-declaration
AND/OR/XOR source through the production native pipeline to an ELF relocatable
object. It extracts the full `oak_mix` symbol, rejects unresolved relocations in
its range, and passes those exact bytes to production `asm.WriteExecutable`.
This two-stage route preserves the source identity required by the restricted
grammar; it does not append an unproved `main` declaration or call `EmitExecutable`.

Each currently emitted complete ELF is 4,680 bytes, with a 64-byte RX load
segment at file offset `0x1000` and virtual address `0x10000`. The full 36-byte
function begins at `0x10010`; startup at `0x10000` is not executed in the theorem.
All image bytes, including startup, padding and nonloaded metadata, are retained
in kernel-evaluated literals. Zero runs are represented by `List.replicate`, not
omitted. The actual image acceptance specializes the constructive execution
corollary for every u32 pair.

Mutants cover altered original source, type and claim; wrong/misaligned/outside
function addresses; instruction bytes; header/segment offsets and sizes;
truncation; incompatible permissions; multiple overlapping load entries;
zero-fill tails; 64-bit wrapping; and invalid or segment-overlapping stacks.
Boundary positives include disjoint frames below and above the exact segment.

`image-audit.py` fails closed on every new proof helper's axiom closure. Loader,
placement, permissions, preservation and profile construction use only standard
Lean axioms. Both source-image execution corollaries must have exactly the same
77-name closure as the existing source-clocked theorem, retaining its pinned
configuration/full-dispatch opaque parameters and `valid_reservation`. No new
opaque declaration, `sorryAx` or native-evaluation axiom is allowed.

Run in this pinned Lean 4.29 project:

    lake build OakSailImageLoad OakSailImageSource OakSailImageChecks
    python3 image-audit.py

And from the repository root with the pinned export present:

    OAK_REQUIRE_RV64_LEAN=1 go test ./compiler -run '^TestRV64ImageBitwiseCompilerMatchesLean$' -count=1 -timeout=30m -v
