# Oak assembler and linker bootstrap core

This is the Oak assembler/linker bootstrap for roadmap M7/M8. The production
assembler, object reader/writer, and linker still run in Go. These routines
are compiled by the Go seed; this is not a self-hosted toolchain release.
The [object linker contract](../../docs/spec/94-selfhost-linker.md)
defines this bootstrap profile's admission and mutation rules.

## Implemented profile

`native.oak` assembles ARM64 B/BL and RV64 AUIPC+JALR/ADDI pairs and applies
these relocations to actual little-endian bytes:

| Kind | Architecture | Operation | Footprint |
| --- | --- | --- | --- |
| 1 | ARM64 | B | 4 bytes |
| 2 | ARM64 | BL | 4 bytes |
| 3 | ARM64 | ADRP + ADD (one non-SP register) | 8 bytes |
| 4 | RV64 | AUIPC ra + JALR ra, offset(ra) | 8 bytes |
| 5 | RV64 | AUIPC rd + ADDI rd, rd, offset (nonzero rd) | 8 bytes |

`native_relocate` returns `{status, first, second}`. Status zero means success;
all refusals return status one and zero words. All addresses are unsigned 64
bit. Branch targets are aligned, pair footprints cannot cross the address
space, and address subtraction cannot succeed by wrapping. RV64 admits the
exact displacement interval `[-2147485696, 2147481599]`, with even call targets.
Its pair kernel admits halfword instruction places for the C extension.

`native_link_patch` checks a complete footprint before reading or writing.
`native_link_text` accepts a sorted, nonoverlapping relocation plan and an
indexed table of resolved symbol addresses. It checks the entire plan before
writing, so a late error leaves all original bytes intact. It runs in linear
time with constant extra storage. Name resolution and symbol provenance are
still the caller's responsibility; there is no textual symbol table parser.

`objects.oak` adds `native_link_objects`: checked layout and named symbol
resolution over text objects, using the same relocation kernel. Each object
selects a span of a source byte pool and an absolute alignment (a power of two
from 4 through 4096). Each definition binds a nonempty byte-string name to an
object and an aligned offset strictly inside its text. Definitions are
strictly sorted by name, so duplicates and unsorted tables are refused;
lookups use binary search. Relocations identify names rather than addresses.
The caller supplies one `u32` scratch slot per object, but performs no address
resolution. Source ranges may overlap (reusing immutable bytes).

The function validates all objects, definitions, the named entry, and every
relocation before writing any destination byte. Refusal returns `{1, 0, 0}`
with the destination unchanged; scratch layout may have changed. Success
returns `{0, text_size, entry_offset}`, copies the source objects, zeroes
alignment gaps, and applies the admitted relocations. Bytes beyond text_size
are preserved. Alignment is computed against the absolute base, and all
extents and addresses are checked without wrapping. Input tables and byte
pools must be disjoint from writable borrows.

This profile has strong global text labels only, no addends, local/weak
symbols, data, BSS, archives, or object-file parser. Both ARM64 and RV64 use
four-byte instruction boundaries here; compressed RV64 remains outside this
object/ELF profile. Relocations are sorted by object and offset, nonoverlapping,
within their owning object, and restricted to the selected architecture.
Admission does not verify arbitrary instruction bytes or control flow.

`elf.oak` writes a minimal static ELF64 image over caller-owned storage:
AArch64 or uncompressed RV64, little endian, one read/execute PT_LOAD at a
page-aligned caller-supplied address, and an entry offset inside the text.
The text is already linked and includes caller-supplied startup code. It has
no section table, dynamic linking, writable data, or implicit runtime. The
RV64 profile declares soft-float ABI. The complete image size is returned;
zero indicates refusal without mutation. Source and destination storage must
be disjoint, as enforced by the Oak borrow checker. Internal word read/write
helpers require an in-bounds footprint.

`native_place` is the shared pure placement kernel: checked absolute
alignment with `u32` extents and `u64` address arithmetic. Text retains its
four-byte minimum alignment; the helper also admits one- and two-byte data
alignment. It returns `{status, start, end}` and zeros the offsets on refusal.

`native_link_objects_data` extends the text API with an initialized-data base
and data/BSS extents. `NativeSymbol.object = 0xffffffff` identifies data;
`0xfffffffe` identifies BSS immediately following it. Other indices still
identify text objects, whose count must be below `0xfffffffe`. Data/BSS
offsets are byte offsets strictly inside their section. These symbols may be
addressed by kinds 3 and 5, but never used as branch or entry targets. The
entire data/BSS extent must follow the text without address wrap. The routine
patches text only; it preserves the same all-or-nothing destination contract.

`elf_data.oak` provides `native_elf_data_layout` and `native_elf_data_image`.
The pure layout supplies data/BSS addresses before named text relocation. The
image writer emits two page-separated PT_LOAD segments: RX text and RW
initialized data followed by BSS. BSS contributes to memory size, not file
size; a BSS-only RW segment is supported. Text plus the RW memory extent fits
the `u32` layout domain, and the caller-owned file buffer bounds the image.
All image admission happens before writing. Callers pass the same text/data
lengths and base to layout, linking, and emission. There is still no dynamic
linking, section table, implicit runtime, or allocation.

## Evidence and limits

- `TestE2ESelfHostedRelocationKernel` compiles and executes the Oak routines on
  signed endpoints, malformed words, high addresses, refusal preservation,
  and deterministic generated ARM64 cases.
- `TestE2ESelfHostedELF` runs the Oak image writer for both architectures,
  resolving a named call between separately described startup/main objects,
  inspects its bytes with Go's independent ELF reader, compares its linked
  text byte-for-byte with the production assembler/linker, and runs both
  outputs to exit status 42 under user-mode QEMU. The cross-target CI lane
  requires the QEMU runs; local runs without QEMU report their absence.
- `TestE2ESelfHostedObjects` executes the object linker on forward/backward
  references, prefix and binary names, absolute alignment, high addresses,
  both target lanes, and malformed metadata. It compares every destination
  byte, including preservation after a late refusal.
- `Oak.RV64Relocation` specifies range admission and paired instruction fields,
  proves preservation of fixed bits and exact decoded target displacement,
  and records call target alignment. `TestRV64PCRelMatchesLean` renders
  production Go decisions as kernel-checked Lean examples in formal CI.
- Existing ARM64 branch and ADRP+ADD laws remain the ARM64 model anchors.
- `Oak.LinkerLayout` proves absolute alignment and minimal padding, admitted
  bounds, disjoint consecutive placements, in-range symbol addresses, and
  the safety of placement intermediates. Its concrete ordered byte-write
  transaction model proves refusal preservation, rejection of any out-of-range
  write including a late one, and preservation beyond the destination extent.
- `TestE2ESelfHostedPlacement` compares 447 compiled Oak placement decisions
  with an independent big-integer oracle and kernel-checked Lean examples.
  Formal CI sets `OAK_REQUIRE_LINKER_LEAN=1`; absence of Lean is an error there.
- `TestE2ESelfHostedELFData` executes named data/BSS references on ARM64 and
  RV64, including a BSS-only segment and a BSS cell on a page beyond EOF.
  Programs check its initial zero value, store/load it, and exit with 42.
  Independent ELF and instruction-field readers also inspect the image.
  `TestE2ESelfHostedELFDataAdmission` checks failed-image preservation and
  preservation past the file extent on success.

These are scoped model proofs and executable correspondence checks. They do
not yet prove refinement of the Go or Oak implementation, the ELF writer,
startup behavior, or the complete source-to-executable pipeline. Tests must
not be reported as universal implementation proofs.

## Wasm scalar assembler

`wasm.oak` adds caller-owned LEB and scalar instruction/sequence assembly for
`core/wasm32`. The [Wasm assembler contract](../../docs/spec/91-wasm-assembler-proofs.md)
lists the exact opcode/immediate domain, unchanged-on-refusal behavior,
universal Lean encoding laws, production correspondence and independent engine
tests. The Oak implementation is a bootstrap kernel; module writing, linking,
implementation refinement and source-to-module verification remain open.

## Remaining M7/M8 work

Port and prove the remaining emitted instruction forms and their decoders;
extend symbolic object admission/resolution beyond strong text/data/BSS labels;
add remaining relocations, object readers, multi-section data layout, and the
Mach-O profile; refine the actual Oak kernels against their models;
bind final image validation to source/ISA certificates
and the platform's loading/runtime contracts. Both ARM64 and RV64 remain
mandatory release targets.

The RV64 arithmetic follows the sign extension specified in the
[RISC-V RV64I ISA](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv64.html)
and the pair structure in the
[RISC-V ELF psABI](https://docs.riscv.org/reference/abi/v1.0/riscv-elf-object-files.html).
