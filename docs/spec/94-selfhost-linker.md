# Oak-hosted object linker bootstrap

`asm/selfhost/objects.oak` defines the first named-object linker profile in
Oak. The Go toolchain remains the production driver and compilation seed;
this profile is an executable kernel, not a complete self-hosted release.
It composes with `native.oak` for relocations and `elf.oak` for Linux ELF64
image output on both ARM64 and uncompressed RV64.

Inputs are immutable source/name byte pools and three record tables:

| Record | Fields | Meaning |
| --- | --- | --- |
| `NativeObject` | source, size, alignment | A nonempty source span and absolute load alignment |
| `NativeSymbol` | name, length, object, offset | A strong global text label, with an explicit byte-string name |
| `NativeObjectRelocation` | object, offset, kind, name, length | An object-relative patch site and referenced name |

Names are nonempty opaque byte strings: embedded zero bytes are allowed,
there is no terminator or Unicode normalization, and prefixes are distinct.
The definitions must be strictly increasing in unsigned byte lexicographic
order. This both rejects duplicate definitions and permits binary search.
The caller supplies sorted records, not resolved addresses. Every symbol,
including unused definitions, must identify an existing object and an aligned
offset strictly inside it. There are no weak/local symbols or addends yet.

Layout follows object order. For an object with alignment `a`, the next start
is the least offset at or above the previous end such that `base + start` is
a multiple of `a`. Alignments are powers of two from 4 through 4096; all text
extents, symbol offsets, and patch sites use four-byte boundaries. Source
fragments may share immutable bytes. Padding is zero-filled; the kernel does
not establish that execution cannot fall through into it.

The relocation kinds are ARM64 B, BL, ADRP+ADD and RV64 AUIPC+JALR-ra,
AUIPC+ADDI. A relocation must belong to the selected architecture, fit fully
inside its owning object, match the instruction/register pattern required by
the relocation kernel, and reach its resolved target without address wrap or
displacement truncation. Relocations must be sorted by object and offset and
have disjoint footprints. Every referenced name and the explicitly supplied
entry name must resolve exactly.

`native_link_objects` receives a mutable destination and one mutable `u32`
layout slot per object. It checks the complete layout, symbol table, entry,
and relocation plan before copying or patching destination bytes. On success
it returns `{status: 0, size: text_extent, entry: entry_offset}`; bytes beyond
the returned extent remain unchanged. On refusal it returns `{1, 0, 0}` and
preserves the entire destination, although scratch layout may have changed.
All inputs must be disjoint from writable borrows. The byte pools and tables
are caller-owned; the kernel allocates no storage. Symbol lookup costs
logarithmically many name comparisons per relocation; validation and copying
otherwise traverse their inputs linearly.

`TestE2ESelfHostedObjects` executes the compiled Oak implementation and checks
the complete destination on success and refusal, including invalid late
records, prefix/binary names, address overflow, absolute alignment and both
architecture lanes. `TestE2ESelfHostedELF` resolves a call across separate
startup/main objects, uses the returned entry for ELF generation, compares
the final text to the production Go assembler/linker, and requires execution
under ARM64 and RV64 QEMU in cross-target CI.

These tests establish bounded executable evidence. They do not constitute a
universal refinement proof of object admission, binary search, layout,
transactional mutation, or the ELF writer. Arbitrary instruction streams,
control flow, symbol types, loading and runtime behavior are not verified by
this admission routine. File readers, general section layout, symbol visibility,
remaining relocation forms, compressed RV64, Mach-O, and proof refinement
remain separate M7/M8 obligations.

## Writable data and BSS extension

`native_link_objects_data` extends the API with `data_address`, `data_size`,
and `bss_size`. Initialized data is followed immediately by zero-initialized
BSS. The combined extent must follow all text bytes and remain within the
unsigned 64-bit address space. The text-only entry point delegates with empty
data/BSS extents, retaining its original acceptance profile.

Two reserved `NativeSymbol.object` values name these sections:

| Object value | Symbol offset relative to | Permitted references |
| --- | --- | --- |
| `0xffffffff` | `data_address` | ARM64 ADRP+ADD, RV64 AUIPC+ADDI |
| `0xfffffffe` | `data_address + data_size` | ARM64 ADRP+ADD, RV64 AUIPC+ADDI |

The text object count is strictly below `0xfffffffe`. A data/BSS definition
must be strictly inside its nonempty section; arbitrary byte offsets are
allowed. It is never a valid entry or branch destination. Definitions still
share one sorted global namespace, so duplicate names across sections are
refused. Only text is patched; the image writer copies the data payload.

`native_elf_data_layout(text_size, data_size, bss_size, base, capacity)` returns
the planned file extent and section addresses. The text base is page-aligned,
and data begins at the first page boundary at or beyond the text end. File
data begins at `4096 + (data_address - base)`; BSS begins immediately after
the initialized bytes in memory. At least one RW memory byte is required;
empty data with nonempty BSS is legal. Total memory offsets and the file size
must fit `u32`, and absolute addresses must fit `u64` without wrapping.

`native_elf_data_image` uses the same layout and emits ELF64 for ARM64 or
uncompressed RV64 with two PT_LOAD headers. Text has R/X permissions, data
and BSS R/W. Their virtual page ranges do not overlap. The RW file size equals
the initialized data length; its memory size additionally includes BSS.
Alignment gaps are zeroed in the file, and bytes beyond the returned file
extent remain unchanged. On any refusal every destination byte is preserved.
The entry must remain inside aligned text. The caller must use identical
lengths/base when calculating addresses, linking text, and emitting the image.

`TestE2ESelfHostedELFData` covers both architectures with data+BSS and BSS-only
images. It independently reads ELF headers and decodes relocated addresses;
QEMU programs check zero initialization beyond EOF, then store/load and exit
with 42. The cross-target lane requires these executions. Admission tests
check image preservation after malformed layout/entry requests and named
symbol refusals, including branches to data and BSS.

## Placement laws and proof boundary

`native_place` is the pure placement step actually used by text and RW layout.
Its unsigned machine arithmetic corresponds to `Oak.LinkerLayout.place`,
which uses unbounded naturals and explicit representation bounds. The Lean
module proves alignment, minimal padding, monotone placement, positive extent,
destination/address bounds, disjoint consecutive placements, and in-range
symbol addresses. An additional bound proves that the widened intermediate
placement sums fit `u64` for the admitted input domains.

The same module defines a concrete ordered byte-write transaction and proves
that every rejection preserves the original byte store, any out-of-range
write (even after valid prefix writes) is rejected, and successful writes
preserve bytes outside the owned extent. That transaction is a model of the
validate-then-commit discipline; it is not an extraction or universal proof
of the mutable Oak object-linker implementation.

`TestE2ESelfHostedPlacement` compares 447 results from compiled Oak with a
separate big-integer ceiling-division oracle. It then renders those actual
Oak results as Lean `by decide` examples against the proved placement model.
Formal CI requires that kernel check. The universal model laws use ordinary
Lean proof terms; they contain no `sorry`, custom axioms, or native decision
certificates. Compiled-Oak correspondence remains bounded, and full byte-level
refinement of admission, symbol resolution, copying, patching, ELF loading,
and execution is still open.
