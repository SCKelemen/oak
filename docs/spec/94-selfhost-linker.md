# Oak-hosted text object linker bootstrap

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
this admission routine. File readers, data/BSS layout, symbol visibility,
remaining relocation forms, compressed RV64, Mach-O, and proof refinement
remain separate M7/M8 obligations.
