package compiler

import (
	"bytes"
	"debug/macho"
	"encoding/binary"
	"fmt"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/target"
)

// Mach-O symbols have no function size. These fixtures deliberately emit one
// leaf per object, so the oracle can check the whole instruction section without
// guessing a boundary from RET or the next symbol (and losing a trailing trap).
// This is a byte-level regression witness, not an Arm execution theorem.
func aarch64MachOLeafWords(object []byte, symbol string) ([]uint32, error) {
	file, err := macho.NewFile(bytes.NewReader(object))
	if err != nil {
		return nil, err
	}
	defer file.Close()
	if file.Magic != macho.Magic64 || file.ByteOrder != binary.LittleEndian ||
		file.Cpu != macho.CpuArm64 || file.SubCpu != 0 || file.Type != macho.TypeObj {
		return nil, fmt.Errorf("want little-endian ARM64_ALL MH_OBJECT, got %+v", file.FileHeader)
	}
	if len(file.Sections) != 1 {
		return nil, fmt.Errorf("want one instruction section, got %d", len(file.Sections))
	}
	section := file.Sections[0]
	if section.Seg != "__TEXT" || section.Name != "__text" || section.Flags != 0x80000400 {
		return nil, fmt.Errorf("unexpected instruction section: %+v", section.SectionHeader)
	}
	if section.Nreloc != 0 || len(section.Relocs) != 0 {
		return nil, fmt.Errorf("instruction section has relocations; linker could change the checked words")
	}
	if file.Symtab == nil || len(file.Symtab.Syms) != 1 {
		return nil, fmt.Errorf("want exactly one leaf symbol")
	}
	entry := file.Symtab.Syms[0]
	if entry.Name != "_"+symbol || entry.Type != 0x0f || entry.Sect != 1 || entry.Value != section.Addr {
		return nil, fmt.Errorf("want external section-defined _%s at instruction-section start, got %+v", symbol, entry)
	}
	// Bound the section against the actual object before Data allocates or reads.
	start := uint64(section.Offset)
	if section.Addr%4 != 0 || section.Align < 2 || start%4 != 0 || section.Size == 0 || section.Size%4 != 0 ||
		start > uint64(len(object)) || section.Size > uint64(len(object))-start {
		return nil, fmt.Errorf("invalid instruction-section extent: offset=%d size=%d", start, section.Size)
	}
	data, err := section.Data()
	if err != nil {
		return nil, err
	}
	words := make([]uint32, len(data)/4)
	for i := range words {
		words[i] = file.ByteOrder.Uint32(data[4*i : 4*i+4])
	}
	return words, nil
}

func checkAArch64MachOLeafWords(object []byte, symbol string, want []uint32) error {
	got, err := aarch64MachOLeafWords(object, symbol)
	if err != nil {
		return err
	}
	if !slices.Equal(got, want) {
		return fmt.Errorf("%s whole instruction section = %#x, want %#x", symbol, got, want)
	}
	return nil
}

// Cross-emission requires neither a Darwin host nor Clang. In particular these
// privileged leaves are never loaded or executed in Apple userland.
func TestE2ENativeDarwinOrderingExactWords(t *testing.T) {
	cases := []struct {
		name      string
		operation string
		words     []uint32
	}{
		{"barrier_dmb_ishld", "dmb_ishld", []uint32{0xd50339bf, 0xd65f03c0}},
		{"barrier_dmb_ish", "dmb_ish", []uint32{0xd5033bbf, 0xd65f03c0}},
		{"barrier_dmb_sy", "dmb_sy", []uint32{0xd5033fbf, 0xd65f03c0}},
		{"barrier_dsb_ish", "dsb_ish", []uint32{0xd5033b9f, 0xd65f03c0}},
		{"barrier_dsb_sy", "dsb_sy", []uint32{0xd5033f9f, 0xd65f03c0}},
		{"barrier_isb", "isb", []uint32{0xd5033fdf, 0xd65f03c0}},
		{"tlbi_vmalls12e1is", "tlbi_vmalls12e1is", []uint32{0xd50c83df, 0xd65f03c0}},
		{"stage2_vmalls12e1is_context_sync", "", []uint32{
			0xd5033b9f, 0xd50c83df, 0xd5033b9f, 0xd5033fdf, 0xd65f03c0,
		}},
		{"stage2_bbm_ordering_slice", "", []uint32{
			0x340000e1, // cbz w1, trap
			0xf900001f, // str xzr, [x0]: break
			0xd5033b9f, // dsb ish
			0xd50c83df, // tlbi vmalls12e1is
			0xd5033b9f, // dsb ish
			0xf9000002, // str x2, [x0]: make
			0xd65f03c0, // ret
			0xd4200020, // trap: brk #1
		}},
		{"el2_cold_prepare", "", append(slices.Clone(coldEntryRegisterPrefix), 0xd5033fdf, 0xd65f03c0)},
		{"el2_cold_enter", "", append(slices.Clone(coldEntryRegisterPrefix), 0xd5033fdf, 0xd69f03e0)},
	}
	for _, test := range cases {
		t.Run(test.name, func(t *testing.T) {
			path := test.name + ".oak"
			var source string
			if test.operation != "" {
				source = fmt.Sprintf("package maintenance\nfn %s() -> () { arm64.%s() }\n", test.name, test.operation)
			} else {
				path = filepath.Join("..", "examples", "hypervisor", path)
				data, err := os.ReadFile(path)
				if err != nil {
					t.Fatal(err)
				}
				source = string(data)
			}
			object, err := New().WithSource(path, source).
				WithTarget(target.Target{OS: target.OSDarwin, Arch: target.ArchArm64}).
				EmitNativeObject(asm.MachO).Get()
			if err != nil {
				t.Fatal(err)
			}
			if err := checkAArch64MachOLeafWords(object, "oak_"+test.name, test.words); err != nil {
				t.Fatal(err)
			}
		})
	}
}

// Byte identity is not a semantic-verification verdict. Until the ordering
// execution seam is proved, neither object format may admit this DSB body into
// the strict profile, even though the ordinary native object gates pass.
func TestE2ENativeBBMOrderingObjectsRemainOutsideVerifiedProfile(t *testing.T) {
	path := filepath.Join("..", "examples", "hypervisor", "stage2_bbm_ordering_slice.oak")
	source, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	for _, test := range []struct {
		os     string
		format asm.ObjectFormat
	}{
		{target.OSFreestanding, asm.ELF},
		{target.OSDarwin, asm.MachO},
	} {
		t.Run(test.os, func(t *testing.T) {
			comp := New().WithSource(path, string(source)).
				WithTarget(target.Target{OS: test.os, Arch: target.ArchArm64})
			if object, err := comp.EmitNativeObject(test.format).Get(); err != nil || len(object) == 0 {
				t.Fatalf("ordinary native emission failed: %v", err)
			}
			object, err := comp.WithVerifiedProfile().EmitNativeObject(test.format).Get()
			if err == nil || len(object) != 0 {
				t.Fatalf("verified profile emitted a BBM object: %d bytes, error %v", len(object), err)
			}
			for _, want := range []string{"verified profile: 1 bodies are not proven", "trusted:", "stage2_bbm_ordering_slice"} {
				if !strings.Contains(err.Error(), want) {
					t.Errorf("verified refusal lacks %q: %v", want, err)
				}
			}
		})
	}
}

func machoOrderingFixture(t *testing.T, words []uint32, relocs []asm.Relocation, extra ...asm.EncodedFunction) []byte {
	t.Helper()
	var data []byte
	for _, word := range words {
		data = binary.LittleEndian.AppendUint32(data, word)
	}
	functions := append([]asm.EncodedFunction{{Symbol: "leaf", Bytes: data, Relocs: relocs}}, extra...)
	object, err := asm.WriteObject(asm.MachO, functions)
	if err != nil {
		t.Fatal(err)
	}
	return object
}

func TestAArch64MachOOrderingOracleRejectsMetadataDrift(t *testing.T) {
	want := []uint32{0xd5033b9f, 0xd65f03c0}
	object := machoOrderingFixture(t, want, nil)
	if err := checkAArch64MachOLeafWords(object, "leaf", want); err != nil {
		t.Fatal(err)
	}
	file, err := macho.NewFile(bytes.NewReader(object))
	if err != nil {
		t.Fatal(err)
	}
	defer file.Close()
	symbolAt := int(file.Symtab.Symoff)
	// This fixture is Oak's one-section LC_SEGMENT_64 layout: 32-byte header,
	// 72-byte segment command, then section_64. Offsets below mutate serialized
	// fields, so the independent standard-library parser also sees each mutant.
	const sectionAt = 32 + 72
	cases := []struct {
		name   string
		mutate func([]byte)
	}{
		{"wrong-cpu", func(b []byte) { binary.LittleEndian.PutUint32(b[4:], uint32(macho.CpuAmd64)) }},
		{"wrong-subcpu", func(b []byte) { binary.LittleEndian.PutUint32(b[8:], 2) }},
		{"executable", func(b []byte) { binary.LittleEndian.PutUint32(b[12:], uint32(macho.TypeExec)) }},
		{"wrong-section-name", func(b []byte) { b[sectionAt] = 'x' }},
		{"non-instructions", func(b []byte) { binary.LittleEndian.PutUint32(b[sectionAt+64:], 0) }},
		{"empty-section", func(b []byte) { binary.LittleEndian.PutUint64(b[sectionAt+40:], 0) }},
		{"partial-word", func(b []byte) { binary.LittleEndian.PutUint64(b[sectionAt+40:], 7) }},
		{"oversized-section", func(b []byte) { binary.LittleEndian.PutUint64(b[sectionAt+40:], ^uint64(0)) }},
		{"outside-object", func(b []byte) { binary.LittleEndian.PutUint32(b[sectionAt+48:], ^uint32(0)) }},
		{"unaligned-offset", func(b []byte) { binary.LittleEndian.PutUint32(b[sectionAt+48:], file.Sections[0].Offset+1) }},
		{"weak-alignment", func(b []byte) { binary.LittleEndian.PutUint32(b[sectionAt+52:], 0) }},
		{"undefined-symbol", func(b []byte) { b[symbolAt+4] = 0x01 }},
		{"debug-symbol", func(b []byte) { b[symbolAt+4] |= 0xe0 }},
		{"wrong-symbol-section", func(b []byte) { b[symbolAt+5] = 2 }},
		{"interior-symbol", func(b []byte) { binary.LittleEndian.PutUint64(b[symbolAt+8:], 4) }},
	}
	for _, test := range cases {
		t.Run(test.name, func(t *testing.T) {
			mutant := bytes.Clone(object)
			test.mutate(mutant)
			if err := checkAArch64MachOLeafWords(mutant, "leaf", want); err == nil {
				t.Fatal("accepted mutated object metadata")
			}
		})
	}
	for name, mutant := range map[string][]byte{
		"truncated":  object[:len(object)/2],
		"relocation": machoOrderingFixture(t, want, []asm.Relocation{{Offset: 0, Kind: "call26", Symbol: "leaf"}}),
		"extra-symbol": machoOrderingFixture(t, want, nil, asm.EncodedFunction{
			Symbol: "other", Bytes: []byte{0xc0, 0x03, 0x5f, 0xd6},
		}),
	} {
		t.Run(name, func(t *testing.T) {
			if err := checkAArch64MachOLeafWords(mutant, "leaf", want); err == nil {
				t.Fatal("accepted malformed or non-leaf object")
			}
		})
	}
	if err := checkAArch64MachOLeafWords(object, "missing", want); err == nil {
		t.Fatal("accepted a missing symbol")
	}
}

func TestAArch64MachOOrderingOracleRejectsInstructionDrift(t *testing.T) {
	want := []uint32{0x340000e1, 0xf900001f, 0xd5033b9f, 0xd50c83df, 0xd5033b9f, 0xf9000002, 0xd65f03c0, 0xd4200020}
	if err := checkAArch64MachOLeafWords(machoOrderingFixture(t, want, nil), "leaf", want); err != nil {
		t.Fatal(err)
	}
	cases := map[string][]uint32{
		"missing-trap": slices.Clone(want[:len(want)-1]),
		"extra-isb":    append(slices.Clone(want), 0xd5033fdf),
		"missing-dsb":  append(slices.Clone(want[:4]), want[5:]...),
	}
	for name, change := range map[string]struct {
		index int
		word  uint32
	}{
		"guard-target":   {0, 0x340000c1}, // branch to RET, not the trap
		"break-data":     {1, 0xf9000002}, // store X2, not zero
		"dmb-not-dsb":    {2, 0xd5033bbf},
		"local-not-ish":  {3, 0xd50c87df},
		"make-data":      {5, 0xf900001f},
		"trap-as-return": {7, 0xd65f03c0},
	} {
		words := slices.Clone(want)
		words[change.index] = change.word
		cases[name] = words
	}
	reordered := slices.Clone(want)
	reordered[3], reordered[4] = reordered[4], reordered[3]
	cases["tlbi-after-post-dsb"] = reordered
	for name, words := range cases {
		t.Run(name, func(t *testing.T) {
			if err := checkAArch64MachOLeafWords(machoOrderingFixture(t, words, nil), "leaf", want); err == nil {
				t.Fatal("accepted changed ordering, guard, store, or trap")
			}
		})
	}
}
