package compiler

import (
	"bytes"
	"debug/elf"
	"os"
	"path/filepath"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/target"
)

// aarch64ObjectFunctionWords extracts one function from Oak's relocatable
// object. Keeping this at the object boundary checks the bytes that a linker
// consumes, rather than re-encoding the native backend's assembly text.
func aarch64ObjectFunctionWords(t *testing.T, object []byte, symbol string) []uint32 {
	t.Helper()
	file, err := elf.NewFile(bytes.NewReader(object))
	if err != nil {
		t.Fatal(err)
	}
	defer file.Close()
	if file.Type != elf.ET_REL || file.Machine != elf.EM_AARCH64 {
		t.Fatalf("object is %v/%v, want ET_REL/EM_AARCH64", file.Type, file.Machine)
	}
	symbols, err := file.Symbols()
	if err != nil {
		t.Fatal(err)
	}
	var functionSymbols []string
	for _, candidate := range symbols {
		if elf.ST_TYPE(candidate.Info) == elf.STT_FUNC {
			functionSymbols = append(functionSymbols, candidate.Name)
		}
		if candidate.Name != symbol {
			continue
		}
		if elf.ST_TYPE(candidate.Info) != elf.STT_FUNC {
			t.Fatalf("%s is ELF symbol type %v, want STT_FUNC", symbol, elf.ST_TYPE(candidate.Info))
		}
		if candidate.Section == elf.SHN_UNDEF || int(candidate.Section) >= len(file.Sections) {
			t.Fatalf("%s has invalid section %d", symbol, candidate.Section)
		}
		section := file.Sections[candidate.Section]
		data, err := section.Data()
		if err != nil {
			t.Fatal(err)
		}
		if candidate.Value < section.Addr {
			t.Fatalf("%s value %#x precedes section address %#x", symbol, candidate.Value, section.Addr)
		}
		start := candidate.Value - section.Addr
		end := start + candidate.Size
		if candidate.Size == 0 || candidate.Size%4 != 0 || end < start || end > uint64(len(data)) {
			t.Fatalf("%s has invalid byte range [%d,%d) in %s (%d bytes)",
				symbol, start, end, section.Name, len(data))
		}
		words := make([]uint32, 0, candidate.Size/4)
		for at := start; at < end; at += 4 {
			words = append(words, file.ByteOrder.Uint32(data[at:at+4]))
		}
		return words
	}
	t.Fatalf("object lacks function symbol %s; functions: %v", symbol, functionSymbols)
	return nil
}

func requireAArch64ObjectWords(t *testing.T, object []byte, symbol string, want []uint32) {
	t.Helper()
	got := aarch64ObjectFunctionWords(t, object, symbol)
	if len(got) != len(want) {
		t.Fatalf("%s has %d words, want %d: %#x", symbol, len(got), len(want), got)
	}
	for i := range want {
		if got[i] != want[i] {
			t.Fatalf("%s word %d = %#08x, want %#08x; body %#x", symbol, i, got[i], want[i], got)
		}
	}
}

const nativeBarrierWordsProgram = `
package barriers

fn barrier_dmb_ishld() -> () { arm64.dmb_ishld() }
fn barrier_dmb_ish() -> () { arm64.dmb_ish() }
fn barrier_dmb_sy() -> () { arm64.dmb_sy() }
fn barrier_dsb_ish() -> () { arm64.dsb_ish() }
fn barrier_dsb_sy() -> () { arm64.dsb_sy() }
fn barrier_isb() -> () { arm64.isb() }
`

// This is an executable source-to-object regression witness, not a
// substitute for the Lean encoder/Sail decoder proof. It also pins the native
// hot path to exactly one barrier instruction followed by RET.
func TestE2ENativeBarrierExactWords(t *testing.T) {
	tgt := target.Target{OS: target.OSFreestanding, Arch: target.ArchArm64}
	object, err := New().WithSource("barriers.oak", nativeBarrierWordsProgram).
		WithTarget(tgt).EmitNativeObject(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	const ret = 0xd65f03c0
	cases := []struct {
		symbol string
		word   uint32
	}{
		{"oak_barrier_dmb_ishld", 0xd50339bf},
		{"oak_barrier_dmb_ish", 0xd5033bbf},
		{"oak_barrier_dmb_sy", 0xd5033fbf},
		{"oak_barrier_dsb_ish", 0xd5033b9f},
		{"oak_barrier_dsb_sy", 0xd5033f9f},
		{"oak_barrier_isb", 0xd5033fdf},
	}
	for _, test := range cases {
		t.Run(test.symbol, func(t *testing.T) {
			requireAArch64ObjectWords(t, object, test.symbol, []uint32{test.word, ret})
		})
	}
}

var coldEntryRegisterPrefix = []uint32{
	0xd50342df, // msr DAIFSet, #2
	0xd51c1100, // msr HCR_EL2, x0
	0xd51c2101, // msr VTTBR_EL2, x1
	0xd51c2142, // msr VTCR_EL2, x2
	0xd51ce103, // msr CNTHCTL_EL2, x3
	0xd51ce064, // msr CNTVOFF_EL2, x4
	0xd51c4105, // msr SP_EL1, x5
	0xd51c4026, // msr ELR_EL2, x6
	0xd51c4007, // msr SPSR_EL2, x7
}

// The actual cold-entry examples carry the same exact context writes and ISB
// occurrence. Preparation returns; entry transfers with ERET. Pinning the
// complete leaf bodies makes both the ordering and absence of hidden barriers
// visible at the object seam.
func TestE2ENativeColdEntryExactWords(t *testing.T) {
	tgt := target.Target{OS: target.OSFreestanding, Arch: target.ArchArm64}
	cases := []struct {
		file     string
		symbol   string
		terminal uint32
	}{
		{"el2_cold_prepare.oak", "oak_el2_cold_prepare", 0xd65f03c0},
		{"el2_cold_enter.oak", "oak_el2_cold_enter", 0xd69f03e0},
	}
	for _, test := range cases {
		t.Run(test.file, func(t *testing.T) {
			path := filepath.Join("..", "examples", "hypervisor", test.file)
			source, err := os.ReadFile(path)
			if err != nil {
				t.Fatal(err)
			}
			object, err := New().WithSource(path, string(source)).WithTarget(tgt).
				EmitNativeObject(asm.ELF).Get()
			if err != nil {
				t.Fatal(err)
			}
			want := append([]uint32{}, coldEntryRegisterPrefix...)
			want = append(want, 0xd5033fdf, test.terminal)
			requireAArch64ObjectWords(t, object, test.symbol, want)
		})
	}
}
