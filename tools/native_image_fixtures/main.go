// Command native_image_fixtures records complete production ELF executable images.
// Its parsing, metadata, hashes, and mutations are diagnostics, not proof authority.
package main

import (
	"bytes"
	"crypto/sha256"
	"debug/elf"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"strings"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/target"
)

type region struct {
	Family string `json:"family"`
	Offset int    `json:"offset"`
	Length int    `json:"length"`
}
type mutation struct {
	Name   string `json:"name"`
	Family string `json:"family"`
	Kind   string `json:"kind"`
	Offset int    `json:"offset"`
	Width  int    `json:"width,omitempty"`
	Value  uint64 `json:"value,omitempty"`
}
type fixture struct {
	ID                  string              `json:"id"`
	Target              string              `json:"target"`
	Operation           string              `json:"operation"`
	Function            string              `json:"function"`
	First               string              `json:"first"`
	Second              string              `json:"second"`
	SourcePath          string              `json:"source_path"`
	ImagePath           string              `json:"image_path"`
	SourceSHA256        string              `json:"source_sha256"`
	ImageSHA256         string              `json:"image_sha256"`
	SourceLength        int                 `json:"source_length"`
	ImageLength         int                 `json:"image_length"`
	Machine             uint16              `json:"machine"`
	Flags               uint32              `json:"flags"`
	TextOffset          uint64              `json:"text_offset"`
	TextSize            uint64              `json:"text_size"`
	TextHex             string              `json:"text_hex"`
	SectionHeaderOffset uint64              `json:"section_header_offset"`
	Sections            []elf.SectionHeader `json:"sections"`
	Symbols             []elf.Symbol        `json:"symbols"`
	Regions             []region            `json:"bit_flip_regions"`
	Mutations           []mutation          `json:"mutations"`
}
type field struct {
	name       string
	off, width int
}

var headerFields = []field{{"type", 16, 2}, {"machine", 18, 2}, {"version", 20, 4}, {"entry", 24, 8}, {"phoff", 32, 8}, {"shoff", 40, 8}, {"flags", 48, 4}, {"ehsize", 52, 2}, {"phentsize", 54, 2}, {"phnum", 56, 2}, {"shentsize", 58, 2}, {"shnum", 60, 2}, {"shstrndx", 62, 2}}
var programFields = []field{{"type", 0, 4}, {"flags", 4, 4}, {"offset", 8, 8}, {"vaddr", 16, 8}, {"paddr", 24, 8}, {"filesz", 32, 8}, {"memsz", 40, 8}, {"align", 48, 8}}
var sectionFields = []field{{"name", 0, 4}, {"type", 4, 4}, {"flags", 8, 8}, {"addr", 16, 8}, {"offset", 24, 8}, {"size", 32, 8}, {"link", 40, 4}, {"info", 44, 4}, {"align", 48, 8}, {"entsize", 56, 8}}
var symbolFields = []field{{"name", 0, 4}, {"info", 4, 1}, {"other", 5, 1}, {"shndx", 6, 2}, {"value", 8, 8}, {"size", 16, 8}}

func fatal(err error) {
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
func write(path string, b []byte) {
	fatal(os.MkdirAll(filepath.Dir(path), 0755))
	fatal(os.WriteFile(path, b, 0644))
}
func digest(b []byte) string { h := sha256.Sum256(b); return hex.EncodeToString(h[:]) }
func fieldValue(b []byte, off, width int) uint64 {
	var v uint64
	for i := 0; i < width; i++ {
		v |= uint64(b[off+i]) << (8 * i)
	}
	return v
}
func (f *fixture) mutateField(b []byte, family, prefix string, off int, fields []field) {
	for _, fld := range fields {
		f.Mutations = append(f.Mutations, mutation{Name: prefix + "_" + fld.name, Family: family, Kind: "set_le", Offset: off + fld.off, Width: fld.width, Value: fieldValue(b, off+fld.off, fld.width) ^ 1})
	}
}

// compileImage is only an untrusted proposal producer. The final complete bytes
// are independently re-decoded by Lean; no Go-decoded final symbol/address is
// passed as an admission premise. Preserve the exact original source, without main.
func compileImage(id, arch, name, source string) ([]byte, []byte, error) {
	object, err := compiler.New().WithSource(id+".oak", source).WithTarget(target.Target{OS: target.OSLinux, Arch: arch}).EmitNativeObject(asm.ELF).Get()
	if err != nil {
		return nil, nil, err
	}
	e, err := elf.NewFile(bytes.NewReader(object))
	if err != nil {
		return nil, nil, err
	}
	defer e.Close()
	machine := elf.EM_AARCH64
	flags := uint32(0)
	bodySize := uint64(8)
	lane := asm.ArchArm64
	if arch == target.ArchRiscv64 {
		machine = elf.EM_RISCV
		flags = 4
		bodySize = 36
		lane = asm.ArchRV64
	}
	if e.Class != elf.ELFCLASS64 || e.Data != elf.ELFDATA2LSB || e.Type != elf.ET_REL || e.Machine != machine || binary.LittleEndian.Uint32(object[48:52]) != flags {
		return nil, nil, fmt.Errorf("%s: object profile drift", id)
	}
	syms, err := e.Symbols()
	if err != nil {
		return nil, nil, err
	}
	var code []byte
	found := false
	for _, symbol := range syms {
		if symbol.Name != "oak_"+name {
			continue
		}
		if found || symbol.Info != 18 || symbol.Other != 0 || symbol.Section == elf.SHN_UNDEF || int(symbol.Section) >= len(e.Sections) {
			return nil, nil, fmt.Errorf("%s: invalid/duplicate function", id)
		}
		found = true
		sec := e.Sections[symbol.Section]
		data, err := sec.Data()
		if err != nil {
			return nil, nil, err
		}
		if sec.Type != elf.SHT_PROGBITS || sec.Flags != elf.SHF_ALLOC|elf.SHF_EXECINSTR || symbol.Value > uint64(len(data)) || symbol.Size > uint64(len(data))-symbol.Value || symbol.Size != bodySize {
			return nil, nil, fmt.Errorf("%s: body extent drift", id)
		}
		code = append([]byte(nil), data[symbol.Value:symbol.Value+symbol.Size]...)
		for _, rel := range e.Sections {
			if rel.Info == uint32(symbol.Section) && (rel.Type == elf.SHT_REL || rel.Type == elf.SHT_RELA) && rel.Size != 0 {
				return nil, nil, fmt.Errorf("%s: unresolved body relocations", id)
			}
		}
	}
	if !found {
		return nil, nil, fmt.Errorf("%s: missing source function", id)
	}
	image, err := asm.WriteExecutable([]asm.EncodedFunction{{Symbol: "oak_" + name, Bytes: code, Align: 4, Arch: lane}}, asm.ExecutableOptions{OS: asm.OSLinux, Arch: lane, Entry: "oak_" + name, Base: 0, RV64FloatABI: "double"})
	return object, image, err
}

func inspect(id, arch, op, name, first, second, source, imagePath, sourcePath string, b []byte) fixture {
	f := fixture{ID: id, Target: "linux/" + arch, Operation: op, Function: name, First: first, Second: second, SourcePath: sourcePath, ImagePath: imagePath, SourceSHA256: digest([]byte(source)), ImageSHA256: digest(b), SourceLength: len(source), ImageLength: len(b)}
	e, err := elf.NewFile(bytes.NewReader(b))
	fatal(err)
	defer e.Close()
	f.Machine = uint16(e.Machine)
	f.Flags = binary.LittleEndian.Uint32(b[48:52])
	f.SectionHeaderOffset = binary.LittleEndian.Uint64(b[40:48])
	for _, s := range e.Sections {
		f.Sections = append(f.Sections, s.SectionHeader)
	}
	f.Symbols, err = e.Symbols()
	fatal(err)
	t := e.Section(".text")
	if t == nil {
		fatal(fmt.Errorf("%s: no text", id))
	}
	text, err := t.Data()
	fatal(err)
	f.TextOffset = t.Offset
	f.TextSize = t.Size
	f.TextHex = hex.EncodeToString(text)
	stub, size, machine, flags := uint64(12), uint64(8), uint16(183), uint32(0)
	if arch == target.ArchRiscv64 {
		stub, size, machine, flags = 16, 36, 243, 4
	}
	loadSize := (stub + size + 15) / 16 * 16
	if e.Class != elf.ELFCLASS64 || e.Data != elf.ELFDATA2LSB || e.Type != elf.ET_EXEC || e.Entry != 0x10000 || len(e.Sections) != 6 || len(e.Progs) != 1 || len(f.Symbols) != 2 || t.Offset != 4096 || t.Size != stub+size || f.Machine != machine || f.Flags != flags {
		fatal(fmt.Errorf("%s: production executable shape drift", id))
	}
	p := e.Progs[0]
	if p.Type != elf.PT_LOAD || p.Flags != 5 || p.Off != 4096 || p.Vaddr != 0x10000 || p.Paddr != 0x10000 || p.Filesz != loadSize || p.Memsz != loadSize || p.Align != 4096 {
		fatal(fmt.Errorf("%s: load profile drift", id))
	}
	for i, s := range f.Symbols {
		want, value, extent := "_start", uint64(0x10000), stub
		if i == 1 {
			want, value, extent = "oak_"+name, 0x10000+stub, size
		}
		if s.Name != want || s.Info != 18 || s.Other != 0 || s.Section != 1 || s.Value != value || s.Size != extent {
			fatal(fmt.Errorf("%s: symbol drift: %+v", id, s))
		}
	}
	if e.Section(".rodata").Size != 0 {
		fatal(fmt.Errorf("%s: unexpected data", id))
	}
	sym, str, shstr := e.Section(".symtab"), e.Section(".strtab"), e.Section(".shstrtab")
	f.Regions = []region{{"header", 0, 64}, {"program", 64, 56}, {"header_padding", 120, 4096 - 120}, {"stub", 4096, int(stub)}, {"body", 4096 + int(stub), int(size)}, {"text_padding", 4096 + int(stub+size), int(loadSize - stub - size)}, {"symbols", int(sym.Offset), int(sym.Size)}, {"name", int(str.Offset), int(str.Size)}, {"section_names", int(shstr.Offset), int(shstr.Size)}}
	if f.SectionHeaderOffset > shstr.Offset+shstr.Size {
		f.Regions = append(f.Regions, region{"section_padding", int(shstr.Offset + shstr.Size), int(f.SectionHeaderOffset - shstr.Offset - shstr.Size)})
	}
	f.Regions = append(f.Regions, region{"sections", int(f.SectionHeaderOffset), 6 * 64})
	covered := 0
	for _, r := range f.Regions {
		if r.Offset != covered {
			fatal(fmt.Errorf("%s: region gap", id))
		}
		covered += r.Length
	}
	if covered != len(b) {
		fatal(fmt.Errorf("%s: trailing bytes", id))
	}
	for i := 0; i < 16; i++ {
		f.Mutations = append(f.Mutations, mutation{Name: fmt.Sprintf("header_ident_%d", i), Family: "header", Kind: "xor_byte", Offset: i, Value: 1})
	}
	f.mutateField(b, "header", "header", 0, headerFields)
	f.mutateField(b, "program", "program", 64, programFields)
	for i := 0; i < 6; i++ {
		f.mutateField(b, "sections", fmt.Sprintf("section_%d", i), int(f.SectionHeaderOffset)+64*i, sectionFields)
	}
	for i := 0; i < 3; i++ {
		f.mutateField(b, "symbols", fmt.Sprintf("symbol_%d", i), int(sym.Offset)+24*i, symbolFields)
	}
	for _, r := range f.Regions {
		if r.Family == "name" || r.Family == "section_names" || r.Family == "stub" || r.Family == "body" || r.Family == "text_padding" || r.Family == "section_padding" {
			for i := r.Offset; i < r.Offset+r.Length; i++ {
				f.Mutations = append(f.Mutations, mutation{Name: fmt.Sprintf("%s_byte_%d", r.Family, i), Family: r.Family, Kind: "xor_byte", Offset: i, Value: 1})
			}
		}
	}
	for _, i := range []int{120, 121, 2048, 4095} {
		f.Mutations = append(f.Mutations, mutation{Name: fmt.Sprintf("header_padding_byte_%d", i), Family: "header_padding", Kind: "xor_byte", Offset: i, Value: 1})
	}
	for _, n := range []int{0, 1, 15, 63, 64, 119, 120, 4095, 4096, 4096 + int(stub) - 1, 4096 + int(stub), 4096 + int(stub+size) - 1, int(sym.Offset), int(str.Offset), int(shstr.Offset), int(f.SectionHeaderOffset), len(b) - 1} {
		f.Mutations = append(f.Mutations, mutation{Name: fmt.Sprintf("truncate_%d", n), Family: "truncation", Kind: "truncate", Offset: n})
	}
	f.Mutations = append(f.Mutations, mutation{Name: "append_zero", Family: "append", Kind: "append_byte", Offset: len(b), Value: 0}, mutation{Name: "append_one", Family: "append", Kind: "append_byte", Offset: len(b), Value: 1})
	for _, m := range []mutation{
		{Name: "program_offset_overflow", Family: "bounds", Kind: "set_le", Offset: 72, Width: 8, Value: ^uint64(0)},
		{Name: "program_vaddr_overflow", Family: "bounds", Kind: "set_le", Offset: 80, Width: 8, Value: ^uint64(0)},
		{Name: "program_zero_fill_tail", Family: "bounds", Kind: "set_le", Offset: 104, Width: 8, Value: loadSize + 1},
		{Name: "program_writable", Family: "program", Kind: "set_le", Offset: 68, Width: 4, Value: 7},
		{Name: "function_short_prefix", Family: "extent", Kind: "set_le", Offset: int(sym.Offset) + 48 + 16, Width: 8, Value: size - 4},
		{Name: "function_extended", Family: "extent", Kind: "set_le", Offset: int(sym.Offset) + 48 + 16, Width: 8, Value: size + 4},
		{Name: "function_shifted", Family: "extent", Kind: "set_le", Offset: int(sym.Offset) + 48 + 8, Width: 8, Value: 0x10000 + stub + 4},
		{Name: "function_alias_start", Family: "symbols", Kind: "set_le", Offset: int(sym.Offset) + 48, Width: 4, Value: 1},
		{Name: "function_undefined", Family: "symbols", Kind: "set_le", Offset: int(sym.Offset) + 48 + 6, Width: 2, Value: 0},
		{Name: "function_wrong_section", Family: "symbols", Kind: "set_le", Offset: int(sym.Offset) + 48 + 6, Width: 2, Value: 2},
		{Name: "function_local", Family: "symbols", Kind: "set_le", Offset: int(sym.Offset) + 48 + 4, Width: 1, Value: 2},
		{Name: "function_object", Family: "symbols", Kind: "set_le", Offset: int(sym.Offset) + 48 + 4, Width: 1, Value: 17},
		{Name: "function_extent_overflow", Family: "bounds", Kind: "set_le", Offset: int(sym.Offset) + 48 + 16, Width: 8, Value: ^uint64(0)},
		{Name: "text_offset_overlap_header", Family: "extent", Kind: "set_le", Offset: int(f.SectionHeaderOffset) + 64 + 24, Width: 8, Value: 0},
		{Name: "symtab_wrong_link", Family: "sections", Kind: "set_le", Offset: int(f.SectionHeaderOffset) + 3*64 + 40, Width: 4, Value: 5},
		{Name: "symtab_extra_symbol", Family: "symbols", Kind: "set_le", Offset: int(f.SectionHeaderOffset) + 3*64 + 32, Width: 8, Value: 96},
		{Name: "rodata_extra_data", Family: "data", Kind: "set_le", Offset: int(f.SectionHeaderOffset) + 2*64 + 32, Width: 8, Value: 1},
		{Name: "rodata_relocation", Family: "relocation", Kind: "set_le", Offset: int(f.SectionHeaderOffset) + 2*64 + 4, Width: 4, Value: 4},
	} {
		f.Mutations = append(f.Mutations, m)
	}
	if arch == target.ArchRiscv64 {
		f.Mutations = append(f.Mutations, mutation{Name: "abi_soft_float", Family: "abi", Kind: "set_le", Offset: 48, Width: 4, Value: 0}, mutation{Name: "abi_rvc", Family: "abi", Kind: "set_le", Offset: 48, Width: 4, Value: 5})
	}
	return f
}
func main() {
	out := flag.String("out", "diagnostics/native-image-fixtures", "fixture output directory")
	verify := flag.Bool("verify-pins", false, "fail on any fresh complete-image digest/length drift from reviewed evidence.json")
	flag.Parse()
	var fs []fixture
	families := []struct {
		id, name, first, second string
		allOps                  bool
	}{{"mix", "mix", "a", "b", true}, {"Mix9", "Mix9", "left0", "Right9", true}, {"one", "f", "a", "b", false}, {"max256", strings.Repeat("N", 256), "a", "b", false}, {"over257", strings.Repeat("N", 257), "a", "b", false}}
	for _, arch := range []string{target.ArchArm64, target.ArchRiscv64} {
		for _, family := range families {
			for oi, op := range []struct{ name, symbol string }{{"and", "&"}, {"or", "|"}, {"xor", "^"}} {
				if oi > 0 && !family.allOps {
					continue
				}
				id := arch + "_" + family.id + "_" + op.name
				source := fmt.Sprintf("%s: (%s: u32, %s: u32): u32 = %s %s %s\n", family.name, family.first, family.second, family.first, op.symbol, family.second)
				object, b, err := compileImage(id, arch, family.name, source)
				fatal(err)
				f := inspect(id, arch, op.name, family.name, family.first, family.second, source, id+".elf", id+".oak", b)
				write(filepath.Join(*out, f.ImagePath), b)
				write(filepath.Join(*out, f.SourcePath), []byte(source))
				write(filepath.Join(*out, id+".o"), object)
				fs = append(fs, f)
				fmt.Printf("%s: image=%d bytes text=%d bytes sha256=%s\n", id, len(b), f.TextSize, f.ImageSHA256)
			}
		}
	}
	manifest := struct {
		SchemaVersion int       `json:"schema_version"`
		Producer      string    `json:"producer"`
		GoVersion     string    `json:"go_version"`
		Scope         string    `json:"scope"`
		Fixtures      []fixture `json:"fixtures"`
	}{1, "EmitNativeObject(ELF) -> untrusted complete-body proposal -> asm.WriteExecutable(linux,Base=0 selecting0x10000,RV64FloatABI=double)", runtime.Version(), "Diagnostics only. Lean independently validates the complete final image; no Go-supplied address or extracted final body is trusted.", fs}
	b, err := json.MarshalIndent(manifest, "", "  ")
	fatal(err)
	write(filepath.Join(*out, "manifest.json"), append(b, '\n'))
	pins := map[string]struct {
		Length       int    `json:"length"`
		SHA256       string `json:"sha256"`
		SourceSHA256 string `json:"source_sha256"`
		Name         string `json:"name"`
	}{}
	for _, f := range fs {
		pins[f.ID] = struct {
			Length       int    `json:"length"`
			SHA256       string `json:"sha256"`
			SourceSHA256 string `json:"source_sha256"`
			Name         string `json:"name"`
		}{f.ImageLength, f.ImageSHA256, f.SourceSHA256, f.Function}
	}
	b, err = json.MarshalIndent(pins, "", "  ")
	fatal(err)
	write(filepath.Join(*out, "evidence.json"), append(b, '\n'))
	if *verify {
		expected, err := os.ReadFile("tools/native_image_fixtures/evidence.json")
		fatal(err)
		if !bytes.Equal(expected, append(b, '\n')) {
			fatal(fmt.Errorf("fresh executable drift: review writer/profile; do not automatically regenerate pins"))
		}
	}
}
