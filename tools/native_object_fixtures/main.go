// Command native_object_fixtures records complete production ELF objects.
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
	ObjectPath          string              `json:"object_path"`
	SourceSHA256        string              `json:"source_sha256"`
	ObjectSHA256        string              `json:"object_sha256"`
	SourceLength        int                 `json:"source_length"`
	ObjectLength        int                 `json:"object_length"`
	Machine             uint16              `json:"machine"`
	Flags               uint32              `json:"flags"`
	TextOffset          uint64              `json:"text_offset"`
	TextSize            uint64              `json:"text_size"`
	BodyHex             string              `json:"body_hex"`
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
func leanBytes(b []byte) string {
	var s strings.Builder
	s.WriteByte('[')
	for i, v := range b {
		if i > 0 {
			s.WriteByte(',')
		}
		fmt.Fprint(&s, v)
	}
	s.WriteByte(']')
	return s.String()
}
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
func inspect(id, arch, op, name, first, second, source, objectPath, sourcePath string, b []byte) fixture {
	f := fixture{ID: id, Target: "linux/" + arch, Operation: op, Function: name, First: first, Second: second, SourcePath: sourcePath, ObjectPath: objectPath, SourceSHA256: digest([]byte(source)), ObjectSHA256: digest(b), SourceLength: len(source), ObjectLength: len(b)}
	e, err := elf.NewFile(bytes.NewReader(b))
	fatal(err)
	defer e.Close()
	if e.Class != elf.ELFCLASS64 || e.Data != elf.ELFDATA2LSB || e.Type != elf.ET_REL {
		fatal(fmt.Errorf("%s: unexpected ELF profile", id))
	}
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
		fatal(fmt.Errorf("%s: missing .text", id))
	}
	body, err := t.Data()
	fatal(err)
	f.TextOffset = t.Offset
	f.TextSize = t.Size
	f.BodyHex = hex.EncodeToString(body)
	size := uint64(8)
	machine := uint16(183)
	flags := uint32(0)
	if arch == target.ArchRiscv64 {
		size = 36
		machine = 243
		flags = 4
	}
	if len(e.Sections) != 7 || len(f.Symbols) != 3 || t.Offset != 64 || t.Size != size || f.Machine != machine || f.Flags != flags {
		fatal(fmt.Errorf("%s: production shape drift: sections=%d symbols=%d body=%d machine=%d flags=%d", id, len(e.Sections), len(f.Symbols), t.Size, f.Machine, f.Flags))
	}
	s := f.Symbols[2]
	if s.Name != "oak_"+name || s.Info != 18 || s.Other != 0 || s.Section != 1 || s.Value != 0 || s.Size != size {
		fatal(fmt.Errorf("%s: wrong function symbol: %+v", id, s))
	}
	for _, n := range []string{".rodata", ".rela.text"} {
		if e.Section(n).Size != 0 {
			fatal(fmt.Errorf("%s: nonempty %s", id, n))
		}
	}
	sym := e.Section(".symtab")
	str := e.Section(".strtab")
	shstr := e.Section(".shstrtab")
	// Every image byte belongs to one region. Flip each byte's bits 0..7 for
	// an exhaustive single-bit mutation sweep; descriptors avoid duplicating files.
	f.Regions = []region{{"header", 0, 64}, {"body", 64, int(t.Size)}}
	if sym.Offset > 64+t.Size {
		f.Regions = append(f.Regions, region{"padding", int(64 + t.Size), int(sym.Offset - 64 - t.Size)})
	}
	f.Regions = append(f.Regions, region{"symbols", int(sym.Offset), int(sym.Size)}, region{"name", int(str.Offset), int(str.Size)}, region{"section_names", int(shstr.Offset), int(shstr.Size)})
	if f.SectionHeaderOffset > shstr.Offset+shstr.Size {
		f.Regions = append(f.Regions, region{"padding", int(shstr.Offset + shstr.Size), int(f.SectionHeaderOffset - shstr.Offset - shstr.Size)})
	}
	f.Regions = append(f.Regions, region{"sections", int(f.SectionHeaderOffset), 7 * 64})
	covered := 0
	for _, r := range f.Regions {
		if r.Offset != covered {
			fatal(fmt.Errorf("%s: region gap", id))
		}
		covered += r.Length
	}
	if covered != len(b) {
		fatal(fmt.Errorf("%s: region does not exhaust image", id))
	}
	for i := 0; i < 16; i++ {
		f.Mutations = append(f.Mutations, mutation{Name: fmt.Sprintf("header_ident_%d", i), Family: "header", Kind: "xor_byte", Offset: i, Value: 1})
	}
	f.mutateField(b, "header", "header", 0, headerFields)
	for i := 0; i < 7; i++ {
		f.mutateField(b, "sections", fmt.Sprintf("section_%d", i), int(f.SectionHeaderOffset)+64*i, sectionFields)
	}
	for i := 0; i < 4; i++ {
		f.mutateField(b, "symbols", fmt.Sprintf("symbol_%d", i), int(sym.Offset)+24*i, symbolFields)
	}
	for _, r := range f.Regions {
		if r.Family == "name" || r.Family == "section_names" || r.Family == "padding" || r.Family == "body" {
			for i := r.Offset; i < r.Offset+r.Length; i++ {
				f.Mutations = append(f.Mutations, mutation{Name: fmt.Sprintf("%s_byte_%d", r.Family, i), Family: r.Family, Kind: "xor_byte", Offset: i, Value: 1})
			}
		}
	}
	for _, n := range []int{0, 1, 15, 63, 64, int(64 + t.Size - 1), int(sym.Offset), int(str.Offset), int(shstr.Offset), int(f.SectionHeaderOffset), len(b) - 1} {
		f.Mutations = append(f.Mutations, mutation{Name: fmt.Sprintf("truncate_%d", n), Family: "truncation", Kind: "truncate", Offset: n})
	}
	f.Mutations = append(f.Mutations, mutation{Name: "append_zero", Family: "append", Kind: "append_byte", Offset: len(b), Value: 0}, mutation{Name: "append_one", Family: "append", Kind: "append_byte", Offset: len(b), Value: 1})
	// Multi-byte field cases expose overflows/overlap and false-good body extents.
	f.Mutations = append(f.Mutations,
		mutation{Name: "section_text_offset_overflow", Family: "sections", Kind: "set_le", Offset: int(f.SectionHeaderOffset) + 64 + 24, Width: 8, Value: ^uint64(0)},
		mutation{Name: "section_text_overlap_header", Family: "sections", Kind: "set_le", Offset: int(f.SectionHeaderOffset) + 64 + 24, Width: 8, Value: 0},
		mutation{Name: "symbol_function_undefined", Family: "symbols", Kind: "set_le", Offset: int(sym.Offset) + 72 + 6, Width: 2, Value: 0},
		mutation{Name: "symbol_function_local", Family: "symbols", Kind: "set_le", Offset: int(sym.Offset) + 72 + 4, Width: 1, Value: 2},
		mutation{Name: "symbol_function_short_prefix", Family: "symbols", Kind: "set_le", Offset: int(sym.Offset) + 72 + 16, Width: 8, Value: size - 4},
		mutation{Name: "symbol_function_name_alias_null", Family: "name", Kind: "set_le", Offset: int(sym.Offset) + 72, Width: 4, Value: 0})
	return f
}
func main() {
	out := flag.String("out", "diagnostics/native-object-fixtures", "fixture output directory")
	flag.Parse()
	var fs []fixture
	var lean strings.Builder
	lean.WriteString("/- Generated from complete compiler.EmitNativeObject(asm.ELF) outputs.\n   Data only: not an admission result or a theorem. -/\nnamespace NativeObjectFixtures\n")
	families := []struct{ name, first, second string }{{"bitwise", "x", "y"}, {"Mix9", "left0", "Right9"}}
	for _, arch := range []string{target.ArchArm64, target.ArchRiscv64} {
		for _, family := range families {
			for _, op := range []struct{ name, symbol string }{{"and", "&"}, {"or", "|"}, {"xor", "^"}} {
				id := arch + "_" + family.name + "_" + op.name
				source := fmt.Sprintf("%s: (%s: u32, %s: u32): u32 = %s %s %s\n", family.name, family.first, family.second, family.first, op.symbol, family.second)
				b, err := compiler.New().WithSource(id+".oak", source).WithTarget(target.Target{OS: target.OSLinux, Arch: arch}).EmitNativeObject(asm.ELF).Get()
				fatal(err)
				objectPath := id + ".o"
				sourcePath := id + ".oak"
				f := inspect(id, arch, op.name, family.name, family.first, family.second, source, objectPath, sourcePath, b)
				write(filepath.Join(*out, objectPath), b)
				write(filepath.Join(*out, sourcePath), []byte(source))
				fs = append(fs, f)
				fmt.Fprintf(&lean, "\nnamespace %s\ndef source : List UInt8 := %s\ndef name : List UInt8 := %s\ndef object : List UInt8 := %s\nend %s\n", id, leanBytes([]byte(source)), leanBytes([]byte(family.name)), leanBytes(b), id)
				fmt.Printf("%s: object=%d bytes .text=%d bytes symbol=oak_%s sha256=%s\n", id, len(b), f.TextSize, family.name, f.ObjectSHA256)
			}
		}
	}
	lean.WriteString("\nend NativeObjectFixtures\n")
	write(filepath.Join(*out, "FixtureData.lean"), []byte(lean.String()))
	manifest := struct {
		SchemaVersion    int       `json:"schema_version"`
		Producer         string    `json:"producer"`
		GoVersion        string    `json:"go_version"`
		Scope            string    `json:"scope"`
		MutationProtocol string    `json:"mutation_protocol"`
		Fixtures         []fixture `json:"fixtures"`
	}{1, "compiler.New().WithSource(...).WithTarget(linux/arm64|riscv64).EmitNativeObject(asm.ELF).Get()", runtime.Version(), "Diagnostic complete-object fixtures only; no production authority changed and no Lean proof implied.", "Each explicit mutation is applied independently to its original complete object. set_le writes width little-endian bytes; xor_byte XORs the given value; truncate retains exactly offset bytes; append_byte appends value. For exhaustive bit coverage, flip bits 0..7 at every byte of bit_flip_regions independently. For exhaustive truncation, retain lengths 0 through object_length-1. Cross-operation replay and cross-name replay require retaining the original expected operation/name.", fs}
	b, err := json.MarshalIndent(manifest, "", "  ")
	fatal(err)
	write(filepath.Join(*out, "manifest.json"), append(b, '\n'))
}
