package compiler

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/bitwisecheck"
	"github.com/SCKelemen/oak/target"
)

// This gate tests the untrusted producer only. None of its outputs are checked
// capabilities; the equipped real-kernel test separately admits final images.
func TestCheckedImageProposalProduction(t *testing.T) {
	encoded, err := os.ReadFile("../tools/native_image_fixtures/evidence.json")
	if err != nil {
		t.Fatal(err)
	}
	var pins map[string]struct {
		Length int    `json:"length"`
		SHA256 string `json:"sha256"`
	}
	if err := json.Unmarshal(encoded, &pins); err != nil {
		t.Fatal(err)
	}
	count := 0
	for _, arch := range []string{target.ArchArm64, target.ArchRiscv64} {
		for _, family := range []struct{ id, name, first, second string }{
			{"mix", "mix", "a", "b"}, {"Mix9", "Mix9", "left0", "Right9"},
			{"one", "f", "a", "b"}, {"max256", strings.Repeat("N", 256), "a", "b"},
		} {
			for _, op := range []struct{ name, token string }{{"and", "&"}, {"or", "|"}, {"xor", "^"}} {
				if (family.id == "one" || family.id == "max256") && op.name != "and" {
					continue
				}
				id := arch + "_" + family.id + "_" + op.name
				t.Run(id, func(t *testing.T) {
					source := fmt.Sprintf("%s: (%s: u32, %s: u32): u32 = %s %s %s\n", family.name, family.first, family.second, family.first, op.token, family.second)
					object := checkedImageTestObject(t, source, arch)
					symbol, err := checkedImageProposedSymbol(source)
					if err != nil {
						t.Fatal(err)
					}
					body, err := checkedImageProposeBody(object, symbol, arch)
					if err != nil {
						t.Fatal(err)
					}
					if body.Symbol != "oak_"+family.name || body.Align != 4 || body.Compressed || len(body.Relocs) != 0 {
						t.Fatalf("unexpected proposal: %+v", body)
					}
					image, err := asm.WriteExecutable([]asm.EncodedFunction{body}, asm.ExecutableOptions{OS: asm.OSLinux, Arch: body.Arch, Entry: symbol, RV64FloatABI: "double"})
					if err != nil {
						t.Fatal(err)
					}
					sum := sha256.Sum256(image)
					pin, ok := pins[id]
					if !ok || len(image) != pin.Length || hex.EncodeToString(sum[:]) != pin.SHA256 {
						t.Fatalf("proposal/writer output differs from frozen actual-image correspondence pin %s: %d %x", id, len(image), sum)
					}
					count++
				})
			}
		}
	}
	if count != 16 {
		t.Fatalf("missing complete-image correspondence proposals: got %d, want 16", count)
	}
}

func checkedImageTestObject(t *testing.T, source, arch string) []byte {
	t.Helper()
	object, err := New().WithSource("unchanged.oak", source).
		WithTarget(target.Target{OS: target.OSLinux, Arch: arch}).EmitNativeObject(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	return object
}

func TestCheckedImageProposalRefusesMalformedObjects(t *testing.T) {
	for _, arch := range []string{target.ArchArm64, target.ArchRiscv64} {
		t.Run(arch, func(t *testing.T) {
			object := checkedImageTestObject(t, "bitwise: (x: u32, y: u32): u32 = x & y\n", arch)
			le := binary.LittleEndian
			shoff := int(le.Uint64(object[40:48]))
			symoff := int(le.Uint64(object[shoff+4*64+24 : shoff+4*64+32]))
			strOff := int(le.Uint64(object[shoff+5*64+24 : shoff+5*64+32]))
			controls := []struct {
				name   string
				mutate func([]byte) []byte
			}{
				{"trailing", func(b []byte) []byte { return append(b, 0) }},
				{"oversized", func(b []byte) []byte { return append(b, make([]byte, bitwisecheck.MaxObjectBytes)...) }},
				{"symbol_name", func(b []byte) []byte { b[strOff+1] ^= 1; return b }},
				{"duplicate_function", func(b []byte) []byte { copy(b[symoff+2*24:symoff+3*24], b[symoff+3*24:symoff+4*24]); return b }},
			}
			for _, field := range []struct {
				name       string
				off, width int
				value      uint64
			}{
				{"magic", 0, 1, 0}, {"class", 4, 1, 1}, {"endianness", 5, 1, 2}, {"ident_version", 6, 1, 0}, {"osabi", 7, 1, 3},
				{"type", 16, 2, 2}, {"machine", 18, 2, 0}, {"version", 20, 4, 2}, {"entry", 24, 8, 1}, {"program_offset", 32, 8, 64},
				{"section_offset_overflow", 40, 8, ^uint64(0)}, {"section_offset_header", 40, 8, 0}, {"flags", 48, 4, 1},
				{"header_size", 52, 2, 0}, {"program_entry_size", 54, 2, 56}, {"program_count", 56, 2, 1},
				{"section_entry_size", 58, 2, 0}, {"section_count", 60, 2, 65535}, {"section_names", 62, 2, 0},
				{"text_type", shoff + 64 + 4, 4, 8}, {"text_compressed", shoff + 64 + 8, 8, 0x806}, {"text_writable", shoff + 64 + 8, 8, 7},
				{"text_address", shoff + 64 + 16, 8, 1}, {"text_offset_overflow", shoff + 64 + 24, 8, ^uint64(0)},
				{"text_offset_header", shoff + 64 + 24, 8, 0}, {"text_size_overflow", shoff + 64 + 32, 8, ^uint64(0)},
				{"text_alignment", shoff + 64 + 48, 8, 2}, {"text_entry_size", shoff + 64 + 56, 8, 4},
				{"data_nonempty", shoff + 2*64 + 32, 8, 1}, {"body_relocation", shoff + 3*64 + 32, 8, 24},
				{"relocation_owner", shoff + 3*64 + 44, 4, 2}, {"symbol_compressed", shoff + 4*64 + 8, 8, 0x800},
				{"symbol_table_size", shoff + 4*64 + 32, 8, 72}, {"symbol_string_link", shoff + 4*64 + 40, 4, 6},
				{"string_compressed", shoff + 5*64 + 8, 8, 0x800}, {"string_offset_overlap", shoff + 5*64 + 24, 8, 64},
				{"string_size_overflow", shoff + 5*64 + 32, 8, ^uint64(0)}, {"name_table_compressed", shoff + 6*64 + 8, 8, 0x800},
				{"function_name_bounds", symoff + 3*24, 4, ^uint64(0)}, {"function_missing", symoff + 3*24, 4, 0},
				{"function_local", symoff + 3*24 + 4, 1, 2}, {"function_hidden", symoff + 3*24 + 5, 1, 2},
				{"function_undefined", symoff + 3*24 + 6, 2, 0}, {"function_data_owner", symoff + 3*24 + 6, 2, 2},
				{"function_owner_bounds", symoff + 3*24 + 6, 2, 65535}, {"function_extent_shift", symoff + 3*24 + 8, 8, 4},
				{"function_extent_overflow", symoff + 3*24 + 8, 8, ^uint64(0)}, {"function_size_zero", symoff + 3*24 + 16, 8, 0},
				{"function_size_overflow", symoff + 3*24 + 16, 8, ^uint64(0)},
			} {
				controls = append(controls, struct {
					name   string
					mutate func([]byte) []byte
				}{field.name, func(b []byte) []byte {
					for j := 0; j < field.width; j++ {
						b[field.off+j] = byte(field.value >> (8 * j))
					}
					return b
				}})
			}
			for _, control := range controls {
				t.Run(control.name, func(t *testing.T) {
					changed := control.mutate(append([]byte(nil), object...))
					body, err := checkedImageProposeBody(changed, "oak_bitwise", arch)
					if err == nil || len(body.Bytes) != 0 {
						t.Fatalf("malformed intermediate object proposed a body: %+v, %v", body, err)
					}
				})
			}
			t.Run("every_truncation", func(t *testing.T) {
				for i := 0; i < len(object); i++ {
					if _, err := checkedImageProposeBody(object[:i], "oak_bitwise", arch); err == nil {
						t.Fatalf("accepted truncation at %d", i)
					}
				}
			})
			t.Run("wrong_target", func(t *testing.T) {
				other := target.ArchArm64
				if arch == other {
					other = target.ArchRiscv64
				}
				if _, err := checkedImageProposeBody(object, "oak_bitwise", other); err == nil {
					t.Fatal("accepted another target's object")
				}
				if _, err := checkedImageProposeBody(object, "oak_bitwise", "not-an-arch"); err == nil {
					t.Fatal("accepted unsupported target")
				}
			})
		})
	}
}

func TestCheckedImageProposalOwnsCopyWithoutClaimingBodyAuthority(t *testing.T) {
	for _, arch := range []string{target.ArchArm64, target.ArchRiscv64} {
		object := checkedImageTestObject(t, "bitwise: (x: u32, y: u32): u32 = x & y\n", arch)
		body, err := checkedImageProposeBody(object, "oak_bitwise", arch)
		if err != nil {
			t.Fatal(err)
		}
		original := append([]byte(nil), body.Bytes...)
		object[64] ^= 1
		if !bytes.Equal(body.Bytes, original) {
			t.Fatal("proposal aliases mutable object input")
		}
		changed, err := checkedImageProposeBody(object, "oak_bitwise", arch)
		if err != nil || bytes.Equal(changed.Bytes, original) {
			t.Fatalf("producer must pass actual changed body to the independent checker: %v", err)
		}
		body.Bytes[0] ^= 2
		if object[64] == body.Bytes[0] {
			t.Fatal("mutating proposed body changed its original object")
		}
	}
}

func TestCheckedImageProposedSymbolBoundaries(t *testing.T) {
	for _, name := range []string{"a", "Mix9", strings.Repeat("N", 256)} {
		got, err := checkedImageProposedSymbol(name + ": (x: u32, y: u32): u32 = x & y\n")
		if err != nil || got != "oak_"+name {
			t.Fatalf("valid name %q: %q %v", name, got, err)
		}
	}
	for _, source := range []string{"", ":", "missing", "3x:", "two names:", "\xef\xbb\xbfx:", "na\x00me:", strings.Repeat("N", 257) + ":"} {
		if _, err := checkedImageProposedSymbol(source); err == nil {
			t.Fatalf("accepted invalid initial name in %q", source)
		}
	}
}
