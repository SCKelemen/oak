package compiler

import (
	"bytes"
	"crypto/sha256"
	"debug/elf"
	"encoding/binary"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/target"
)

// Shared by the cheap interface preflight and every generated load pin.
const rv64ImageLeanState = "OakSailBridge.BitwiseDecoded.State"

// rv64ImageLeanBytes preserves the complete artifact, including padding,
// symbols, and section headers. Only runs of zero bytes are compressed.
func rv64ImageLeanBytes(data []byte) string {
	var chunks []string
	for len(data) != 0 {
		n := 0
		for n < len(data) && data[n] == 0 {
			n++
		}
		if n >= 8 {
			chunks = append(chunks, fmt.Sprintf("List.replicate %d 0", n))
			data = data[n:]
			continue
		}
		end := 1
		for end < len(data) {
			run := 0
			for end+run < len(data) && data[end+run] == 0 {
				run++
			}
			if run >= 8 {
				break
			}
			if run == 0 {
				end++
			} else {
				end += run
			}
		}
		values := make([]string, end)
		for i, b := range data[:end] {
			values[i] = fmt.Sprint(b)
		}
		chunks = append(chunks, "["+strings.Join(values, ",")+"]")
		data = data[end:]
	}
	if len(chunks) == 0 {
		return "[]"
	}
	return "(" + strings.Join(chunks, " ++ ") + ")"
}

type rv64BitwiseImage struct {
	source            string
	image, code       []byte
	address, fileBody uint64
	segment           elf.ProgHeader
}

// The restricted grammar accepts exactly the original declaration. Appending
// main merely to call EmitExecutable would break that source identity. Instead
// compile the exact source to ET_REL, reject relocations in its complete body,
// and pass those production bytes to the production ET_EXEC writer. Its _start
// and all nonloaded metadata remain in the file; no startup execution is claimed.
func compileRV64BitwiseImage(t *testing.T, operator string) rv64BitwiseImage {
	t.Helper()
	source := fmt.Sprintf("mix: (a: u32, b: u32): u32 = a %s b\n", operator)
	out, err := New().WithSource("image_bitwise.oak", source).
		WithTarget(target.Target{OS: target.OSLinux, Arch: target.ArchRiscv64}).
		WithNativeBodies().EmitNative(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	object, err := elf.NewFile(bytes.NewReader(out.Object))
	if err != nil {
		t.Fatal(err)
	}
	defer object.Close()
	if object.Machine != elf.EM_RISCV || object.Class != elf.ELFCLASS64 || object.Data != elf.ELFDATA2LSB || object.Type != elf.ET_REL {
		t.Fatalf("wrong production object: %+v", object.FileHeader)
	}
	if binary.LittleEndian.Uint32(out.Object[48:52]) != 4 {
		t.Fatal("expected the uncompressed LP64D object profile")
	}
	syms, err := object.Symbols()
	if err != nil {
		t.Fatal(err)
	}
	var code []byte
	found := false
	for _, symbol := range syms {
		if symbol.Name != "oak_mix" {
			continue
		}
		if found || elf.ST_TYPE(symbol.Info) != elf.STT_FUNC || symbol.Section == elf.SHN_UNDEF || int(symbol.Section) >= len(object.Sections) {
			t.Fatalf("invalid/duplicate oak_mix symbol: %+v", symbol)
		}
		found = true
		sectionHeader := object.Sections[symbol.Section]
		if sectionHeader.Type != elf.SHT_PROGBITS || sectionHeader.Flags&(elf.SHF_ALLOC|elf.SHF_EXECINSTR) != elf.SHF_ALLOC|elf.SHF_EXECINSTR {
			t.Fatal("production oak_mix is not executable allocated code")
		}
		section, err := sectionHeader.Data()
		if err != nil {
			t.Fatal(err)
		}
		if symbol.Value > uint64(len(section)) || symbol.Size > uint64(len(section))-symbol.Value {
			t.Fatal("production symbol extent exceeds its section")
		}
		code = append([]byte(nil), section[symbol.Value:symbol.Value+symbol.Size]...)
		for _, relocations := range object.Sections {
			if relocations.Info != uint32(symbol.Section) || (relocations.Type != elf.SHT_RELA && relocations.Type != elf.SHT_REL) {
				continue
			}
			if relocations.Type != elf.SHT_RELA {
				t.Fatal("unexpected non-RELA relocation section for oak_mix")
			}
			data, err := relocations.Data()
			if err != nil {
				t.Fatal(err)
			}
			if len(data)%24 != 0 {
				t.Fatal("invalid ELF64 relocation extent")
			}
			for at := 0; at < len(data); at += 24 {
				offset := binary.LittleEndian.Uint64(data[at : at+8])
				if offset >= symbol.Value && offset-symbol.Value < symbol.Size {
					t.Fatal("complete oak_mix contains an unresolved relocation")
				}
			}
		}
	}
	if !found || len(code) != 36 {
		t.Fatalf("complete oak_mix is %d bytes; expected the 36-byte framed profile", len(code))
	}
	image, err := asm.WriteExecutable([]asm.EncodedFunction{{Symbol: "oak_mix", Bytes: code, Align: 4, Arch: asm.ArchRV64}},
		asm.ExecutableOptions{OS: asm.OSLinux, Arch: asm.ArchRV64, Entry: "oak_mix", RV64FloatABI: "double"})
	if err != nil {
		t.Fatal(err)
	}
	executable, err := elf.NewFile(bytes.NewReader(image))
	if err != nil {
		t.Fatal(err)
	}
	defer executable.Close()
	if executable.Machine != elf.EM_RISCV || executable.Class != elf.ELFCLASS64 || executable.Data != elf.ELFDATA2LSB || executable.Type != elf.ET_EXEC {
		t.Fatalf("wrong production executable: %+v", executable.FileHeader)
	}
	if binary.LittleEndian.Uint32(image[48:52]) != 4 || len(executable.Progs) != 1 {
		t.Fatal("expected one uncompressed LP64D load segment")
	}
	p := executable.Progs[0].ProgHeader
	if p.Type != elf.PT_LOAD || p.Flags != elf.PF_R|elf.PF_X || p.Align != 4096 || p.Filesz == 0 || p.Memsz != p.Filesz || p.Vaddr != executable.Entry {
		t.Fatalf("unexpected production PT_LOAD: %+v", p)
	}
	if p.Off > uint64(len(image)) || p.Filesz > uint64(len(image))-p.Off || p.Vaddr > ^uint64(0)-p.Memsz {
		t.Fatal("production PT_LOAD overflows its file/address extent")
	}
	// Require the whole emitted file rather than silently slicing at PT_LOAD.
	if p.Off+p.Filesz >= uint64(len(image)) || executable.Section(".symtab") == nil || executable.Section(".shstrtab") == nil {
		t.Fatal("complete executable metadata is missing")
	}
	syms, err = executable.Symbols()
	if err != nil {
		t.Fatal(err)
	}
	found = false
	var address, fileBody uint64
	for _, symbol := range syms {
		if symbol.Name != "oak_mix" {
			continue
		}
		if found || elf.ST_TYPE(symbol.Info) != elf.STT_FUNC || symbol.Size != uint64(len(code)) || symbol.Section == elf.SHN_UNDEF || int(symbol.Section) >= len(executable.Sections) {
			t.Fatalf("invalid/duplicate executable oak_mix: %+v", symbol)
		}
		found = true
		address = symbol.Value
		if address < p.Vaddr || address-p.Vaddr > p.Filesz || symbol.Size > p.Filesz-(address-p.Vaddr) {
			t.Fatal("oak_mix is not wholly file-backed by PT_LOAD")
		}
		fileBody = p.Off + (address - p.Vaddr)
		if !bytes.Equal(image[fileBody:fileBody+symbol.Size], code) {
			t.Fatal("PT_LOAD oak_mix bytes differ from the production object")
		}
	}
	if !found {
		t.Fatal("oak_mix is absent from the production executable")
	}
	t.Logf("source %q -> ET_REL oak_mix %x -> complete ET_EXEC %d bytes, PT_LOAD file=%#x address=%#x size=%d, oak_mix file=%#x address=%#x", source, code, len(image), p.Off, p.Vaddr, p.Filesz, fileBody, address)
	return rv64BitwiseImage{source: source, image: image, code: code, address: address, fileBody: fileBody, segment: p}
}

// Pins the actual restricted original source, all 36 production function bytes,
// its actual load address, and every byte of the complete production executable
// to the same-kernel image-placement/source-clocked theorem's admission premise.
// This does not prove the Go compiler, a host ELF loader, or execution of _start.
func TestRV64ImageBitwiseCompilerMatchesLean(t *testing.T) {
	var claims []string
	for _, tc := range []struct{ name, operator string }{{"and", "&"}, {"or", "|"}, {"xor", "^"}} {
		a := compileRV64BitwiseImage(t, tc.operator)
		name := "image_" + tc.name
		source := "source_" + tc.name
		claim := "claim_" + tc.name
		claims = append(claims,
			fmt.Sprintf("def %s : List UInt8 := %s", source, rv64ImageLeanBytes([]byte(a.source))),
			fmt.Sprintf("def %s : Oak.BitwiseSource.Decl := ⟨[109,105,120], [97], [98], .%s⟩", claim, tc.name),
			fmt.Sprintf("def %s : Oak.MinimalELF.Bytes := %s", name, rv64ImageLeanBytes(a.image)),
			fmt.Sprintf("example : %s.length = %d := by decide +kernel", name, len(a.image)),
			fmt.Sprintf("example : Oak.RiscVFramedBitwise.functionBytes .%s = %s := by rfl", tc.name, rv64ImageLeanBytes(a.code)),
			fmt.Sprintf("theorem accepted_%s : accepts %s %s %s %d 69632 = true := by decide +kernel", tc.name, source, claim, name, a.address),
			fmt.Sprintf("noncomputable def compiler_image_%s := OakSailImageChecks.initialized_image_clocked_prefix accepted_%s", tc.name, tc.name),
			fmt.Sprintf("noncomputable def compiler_load_%s (s : %s) := OakSailImageSource.accepted_load s accepted_%s", tc.name, rv64ImageLeanState, tc.name))
		// Exact contact is disjoint: either the stack ends where the loaded
		// segment begins, or its reserved frame starts where that segment ends.
		for _, sp := range []uint64{96, a.segment.Vaddr, a.segment.Vaddr + a.segment.Filesz + 96} {
			claims = append(claims, fmt.Sprintf("example : accepts %s %s %s %d %d = true := by decide +kernel", source, claim, name, a.address, sp))
		}
		reject := func(label, src, decl, image, address, sp string) {
			claims = append(claims, "-- Reject "+tc.name+": "+label,
				fmt.Sprintf("example : accepts %s %s %s %s %s = false := by decide +kernel", src, decl, image, address, sp))
		}
		address := fmt.Sprint(a.address)
		for _, bad := range []uint64{a.address + 1, a.segment.Vaddr - 4, a.address + 4, a.segment.Vaddr + a.segment.Filesz, ^uint64(0) - 3} {
			reject("wrong function address", source, claim, name, fmt.Sprint(bad), "69632")
		}
		reject("address outside u64", source, claim, name, "18446744073709551616", "69632")
		wrong := "or"
		wrongOperator := "|"
		if tc.name == "or" {
			wrong, wrongOperator = "and", "&"
		}
		reject("changed claim", source, "claim_"+wrong, name, address, "69632")
		reject("changed source operator", rv64ImageLeanBytes([]byte(strings.Replace(a.source, " "+tc.operator+" ", " "+wrongOperator+" ", 1))), claim, name, address, "69632")
		reject("changed source type", rv64ImageLeanBytes([]byte(strings.ReplaceAll(a.source, "u32", "u64"))), claim, name, address, "69632")
		reject("extra source declaration", rv64ImageLeanBytes([]byte(a.source+"main: (): i32 = 0\n")), claim, name, address, "69632")
		if tc.name != "and" {
			continue
		}
		// Use explicit changed bytes of the original complete file, not an
		// independent image fixture or a second Go acceptance implementation.
		changedImage := func(label string, bad []byte, badAddress uint64) {
			if len(bad) != len(a.image) {
				t.Fatalf("changed image %s has a different whole-file extent", label)
			}
			expression := name
			changed := false
			for i, b := range bad {
				if b != a.image[i] {
					expression = fmt.Sprintf("(%s.set %d %d)", expression, i, b)
					changed = true
				}
			}
			if !changed {
				t.Fatalf("vacuous adversarial case: %s", label)
			}
			reject(label, source, claim, expression, fmt.Sprint(badAddress), "69632")
		}
		mutate := func(label string, change func([]byte)) {
			bad := append([]byte(nil), a.image...)
			change(bad)
			changedImage(label, bad, a.address)
		}
		// Keep the compiler body unchanged and use the actual production
		// writer at another valid ELF base. Admission rejects only the low-RAM
		// execution profile, not a malformed ELF or wrong body offset.
		highImage, err := asm.WriteExecutable([]asm.EncodedFunction{{Symbol: "oak_mix", Bytes: a.code, Align: 4, Arch: asm.ArchRV64}},
			asm.ExecutableOptions{OS: asm.OSLinux, Arch: asm.ArchRV64, Entry: "oak_mix", RV64FloatABI: "double", Base: 0x02000000})
		if err != nil {
			t.Fatal(err)
		}
		changedImage("production image outside low RAM", highImage, 0x02000000+(a.address-a.segment.Vaddr))
		for _, field := range []struct {
			name   string
			offset int
		}{
			{"ELF magic", 0}, {"ELF class", 4}, {"endianness", 5},
			{"ET_EXEC", 16}, {"RV64 machine", 18}, {"ELF version", 20},
			{"entry address", 24}, {"program-header offset", 32},
			{"LP64D flags", 48}, {"ELF-header size", 52},
			{"program-header size", 54}, {"PT_LOAD type", 64},
			{"segment alignment", 112},
		} {
			mutate(field.name, func(b []byte) { b[field.offset] ^= 0xff })
		}
		for _, flags := range []uint32{0, 1, 5} {
			mutate(fmt.Sprintf("wrong/compressed RV64 ABI flags %d", flags), func(b []byte) { binary.LittleEndian.PutUint32(b[48:52], flags) })
		}
		for _, flags := range []uint32{0, 1, 4, 6, 7} {
			mutate(fmt.Sprintf("non-RX permissions %d", flags), func(b []byte) { binary.LittleEndian.PutUint32(b[68:72], flags) })
		}
		for _, off := range []uint64{0, a.segment.Off + 1, a.segment.Off + 4096, ^uint64(0)} {
			mutate(fmt.Sprintf("invalid segment file offset %d", off), func(b []byte) { binary.LittleEndian.PutUint64(b[72:80], off) })
		}
		mutate("two overlapping PT_LOAD entries", func(b []byte) {
			copy(b[120:176], b[64:120])
			binary.LittleEndian.PutUint16(b[56:58], 2)
		})
		mutate("zero-size segment", func(b []byte) {
			binary.LittleEndian.PutUint64(b[96:104], 0)
			binary.LittleEndian.PutUint64(b[104:112], 0)
		})
		mutate("file size exceeds complete image", func(b []byte) { binary.LittleEndian.PutUint64(b[96:104], ^uint64(0)) })
		mutate("zero-fill tail", func(b []byte) { binary.LittleEndian.PutUint64(b[104:112], a.segment.Memsz+4) })
		mutate("wrapping u64 segment", func(b []byte) {
			base := ^uint64(0) - 4095
			binary.LittleEndian.PutUint64(b[24:32], base)
			binary.LittleEndian.PutUint64(b[80:88], base)
			binary.LittleEndian.PutUint64(b[96:104], 4096)
			binary.LittleEndian.PutUint64(b[104:112], 4096)
		})
		// Isolate the strict u64 extent guard in the underlying ELF checker.
		// Padding retains every original byte and makes the entire 4096-byte
		// segment file-backed; all other header/layout conditions hold.
		padded := append(append([]byte(nil), a.image...), make([]byte, 8192-len(a.image))...)
		topPage := ^uint64(0) - 4095
		for _, offset := range []int{24, 80, 88} {
			binary.LittleEndian.PutUint64(padded[offset:offset+8], topPage)
		}
		for _, offset := range []int{96, 104} {
			binary.LittleEndian.PutUint64(padded[offset:offset+8], 4096)
		}
		wrapping := fmt.Sprintf("(%s ++ List.replicate %d 0)", name, len(padded)-len(a.image))
		for i, b := range padded[:len(a.image)] {
			if b != a.image[i] {
				wrapping = fmt.Sprintf("(%s.set %d %d)", wrapping, i, b)
			}
		}
		claims = append(claims,
			"def image_wrapping : Oak.MinimalELF.Bytes := "+wrapping,
			"example : Oak.MinimalELF.Header .rv64 image_wrapping := by decide +kernel",
			"example : let p := Oak.MinimalELF.segment image_wrapping; p.flags = 5 ∧ p.alignment = 4096 ∧ 120 ≤ p.fileOffset ∧ p.fileOffset % 4096 = p.vaddr % 4096 ∧ p.vaddr % 4096 = 0 ∧ 0 < p.fileSize ∧ p.memorySize = p.fileSize ∧ p.fileOffset + p.fileSize ≤ image_wrapping.length ∧ p.entry = p.vaddr ∧ p.vaddr + p.memorySize = 2^64 := by decide +kernel",
			"example : Oak.MinimalELF.admitted .rv64 image_wrapping = false := by decide +kernel")
		mutate("changed function instruction", func(b []byte) { b[a.fileBody+16] ^= 0x10 })
		for _, size := range []uint64{119, a.fileBody + uint64(len(a.code)) - 1, a.segment.Off + a.segment.Filesz - 1} {
			reject("truncated file", source, claim, fmt.Sprintf("(%s.take %d)", name, size), address, "69632")
		}
		// The entire loaded segment must avoid the entire reserved stack
		// frame, even when only _start overlaps and oak_mix itself does not.
		for _, sp := range []uint64{0, 80, 69633, a.address, a.segment.Vaddr + 96, 0x02000010} {
			reject("invalid or image-overlapping stack", source, claim, name, address, fmt.Sprint(sp))
		}
	}
	// claim_or is also used by the AND adversary; keep declarations before
	// all assertions so cross-operation source/claim mismatches are checked.
	var declarations, assertions []string
	claimCount := 0
	for _, line := range claims {
		if strings.HasPrefix(line, "def ") {
			declarations = append(declarations, line)
		} else {
			assertions = append(assertions, line)
			if !strings.HasPrefix(line, "--") {
				claimCount++
			}
		}
	}
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_RV64_LEAN") != "" {
			t.Fatal("lake required for RV64 image compiler correspondence")
		}
		t.Skip("lake unavailable; complete production ELF structural checks passed")
	}
	export := filepath.Join("..", "external", "sail-riscv", "build", "model", "Lean_RV64D", "LeanRV64D", "Fetch.lean")
	if _, err := os.Stat(export); err != nil {
		if !os.IsNotExist(err) || os.Getenv("OAK_REQUIRE_RV64_LEAN") != "" {
			t.Fatalf("pinned RV64 fetch export required: %v", err)
		}
		t.Skip("optional pinned RV64 Sail export unavailable; complete production ELF structural checks passed")
	}
	root := filepath.Join("..", "spec", "lean-sail429")
	build := exec.Command(lake, "build", "OakSailImageChecks")
	build.Dir = root
	if output, err := build.CombinedOutput(); err != nil {
		t.Fatalf("image model build: %v\n%s", err, output)
	}
	pins := "import OakSailImageChecks\nopen OakSailImageSource\nset_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\n" +
		strings.Join(declarations, "\n") + "\n" + strings.Join(assertions, "\n") + "\n"
	t.Logf("%d-claim certificate SHA-256: %x", claimCount, sha256.Sum256([]byte(pins)))
	// Optional reproducibility capture also works with the interfaces-only
	// filter; it records the exact certificate without claiming to check it.
	if path := os.Getenv("OAK_RV64_IMAGE_PINS_OUTPUT"); path != "" {
		if err := os.WriteFile(path, []byte(pins), 0600); err != nil {
			t.Fatal(err)
		}
	}
	// Run with -run '^TestRV64ImageBitwiseCompilerMatchesLean$/^interfaces$'
	// to check imports and both exact theorem applications without evaluating
	// any complete-image admission. The same State alias is used in the pins.
	if !t.Run("interfaces", func(t *testing.T) {
		preflight := fmt.Sprintf(`import OakSailImageChecks
open OakSailImageSource
namespace ImagePinPreflight
variable {source : List UInt8} {claim : Oak.BitwiseSource.Decl}
  {image : Oak.MinimalELF.Bytes} {address sp : Nat}
noncomputable def execution
    (accepted : accepts source claim image address sp = true) :=
  OakSailImageChecks.initialized_image_clocked_prefix accepted
noncomputable def loading (s : %s)
    (accepted : accepts source claim image address sp = true) :=
  OakSailImageSource.accepted_load s accepted
end ImagePinPreflight
`, rv64ImageLeanState)
		path := filepath.Join(t.TempDir(), "RV64ImageInterfaces.lean")
		if err := os.WriteFile(path, []byte(preflight), 0600); err != nil {
			t.Fatal(err)
		}
		cmd := exec.Command(lake, "env", "lean", path)
		cmd.Dir = root
		if output, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("image theorem interface preflight: %v\n%s", err, output)
		}
	}) {
		return
	}
	t.Run("pins", func(t *testing.T) {
		path := filepath.Join(t.TempDir(), "RV64ImageBitwisePins.lean")
		if err := os.WriteFile(path, []byte(pins), 0600); err != nil {
			t.Fatal(err)
		}
		cmd := exec.Command(lake, "env", "lean", "--tstack=400000", path)
		cmd.Dir = root
		if output, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("complete image/source Lean pins: %v\n%s", err, output)
		}
		t.Logf("checked %d exact complete-image/source and adversarial claims", claimCount)
	})
}
