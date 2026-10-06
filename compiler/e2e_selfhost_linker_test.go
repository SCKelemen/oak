package compiler

import (
	"bytes"
	"context"
	"debug/elf"
	"encoding/binary"
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/target"
	"github.com/SCKelemen/oak/toolchain"
)

func TestE2ESelfHostedRelocationKernel(t *testing.T) {
	source, err := os.ReadFile(filepath.Join("..", "asm", "selfhost", "native.oak"))
	if err != nil {
		t.Fatal(err)
	}
	var s strings.Builder
	s.Write(source)
	s.WriteString("\nmain: (): i32 {\n")
	// Independent expected words, including the rounded-high endpoint that
	// the old production linker silently encoded as a negative displacement.
	deltas := []int64{-2147485697, -2147485696, -2147483648, -4097, -4096, -2049, -2048, -1, 0, 1, 2047, 2048, 4095, 4096, 2147481598, 2147481599, 2147481600, 2147483647}
	for _, d := range deltas {
		for _, kind := range []int{4, 5} {
			place := uint64(1) << 33
			target := uint64(int64(place) + d)
			rd := uint32(1)
			op := uint32(0x67)
			if kind == 5 {
				rd = 31
				op = 0x13
			}
			first, second := rd<<7|0x17, rd<<15|rd<<7|op
			accepted := d >= -2147485696 && d <= 2147481599 && (kind == 5 || target&1 == 0)
			fmt.Fprintf(&s, "  true ? {\n    p: NativePatch = native_relocate(u32(%d), u32(%d), u32(%d), u64(%d), u64(%d))\n", kind, first, second, place, target)
			if accepted {
				// Euclidean quotient/remainder via a nonnegative biased displacement.
				biased := uint64(d + 2147485696)
				hi := int64(biased/4096) - 524288
				lo := int64(biased%4096) - 2048
				a := first | uint32(hi&0xfffff)<<12
				b := second | uint32(lo&0xfff)<<20
				fmt.Fprintf(&s, "    assert(p.status == u32(0) && p.first == u32(%d) && p.second == u32(%d))\n", a, b)
			} else {
				s.WriteString("    assert(p.status != u32(0))\n")
			}
			s.WriteString("  }\n")
		}
	}
	rng := rand.New(rand.NewSource(20261006))
	for i := 0; i < 80; i++ {
		delta := int64(rng.Intn(1<<25)-(1<<24)) * 4
		place := uint64(1) << 40
		target := uint64(int64(place) + delta)
		opcode := uint32(0x14000000)
		kind := 1
		if i%2 == 0 {
			opcode = 0x94000000
			kind = 2
		}
		word := opcode | uint32((delta/4)&0x3ffffff)
		fmt.Fprintf(&s, "  true ? { p: NativePatch = native_relocate(u32(%d), u32(%d), u32(0), u64(%d), u64(%d))\n    assert(p.status == u32(0) && p.first == u32(%d)) }\n", kind, opcode, place, target, word)
	}
	s.WriteString(`
  // ADRP+ADD and full-width addresses.
  p: NativePatch = native_relocate(u32(3), u32(0x90000009), u32(0x91000129), u64(65540), u64(68284))
  assert(p.status == u32(0) && p.first == u32(0x90000009) && p.second == u32(0x912af129))
  assert(native_relocate(u32(4), u32(0x97), u32(0x80e7), u64(18446744073709551614), u64(0)).status != u32(0))
  assert(native_relocate(u32(5), u32(0x17), u32(0x13), u64(0), u64(0)).status != u32(0))
  assert(native_relocate(u32(4), u32(0x97), u32(0x8067), u64(0), u64(0)).status != u32(0))
  assert(native_relocate(u32(99), u32(0), u32(0), u64(0), u64(0)).status != u32(0))
  // Patch actual little-endian storage; malformed or truncated input is
  // rejected without writing either word, including a maximal u32 offset.
  bytes: [12]u8 = [u8(0x97), u8(0), u8(0), u8(0), u8(0xe7), u8(0x80), u8(0), u8(0), u8(91), u8(92), u8(93), u8(94)]
  true ? {
    dst: [*]u8 = span(&bytes)
    assert(native_link_patch(dst, u32(0), u32(4), u64(65536), u64(65552)) == u32(0))
    assert(native_read_word(dst, u32(4)) == u32(0x010080e7))
    assert(native_link_patch(dst, u32(0), u32(4), u64(65536), u64(65553)) != u32(0))
    assert(native_read_word(dst, u32(4)) == u32(0x010080e7))
    assert(native_link_patch(dst, u32(8), u32(4), u64(65536), u64(65552)) != u32(0))
    assert(native_link_patch(dst, u32(4294967295), u32(4), u64(65536), u64(65552)) != u32(0))
    assert(native_read_word(dst, u32(8)) == u32(0x5e5d5c5b))
  }
  plan: [2]NativeRelocation = [NativeRelocation { offset: u32(0), kind: u32(4), symbol: u32(0) }, NativeRelocation { offset: u32(8), kind: u32(4), symbol: u32(1) }]
  symbols: [2]u64 = [u64(65600), u64(65552)]
  true ? {
    dst: [*]u8 = span(&bytes)
    assert(native_link_text(dst, view(&plan), view(&symbols), u64(65536)) != u32(0))
    assert(native_read_word(dst, u32(4)) == u32(0x010080e7))
  }
  42
}
`)
	code, abnormal := buildAndRun(t, "selfhost_relocations", s.String())
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// Execute the Oak assembler/linker/image writer, inspect its actual output
// with an independent ELF reader, and execute both images when QEMU exists.
func TestE2ESelfHostedELF(t *testing.T) {
	var core strings.Builder
	for _, name := range []string{"native.oak", "elf.oak"} {
		data, err := os.ReadFile(filepath.Join("..", "asm", "selfhost", name))
		if err != nil {
			t.Fatal(err)
		}
		core.Write(data)
		core.WriteByte('\n')
	}
	for _, arch := range []string{target.ArchArm64, target.ArchRiscv64} {
		t.Run(arch, func(t *testing.T) {
			words := []uint32{0x94000000, 0x52800ba8, 0xd4000001, 0x52800540, 0xd65f03c0}
			archID, kind, mainAt := 1, 2, 12
			asmArch := asm.ArchArm64
			mainBody := "  movz w0, #42\n  ret\n"
			if arch == target.ArchRiscv64 {
				words = []uint32{0x97, 0x80e7, 0x05d00893, 0x73, 0x02a00513, 0x8067}
				archID, kind, mainAt = 2, 4, 16
				asmArch = asm.ArchRV64
				mainBody = "  li a0, 42\n  ret\n"
			}
			var s strings.Builder
			s.WriteString(core.String())
			s.WriteString("putchar: (ch: c.Int): c.Int = c.extern(\"putchar\")\nmain: (): i32 {\n")
			fmt.Fprintf(&s, "  text: [%d]u8\n  image: [%d]u8\n  symbols: [1]u64 = [u64(%d)]\n", len(words)*4, 4096+len(words)*4, 65536+mainAt)
			fmt.Fprintf(&s, "  plan: [1]NativeRelocation = [NativeRelocation { offset: u32(0), kind: u32(%d), symbol: u32(0) }]\n", kind)
			s.WriteString("  true ? { dst: [*]u8 = span(&text)\n")
			for i, w := range words {
				fmt.Fprintf(&s, "    native_write_word(dst, u32(%d), u32(%d))\n", i*4, w)
			}
			s.WriteString("    assert(native_link_text(dst, view(&plan), view(&symbols), u64(65536)) == u32(0))\n  }\n")
			s.WriteString("  size: u32 = 0\n  true ? { dst: [*]u8 = span(&image)\n")
			// Every rejection must leave the caller's bytes alone.
			s.WriteString("    dst[u32(0)] = u8(99)\n")
			fmt.Fprintf(&s, "    assert(native_elf_image(dst, view(&text), u32(%d), u64(65537), u32(0)) == u32(0))\n", archID)
			s.WriteString("    assert(dst[u32(0)] == u8(99))\n")
			fmt.Fprintf(&s, "    size = native_elf_image(dst, view(&text), u32(%d), u64(65536), u32(0))\n  }\n", archID)
			fmt.Fprintf(&s, "  assert(size == u32(%d))\n", 4096+len(words)*4)
			s.WriteString("  i: u32 = 0\n  while i < size { putchar(c.Int(i32_bits_u32(u32(image[i]))))\n    i = i + u32(1) }\n  0\n}\n")
			stdout, code, abnormal := buildAndRunOutput(t, "selfhost_elf", s.String())
			if code != 0 || abnormal {
				t.Fatalf("Oak image generator exit (%d,%v)", code, abnormal)
			}
			image := []byte(stdout)
			file, err := elf.NewFile(bytes.NewReader(image))
			if err != nil {
				t.Fatal(err)
			}
			defer file.Close()
			machine := elf.EM_AARCH64
			if archID == 2 {
				machine = elf.EM_RISCV
			}
			if file.Type != elf.ET_EXEC || file.Machine != machine || file.Entry != 65536 || len(file.Progs) != 1 {
				t.Fatalf("wrong ELF: %+v", file.FileHeader)
			}
			ph := file.Progs[0]
			if ph.Type != elf.PT_LOAD || ph.Flags != elf.PF_R|elf.PF_X || ph.Off != 4096 || ph.Vaddr != 65536 || ph.Filesz != uint64(len(words)*4) || ph.Memsz != ph.Filesz || ph.Align != 4096 {
				t.Fatalf("wrong load segment: %+v", ph.ProgHeader)
			}
			// Bind Oak's linked bytes to the live Go assembler/linker's output.
			unit, errs := asm.ParseUnit("main."+asmArch+".oakasm", "oak_main: () -> i32 = {\n"+mainBody+"}\n")
			if len(errs) != 0 {
				t.Fatal(errs)
			}
			functions, err := asm.EncodeFunctions(unit.Functions, func(s string) string { return s })
			if err != nil {
				t.Fatal(err)
			}
			reference, err := asm.WriteExecutable(functions, asm.ExecutableOptions{OS: asm.OSLinux, Arch: asmArch, Entry: "oak_main"})
			if err != nil {
				t.Fatal(err)
			}
			referenceELF, err := elf.NewFile(bytes.NewReader(reference))
			if err != nil {
				t.Fatal(err)
			}
			defer referenceELF.Close()
			referenceText, err := referenceELF.Section(".text").Data()
			if err != nil {
				t.Fatal(err)
			}
			if !bytes.Equal(image[4096:], referenceText) {
				t.Fatalf("Oak text %x differs from production %x", image[4096:], referenceText)
			}
			if binary.LittleEndian.Uint64(image[24:32]) != ph.Vaddr {
				t.Fatal("entry not bound to loaded bytes")
			}
			emulator, err := toolchain.ResolveEmulator(target.Target{OS: target.OSLinux, Arch: arch}, nil, nil)
			if err != nil {
				if os.Getenv("OAK_REQUIRE_SELFHOST_QEMU") == "1" {
					t.Fatal(err)
				}
				t.Logf("ELF byte checks passed; execution unavailable: %v", err)
				return
			}
			path := filepath.Join(t.TempDir(), "selfhost.elf")
			if err := os.WriteFile(path, image, 0755); err != nil {
				t.Fatal(err)
			}
			ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
			defer cancel()
			cmd := exec.CommandContext(ctx, emulator.Path, append(append([]string{}, emulator.Args...), path)...)
			out, err := cmd.CombinedOutput()
			exit, ok := err.(*exec.ExitError)
			if ctx.Err() != nil || !ok || exit.ExitCode() != 42 {
				t.Fatalf("Oak ELF execution: %v, %v, output %s", err, ctx.Err(), out)
			}
		})
	}
}
