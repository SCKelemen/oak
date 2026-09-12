package asm

import (
	"bufio"
	"bytes"
	"context"
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
	"time"
)

// The RV64 differential oracle (docs/spec/94-assembler.md §9): the
// verifier's term semantics against the machine. Each unit is encoded by
// the Oak assembler into an ELF object, linked by the GNU toolchain into
// a bare-metal image with a C harness that calls it on chosen inputs and
// prints the results over the virt machine's UART, and run under
// qemu-system-riscv64. The expected values come from the verifier's
// concrete execution of the same unit — so an instruction whose term
// semantics disagree with the ISA shows up as a differing line. Skips
// without riscv64-elf-gcc and qemu-system-riscv64.

type rv64Oracle struct {
	decl, body string
	cType      string // the C type of every parameter and the result
	width      int
	inputs     [][2]uint64
}

func TestRV64QEMUDifferential(t *testing.T) {
	requireRV64Tools(t, "riscv64-elf-gcc", "qemu-system-riscv64")
	rng := rand.New(rand.NewSource(0x5f3759df))
	edge64 := []uint64{0, 1, 2, 0xffffffffffffffff, 0x8000000000000000, 0x7fffffffffffffff, 0x100000000, 0xffffffff}
	edge32 := []uint64{0, 1, 0xffffffff, 0x80000000, 0x7fffffff, 3, 0x12345678}
	pairs := func(edges []uint64, mask uint64) [][2]uint64 {
		var out [][2]uint64
		for i := 0; i < 6; i++ {
			out = append(out, [2]uint64{edges[i%len(edges)], edges[(i*3+1)%len(edges)]})
		}
		for i := 0; i < 10; i++ {
			out = append(out, [2]uint64{rng.Uint64() & mask, rng.Uint64() & mask})
		}
		return out
	}
	oracles := []rv64Oracle{
		{decl: "dmix: (a, b: u64) -> u64", cType: "unsigned long long", width: 64, inputs: pairs(edge64, ^uint64(0)), body: `
  bind a0 = a
  bind a1 = b
  clobber t0, t1, t2
  frame 32
  addi sp, sp, -32
  sd s0, 24(sp)
  mul t0, a0, a1
  mulhu t1, a0, a1
  xor t0, t0, t1
  divu t1, a0, a1
  remu t2, a1, a0
  add t0, t0, t1
  sub t0, t0, t2
  sltu t1, a0, a1
  slli t1, t1, 7
  or t0, t0, t1
  srli t1, a0, 3
  sll t2, a1, a0
  xor t0, t0, t1
  add t0, t0, t2
  mv s0, t0
  sd s0, 8(sp)
  ld t1, 8(sp)
  bltu a0, a1, low
  addi t1, t1, 17
low:
  add a0, t1, s0
  ld s0, 24(sp)
  addi sp, sp, 32
  ret`},
		{decl: "wmix: (a, b: u32) -> u32", cType: "unsigned int", width: 32, inputs: pairs(edge32, 0xffffffff), body: `
  bind a0 = a
  bind a1 = b
  clobber t0, t1, t2
  addw t0, a0, a1
  subw t1, a0, a1
  xor t0, t0, t1
  mulw t1, a0, a1
  add t0, t0, t1
  sllw t1, a0, a1
  srlw t2, a1, a0
  xor t0, t0, t1
  add t0, t0, t2
  sraiw t1, a0, 5
  xor t0, t0, t1
  divuw t1, a0, a1
  remuw t2, a0, a1
  add t0, t0, t1
  xor t0, t0, t2
  li t1, 305419896
  add t0, t0, t1
  bne a0, a1, skip
  not t0, t0
skip:
  sext.w a0, t0
  ret`},
		{decl: "smix: (a, b: i64) -> i64", cType: "long long", width: 64, inputs: pairs(edge64, ^uint64(0)), body: `
  bind a0 = a
  bind a1 = b
  clobber t0, t1, t2
  sra t0, a0, a1
  mulh t1, a0, a1
  xor t0, t0, t1
  div t1, a0, a1
  rem t2, a0, a1
  add t0, t0, t1
  xor t0, t0, t2
  slt t1, a0, a1
  neg t1, t1
  xor t0, t0, t1
  srai t1, a1, 63
  add t0, t0, t1
  bge a0, a1, keep
  sub t0, t0, a1
keep:
  blt a0, zero, done
  addi t0, t0, -5
done:
  mv a0, t0
  ret`},
		{decl: "wsig: (a, b: i32) -> i32", cType: "int", width: 32, inputs: pairs(edge32, 0xffffffff), body: `
  bind a0 = a
  bind a1 = b
  clobber t0, t1
  sraw t0, a0, a1
  divw t1, a0, a1
  xor t0, t0, t1
  remw t1, a0, a1
  add t0, t0, t1
  slt t1, a0, a1
  addw t0, t0, t1
  bgez a0, pos
  negw t0, t0
pos:
  mv a0, t0
  ret`},
	}

	var functions []*Function
	var harness strings.Builder
	harness.WriteString("typedef unsigned long long u64;\n")
	harness.WriteString("static void putc_(char c) { *(volatile unsigned char *)0x10000000 = c; }\n")
	harness.WriteString("static void puthex(u64 v) { for (int i = 60; i >= 0; i -= 4) putc_(\"0123456789abcdef\"[(v >> i) & 15]); putc_('\\n'); }\n")
	var expected []string
	for _, oracle := range oracles {
		fn, errs := rv64Unit(t, oracle.decl, oracle.body)
		if len(errs) != 0 {
			t.Fatalf("%s: %v", oracle.decl, errs)
		}
		sig, err := parseSignature(oracle.decl)
		if err != nil {
			t.Fatal(err)
		}
		if findings := Check(fn, sig, nil); len(findings) != 0 {
			t.Fatalf("%s: checker %v", fn.Name, findings)
		}
		functions = append(functions, fn)
		fmt.Fprintf(&harness, "extern %s %s(%s, %s);\n", oracle.cType, fn.Name, oracle.cType, oracle.cType)
		for _, in := range oracle.inputs {
			a, b := in[0]&mask(oracle.width), in[1]&mask(oracle.width)
			result, _, reason, ok := executeBody(fn, sig, map[string]uint64{"a": a, "b": b})
			if !ok {
				t.Fatalf("%s: verifier: %s", fn.Name, reason)
			}
			expected = append(expected, fmt.Sprintf("%016x", result.eval(map[string]uint64{"a": a, "b": b})&mask(oracle.width)))
		}
	}
	harness.WriteString("void cmain(void) {\n")
	for _, oracle := range oracles {
		name := strings.SplitN(oracle.decl, ":", 2)[0]
		for _, in := range oracle.inputs {
			a, b := in[0]&mask(oracle.width), in[1]&mask(oracle.width)
			// The result is printed at its contract width: a signed narrow
			// result would otherwise sign-extend through the C cast.
			fmt.Fprintf(&harness, "  puthex((u64)%s((%s)%dull, (%s)%dull) & 0x%xull);\n", name, oracle.cType, a, oracle.cType, b, mask(oracle.width))
		}
	}
	harness.WriteString("  *(volatile unsigned int *)0x100000 = 0x5555; /* sifive_test: exit 0 */\n  for (;;) {}\n}\n")
	harness.WriteString("__asm__(\".section .text.init\\n.globl _start\\n_start:\\n  la sp, _stack_top\\n  call cmain\\n1: j 1b\\n\");\n")

	encoded, err := EncodeFunctions(functions, func(s string) string { return s })
	if err != nil {
		t.Fatal(err)
	}
	object, err := WriteObject(ELF, encoded)
	if err != nil {
		t.Fatal(err)
	}
	dir := t.TempDir()
	write := func(name, text string) string {
		path := filepath.Join(dir, name)
		if err := os.WriteFile(path, []byte(text), 0o644); err != nil {
			t.Fatal(err)
		}
		return path
	}
	unitPath := filepath.Join(dir, "unit.o")
	if err := os.WriteFile(unitPath, object, 0o644); err != nil {
		t.Fatal(err)
	}
	harnessPath := write("harness.c", harness.String())
	linkPath := write("link.ld", "ENTRY(_start)\nSECTIONS {\n  . = 0x80000000;\n  .text : { *(.text.init) *(.text*) }\n  .rodata : { *(.rodata*) *(.srodata*) }\n  .data : { *(.data*) *(.sdata*) }\n  .bss : { *(.bss*) *(.sbss*) }\n  . = ALIGN(16);\n  . += 0x10000;\n  _stack_top = .;\n}\n")
	image := filepath.Join(dir, "harness.elf")
	if out, err := exec.Command("riscv64-elf-gcc", "-march=rv64im", "-mabi=lp64", "-mcmodel=medany", "-nostdlib", "-nostartfiles", "-ffreestanding", "-O1", "-T", linkPath, "-o", image, harnessPath, unitPath).CombinedOutput(); err != nil {
		t.Fatalf("link: %v\n%s", err, out)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 90*time.Second)
	defer cancel()
	cmd := exec.CommandContext(ctx, "qemu-system-riscv64", "-machine", "virt", "-bios", "none", "-nographic", "-monitor", "none", "-kernel", image)
	var stdout bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stdout
	if err := cmd.Run(); err != nil {
		t.Fatalf("qemu: %v\n%s", err, stdout.String())
	}
	var got []string
	scanner := bufio.NewScanner(&stdout)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if len(line) == 16 {
			if _, err := strconv.ParseUint(line, 16, 64); err == nil {
				got = append(got, line)
			}
		}
	}
	if len(got) != len(expected) {
		t.Fatalf("qemu printed %d results, expected %d:\n%s", len(got), len(expected), stdout.String())
	}
	index := 0
	for _, oracle := range oracles {
		for _, in := range oracle.inputs {
			if got[index] != expected[index] {
				t.Errorf("%s(%#x, %#x): machine %s, verifier %s", strings.SplitN(oracle.decl, ":", 2)[0], in[0]&mask(oracle.width), in[1]&mask(oracle.width), got[index], expected[index])
			}
			index++
		}
	}
}
