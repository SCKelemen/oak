package asm

import (
	"bufio"
	"bytes"
	"context"
	"fmt"
	"math"
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
	// span names a []u32 parameter the harness materializes as an array of
	// the verifier's fixed element values (elementValue); inputs[i][0] is
	// then the length and inputs[i][1] the scalar parameter.
	span string
	// float marks an (f64, f64) -> f64 unit: the inputs are IEEE-754 bit
	// patterns, the expected result is Go's float64 arithmetic (the same
	// IEEE-754 semantics, round to nearest even) given by expect.
	float  bool
	expect func(a, b float64) float64
}

// rv64Machine is one execution oracle: how the bare-metal harness writes a
// character and exits on it, how it starts, where it links, and how it runs.
type rv64Machine struct {
	name       string
	putc       string // C statement writing char c
	exit       string // C statements ending the run with success
	globals    string // C declarations the harness needs
	start      string // the _start assembly
	linkScript string
	run        func(t *testing.T, image string) string // returns the machine's output
}

// rv64QEMU is the virt machine: a 16550 UART at 0x10000000 and the
// sifive_test finisher at 0x100000.
var rv64QEMU = rv64Machine{
	name:       "qemu-system-riscv64",
	putc:       "*(volatile unsigned char *)0x10000000 = c;",
	exit:       "*(volatile unsigned int *)0x100000 = 0x5555; /* sifive_test: exit 0 */",
	start:      ".section .text.init\n.globl _start\n_start:\n  li t0, 0x6000\n  csrs mstatus, t0\n  la sp, _stack_top\n  call cmain\n1: j 1b\n",
	linkScript: "ENTRY(_start)\nSECTIONS {\n  . = 0x80000000;\n  .text : { *(.text.init) *(.text*) }\n  .rodata : { *(.rodata*) *(.srodata*) }\n  .data : { *(.data*) *(.sdata*) }\n  .bss : { *(.bss*) *(.sbss*) }\n  . = ALIGN(16);\n  . += 0x10000;\n  _stack_top = .;\n}\n",
	run: func(t *testing.T, image string) string {
		ctx, cancel := context.WithTimeout(context.Background(), 90*time.Second)
		defer cancel()
		cmd := exec.CommandContext(ctx, "qemu-system-riscv64", "-machine", "virt", "-bios", "none", "-nographic", "-monitor", "none", "-kernel", image)
		var out bytes.Buffer
		cmd.Stdout, cmd.Stderr = &out, &out
		if err := cmd.Run(); err != nil {
			t.Fatalf("qemu: %v\n%s", err, out.String())
		}
		return out.String()
	},
}

func TestRV64QEMUDifferential(t *testing.T) {
	requireRV64Tools(t, "riscv64-elf-gcc", "qemu-system-riscv64")
	runRV64Differential(t, rv64QEMU)
}

// runRV64Differential encodes the differential units into an ELF object,
// links them with a bare-metal harness for the machine, runs it, and
// compares every printed result with the verifier's concrete execution.
func runRV64Differential(t *testing.T, machine rv64Machine) {
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

	oracles = append(oracles, rv64Oracle{decl: "fmix: (x, y: f64) -> f64", cType: "double", width: 64, float: true,
		expect: func(a, b float64) float64 { return math.Sqrt(math.Abs((a*b+a)/(b-0.5))) * 3.5 },
		inputs: [][2]uint64{{math.Float64bits(1), math.Float64bits(2)}, {math.Float64bits(-7.25), math.Float64bits(0.125)}, {math.Float64bits(1e300), math.Float64bits(3)}, {math.Float64bits(0.5), math.Float64bits(0.5)}, {math.Float64bits(2.5e-310), math.Float64bits(-9)}},
		body: `
  bind fa0 = x
  bind fa1 = y
  clobber ft0, ft1, t0
  fmul.d ft0, fa0, fa1
  fadd.d ft0, ft0, fa0
  lui t0, 261632
  slli t0, t0, 32
  fmv.d.x ft1, t0
  fsub.d ft1, fa1, ft1
  fdiv.d ft0, ft0, ft1
  fsgnjx.d ft0, ft0, ft0
  fsqrt.d ft0, ft0
  lui t0, 262336
  slli t0, t0, 32
  fmv.d.x ft1, t0
  fmul.d fa0, ft0, ft1
  ret`})
	oracles = append(oracles, rv64Oracle{decl: "vsum: (v: []u32, k: u32) -> u32", cType: "unsigned int", width: 32, span: "v", inputs: [][2]uint64{{0, 7}, {1, 0}, {3, 5}, {8, 1}, {13, 0xffffffff}}, body: `
  bind a0, a1 = v
  bind a2 = k
  clobber t0, t1, t2, t3
  slli t1, a1, 32
  srli t1, t1, 32
  li t0, 0
  mv t3, a2
loop:
  bgeu t0, t1, done
  slli t2, t0, 2
  add t2, a0, t2
  lw t2, 0(t2)
  addw t3, t3, t2
  addi t0, t0, 1
  j loop
done:
  mv a0, t3
  ret`})
	var functions []*Function
	var harness strings.Builder
	harness.WriteString("typedef struct { const unsigned int *base; unsigned int len; } view_u32;\n")
	harness.WriteString("typedef unsigned long long u64;\n")
	harness.WriteString("static double bits_to_double(u64 b) { double d; __builtin_memcpy(&d, &b, 8); return d; }\n")
	harness.WriteString("static u64 double_to_bits(double d) { u64 b; __builtin_memcpy(&b, &d, 8); return b; }\n")
	harness.WriteString(machine.globals)
	harness.WriteString("static void putc_(char c) { " + machine.putc + " }\n")
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
		if oracle.float {
			fmt.Fprintf(&harness, "extern double %s(double, double);\n", fn.Name)
			for _, in := range oracle.inputs {
				expected = append(expected, fmt.Sprintf("%016x", math.Float64bits(oracle.expect(math.Float64frombits(in[0]), math.Float64frombits(in[1])))))
			}
			continue
		}
		if oracle.span != "" {
			fmt.Fprintf(&harness, "extern %s %s(view_u32, %s);\n", oracle.cType, fn.Name, oracle.cType)
			// The array holds the verifier's fixed memory for this span.
			fmt.Fprintf(&harness, "static const unsigned int %s_elems[16] = {", oracle.span)
			for k := 0; k < 16; k++ {
				fmt.Fprintf(&harness, "%du,", elementValue(oracle.span, uint64(k), 32))
			}
			harness.WriteString("};\n")
			for _, in := range oracle.inputs {
				env := map[string]uint64{spanLenName(oracle.span): in[0], "k": in[1] & mask(oracle.width)}
				result, _, reason, ok := executeBody(fn, sig, env)
				if !ok {
					t.Fatalf("%s: verifier: %s", fn.Name, reason)
				}
				expected = append(expected, fmt.Sprintf("%016x", result.eval(env)&mask(oracle.width)))
			}
			continue
		}
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
		if oracle.float {
			for _, in := range oracle.inputs {
				fmt.Fprintf(&harness, "  { double r = %s(bits_to_double(%dull), bits_to_double(%dull)); puthex(double_to_bits(r)); }\n", name, in[0], in[1])
			}
			continue
		}
		if oracle.span != "" {
			for _, in := range oracle.inputs {
				fmt.Fprintf(&harness, "  puthex((u64)%s((view_u32){%s_elems, %du}, (%s)%dull) & 0x%xull);\n", name, oracle.span, in[0], oracle.cType, in[1]&mask(oracle.width), mask(oracle.width))
			}
			continue
		}
		for _, in := range oracle.inputs {
			a, b := in[0]&mask(oracle.width), in[1]&mask(oracle.width)
			// The result is printed at its contract width: a signed narrow
			// result would otherwise sign-extend through the C cast.
			fmt.Fprintf(&harness, "  puthex((u64)%s((%s)%dull, (%s)%dull) & 0x%xull);\n", name, oracle.cType, a, oracle.cType, b, mask(oracle.width))
		}
	}
	harness.WriteString("  " + machine.exit + "\n  for (;;) {}\n}\n")
	harness.WriteString("__asm__(" + quoteAsmRV64(machine.start) + ");\n")

	encoded, err := EncodeFunctions(functions, func(s string) string { return s })
	if err != nil {
		t.Fatal(err)
	}
	// The harness is lp64d (the units carry f64 through fa registers), so
	// the companion object declares the double-float ABI as a hosted
	// target's would.
	object, err := WriteObjectWith(ELF, encoded, ObjectOptions{RV64FloatABI: "double"})
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
	linkPath := write("link.ld", machine.linkScript)
	image := filepath.Join(dir, "harness.elf")
	if out, err := exec.Command("riscv64-elf-gcc", "-march=rv64imafdc", "-mabi=lp64d", "-mcmodel=medany", "-nostdlib", "-nostartfiles", "-ffreestanding", "-O1", "-T", linkPath, "-o", image, harnessPath, unitPath).CombinedOutput(); err != nil {
		t.Fatalf("link: %v\n%s", err, out)
	}
	output := machine.run(t, image)
	var got []string
	scanner := bufio.NewScanner(strings.NewReader(output))
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if len(line) == 16 {
			if _, err := strconv.ParseUint(line, 16, 64); err == nil {
				got = append(got, line)
			}
		}
	}
	if len(got) != len(expected) {
		t.Fatalf("%s printed %d results, expected %d:\n%s", machine.name, len(got), len(expected), output)
	}
	index := 0
	for _, oracle := range oracles {
		for _, in := range oracle.inputs {
			if got[index] != expected[index] {
				side := "verifier"
				if oracle.float {
					side = "IEEE-754 (Go)"
				}
				t.Errorf("%s: %s(%#x, %#x): machine %s, %s %s", machine.name, strings.SplitN(oracle.decl, ":", 2)[0], in[0]&mask(oracle.width), in[1]&mask(oracle.width), got[index], side, expected[index])
			}
			index++
		}
	}
}

// quoteAsmRV64 spells assembly text as a C string literal.
func quoteAsmRV64(text string) string {
	return `"` + strings.ReplaceAll(strings.ReplaceAll(text, `"`, `\"`), "\n", `\n`) + `"`
}
