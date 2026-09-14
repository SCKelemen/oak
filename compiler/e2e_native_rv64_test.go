package compiler

import (
	"bytes"
	"context"
	"encoding/binary"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
	"github.com/SCKelemen/oak/toolchain"
)

// The RV64 lane of the native backend (docs/spec/94-assembler.md §9,
// nativegen/rv64.go): the same fixed-width integer corpus the AArch64 lane
// lowers, on a RISC-V target, through the RV64 seam checker, verifier,
// encoder, and ELF writer.

// nativeRV64Lower lowers a program for a RISC-V target through the native
// backend, returning the emitted C and object with the backend's
// diagnostics.
func nativeRV64Lower(t *testing.T, tgt target.Target, source string) (NativeOutput, []string) {
	t.Helper()
	var infos []string
	comp := New().WithSource("native.oak", source).WithTarget(tgt).WithNativeBodies().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	native, err := comp.EmitNative(asm.ELF).Get()
	if err != nil {
		t.Fatalf("rv64 native bodies: %v\n%s", err, strings.Join(infos, "\n"))
	}
	return native, infos
}

func TestE2ENativeRV64Lowers(t *testing.T) {
	native, infos := nativeRV64Lower(t, rv64Linux, nativeProgram)
	joined := strings.Join(infos, "\n")
	t.Log(joined)
	for _, fn := range []string{"mix", "byte_sum", "clamp8", "divmod", "between", "sum_to", "combine", "fact", "check_all", "widen", "narrow", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the rv64 lane; diagnostics:\n%s", fn, joined)
		}
	}
	// divw/remw as the uninterpreted quotient and a - (a / b) * b
	// (docs/spec/94-assembler.md §8, thirty-first increment).
	if !strings.Contains(joined, "asm unit divmod: proven") {
		t.Errorf("divmod was not proven by the verifier; diagnostics:\n%s", joined)
	}
	if machine := binary.LittleEndian.Uint16(native.Object[18:20]); machine != 243 {
		t.Fatalf("companion object e_machine %d, want EM_RISCV (243)", machine)
	}
	if !strings.Contains(native.C, "#if !(defined(__riscv) && (__riscv_xlen == 64)) || defined(OAK_PORTABLE_INTRINSICS)") {
		t.Error("the Oak bodies must be guarded by the rv64 lane's negation")
	}
}

// nativeRV64Machine runs a freestanding/riscv64 image under
// qemu-system-riscv64's virt machine: the harness prints oak_main's result
// over the 16550 UART and exits through the sifive_test device.
type nativeRV64Machine struct {
	qemu      string
	uart      string
	exitCode  string
	startAsm  string
	origin    string
	extraArgs []string
}

var rv64Virt = nativeRV64Machine{
	qemu:     "qemu-system-riscv64",
	uart:     "0x10000000",
	exitCode: `*(volatile unsigned *)0x100000 = 0x5555; /* sifive_test: exit 0 */`,
	// A trap (an ebreak from a failed guard) lands in the machine-mode
	// handler, which prints TRAP and exits, so a trapping run is a fast
	// verdict rather than a hung machine.
	// mstatus.FS is set so the FPU is on for the hard-float runs, and
	// mstatus.VS so the vector unit is on for the runs with V (the bits are
	// ignored on a processor without it).
	startAsm: ".section .text.init\n.globl _start\n_start:\n  la sp, _stack_top\n  li t0, 0x6600\n  csrs mstatus, t0\n  la t0, trap_handler\n  csrw mtvec, t0\n  call cmain\n1: j 1b\n" +
		"trap_handler:\n  li t0, 0x10000000\n  li t1, 84\n  sb t1, 0(t0)\n  li t1, 82\n  sb t1, 0(t0)\n  li t1, 65\n  sb t1, 0(t0)\n  li t1, 80\n  sb t1, 0(t0)\n  li t1, 10\n  sb t1, 0(t0)\n  li t0, 0x100000\n  li t1, 0x5555\n  sw t1, 0(t0)\n2: j 2b\n",
	origin: "0x80000000",
}

// runNativeRV64Bare compiles the emitted C for freestanding/riscv64 with the
// resolved cross compiler, links the Oak companion object beside it into a
// bare-metal image with a UART harness (the shape of e2e_mcu_test.go), runs
// the image under QEMU, and returns the machine's output.
func runNativeRV64Bare(t *testing.T, name string, native NativeOutput) string {
	t.Helper()
	return runNativeRV64BareABI(t, name, native, false)
}

// runNativeRV64BareABI is runNativeRV64Bare with the floating-point ABI
// chosen: hardFloat links under lp64d on a processor with F and D (the
// hosted targets' contract, so C emitted for linux/riscv64 runs on the
// bare machine with the FPU enabled by the start code), else the
// freestanding target's soft-float lp64.
func runNativeRV64BareABI(t *testing.T, name string, native NativeOutput, hardFloat bool) string {
	t.Helper()
	return runNativeRV64BareWith(t, name, native, nativeRV64Run{hardFloat: hardFloat})
}

// nativeRV64Run selects the machine a bare run needs: the hard-float ABI,
// and the vector extension at a VLEN (the C backend's RVV realization and
// the native lane's vector units both need V on the processor;
// mstatus.VS is enabled by the start code).
type nativeRV64Run struct {
	hardFloat bool
	vector    bool
	vlen      int
}

func runNativeRV64BareWith(t *testing.T, name string, native NativeOutput, run nativeRV64Run) string {
	t.Helper()
	hardFloat := run.hardFloat
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	if _, err := exec.LookPath(rv64Virt.qemu); err != nil {
		t.Skipf("%s not present", rv64Virt.qemu)
	}
	drv, err := toolchain.Resolve(bare, toolchain.Options{}, nil, nil)
	if err != nil || drv.Kind != "zig" {
		t.Skipf("no zig for %s (%v)", bare, err)
	}
	dir := t.TempDir()
	write := func(file, text string) string {
		path := filepath.Join(dir, file)
		if err := os.WriteFile(path, []byte(text), 0o644); err != nil {
			t.Fatal(err)
		}
		return path
	}
	oakC := write(name+".c", native.C)
	cpu, abi := bare.DefaultCPU(), "lp64"
	if hardFloat {
		cpu, abi = "generic_rv64+m+a+f+d", "lp64d"
	}
	if run.vector {
		cpu += "+v"
	}
	objArgs := []string{"cc", "--target=" + bare.ZigTriple(), "-mcpu=" + cpu, "-mabi=" + abi, "-mcmodel=medany", "-ffreestanding", "-nostdlib", "-fno-unwind-tables", "-fno-asynchronous-unwind-tables", "-DOAK_FREESTANDING", "-std=c99", "-O1", "-ffp-contract=off"}
	if hardFloat {
		// The C backend's float intrinsics are libm calls, undeclared on a
		// freestanding build (there is no libm): the oracle maps the two the
		// corpus reaches to the compiler's builtins (single F/D instructions).
		proto := write("libm_shim.h", "float oak_test_fabsf(float);\ndouble oak_test_fma(double, double, double);\n")
		objArgs = append(objArgs, "-Dfabsf=oak_test_fabsf", "-Dfma=oak_test_fma", "-include", proto)
	}
	objArgs = append(objArgs, "-c", "-o", filepath.Join(dir, "program.o"), oakC)
	if out, err := exec.Command(drv.Path, objArgs...).CombinedOutput(); err != nil {
		t.Fatalf("oak object: %v\n%s", err, out)
	}
	inputs := []string{filepath.Join(dir, "program.o")}
	if native.Object != nil {
		companion := filepath.Join(dir, "companion.o")
		if err := os.WriteFile(companion, native.Object, 0o644); err != nil {
			t.Fatal(err)
		}
		inputs = append(inputs, companion)
	}
	libm := ""
	if hardFloat {
		// The libm functions the oracle's C reaches, as the F/D instructions
		// they are (compiler-rt's software fma cannot link at this address).
		libm = "float oak_test_fabsf(float x) { float r; __asm__(\"fsgnjx.s %0, %1, %1\" : \"=f\"(r) : \"f\"(x)); return r; }\n" +
			"double oak_test_fma(double a, double b, double c) { double r; __asm__(\"fmadd.d %0, %1, %2, %3\" : \"=f\"(r) : \"f\"(a), \"f\"(b), \"f\"(c)); return r; }\n"
	}
	harness := "extern int oak_main(void);\n" + libm +
		"static void putc_(char c) { *(volatile unsigned char *)" + rv64Virt.uart + " = c; }\n" +
		"long long oak_host_write(long long fd, const unsigned char *buf, unsigned long len) { (void)fd; for (unsigned long i = 0; i < len; i++) putc_((char)buf[i]); return (long long)len; }\n" +
		"static void puthex(unsigned v) { for (int i = 28; i >= 0; i -= 4) putc_(\"0123456789abcdef\"[(v >> i) & 15]); putc_('\\n'); }\n" +
		"void cmain(void) { puthex((unsigned)oak_main()); " + rv64Virt.exitCode + " for (;;) {} }\n" +
		"__asm__(" + quoteAsm(rv64Virt.startAsm) + ");\n"
	harnessC := write("harness.c", harness)
	link := write("link.ld", "ENTRY(_start)\nSECTIONS {\n  /DISCARD/ : { *(.note*) *(.comment) }\n  . = "+rv64Virt.origin+";\n  .text : { *(.text.init) *(.text*) }\n  .rodata : { *(.rodata*) *(.srodata*) }\n  .data : { *(.data*) *(.sdata*) }\n  .bss : { *(.bss*) *(.sbss*) }\n  . = ALIGN(16);\n  . += 0x8000;\n  _stack_top = .;\n}\n")
	image := filepath.Join(dir, "image.elf")
	// The harness is compiled here too: the medium-any code model reaches
	// the image at 0x80000000 (as toolchain.Resolve sets for the Oak object).
	linkArgs := []string{"cc", "--target=" + bare.ZigTriple(), "-mcpu=" + cpu, "-mabi=" + abi, "-mcmodel=medany", "-ffreestanding", "-nostartfiles", "-fno-unwind-tables", "-fno-asynchronous-unwind-tables", "-O1", "-Wl,--build-id=none", "-T", link, "-o", image, harnessC}
	linkArgs = append(linkArgs, inputs...)
	if out, err := exec.Command(drv.Path, linkArgs...).CombinedOutput(); err != nil {
		t.Fatalf("link: %v\n%s", err, out)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
	defer cancel()
	args := append([]string{"-M", "virt", "-bios", "none", "-nographic", "-monitor", "none", "-kernel", image}, rv64Virt.extraArgs...)
	if run.vector {
		vlen := run.vlen
		if vlen == 0 {
			vlen = 128
		}
		args = append(args, "-cpu", fmt.Sprintf("rv64,v=true,vlen=%d", vlen))
	}
	cmd := exec.CommandContext(ctx, rv64Virt.qemu, args...)
	var out bytes.Buffer
	cmd.Stdout, cmd.Stderr = &out, &out
	_ = cmd.Run() // the exit path is the harness's; the output is the verdict
	return out.String()
}

// The native corpus executes on RISC-V: every function lowered by the rv64
// lane, encoded by the Oak assembler into the companion object, linked
// beside the C shell, exits 42 under QEMU — and so do the C backend alone
// and the native build's portable realization.
func TestE2ENativeRV64UnderQEMU(t *testing.T) {
	skipInShort(t)
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	native, infos := nativeRV64Lower(t, bare, nativeProgram)
	joined := strings.Join(infos, "\n")
	for _, fn := range []string{"mix", "byte_sum", "clamp8", "divmod", "between", "sum_to", "combine", "fact", "check_all", "widen", "narrow", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Fatalf("%s was not lowered by the rv64 lane; diagnostics:\n%s", fn, joined)
		}
	}
	if native.Object == nil {
		t.Fatal("no companion object")
	}
	if out := runNativeRV64Bare(t, "native_rv64", native); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("native bodies under QEMU did not exit 42:\n%s", out)
	}
	cOnly, err := New().WithSource("native.oak", nativeProgram).WithTarget(bare).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if out := runNativeRV64Bare(t, "native_rv64_c", NativeOutput{C: cOnly}); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("C backend under QEMU did not exit 42:\n%s", out)
	}
	// A trap in a natively lowered body: the assertion's failure is an
	// ebreak, which the harness never returns from — no exit code printed.
	trapping := strings.Replace(nativeProgram, "assert(mix(u32(5), u32(7)) == u32(37))", "assert(mix(u32(5), u32(7)) == u32(38))", 1)
	native, _ = nativeRV64Lower(t, bare, trapping)
	if out := runNativeRV64Bare(t, "native_rv64_trap", native); strings.Contains(out, "0000002a") || !strings.Contains(out, "TRAP\n") {
		t.Fatalf("a failing assertion in a native body must trap, not exit 42:\n%s", out)
	}
}

// nativeRV64Extra exercises what the corpus above does not and the RV64
// canonical form makes delicate: 64-bit constants beyond the `li` range
// (the low half with bit 31 set), 16-bit arithmetic and negation, shifts by
// a variable count, 64-bit and unsigned 32-bit division and remainder
// (a sign-extended canonical u32 must divide as the unsigned value),
// unsigned and signed `>`/`<=` at the 32-bit boundary, `||`, more
// variables than callee-saved registers (frame slots), calls nested in
// arguments, the u32 -> u64 widening (a zero extension of a sign-extended
// register), sign-extending widenings, truncations, `^`, and a negative
// 64-bit constant.
const nativeRV64Extra = `
wide: (x: u64) -> u64 = x ^ u64(0x1234567880000001)
half: (a: u16, b: u16) -> u16 = (a * b) + u16(1)
short_neg: (a: i16) -> i16 = -a - i16(1)
shifts: (x: u32, n: u32) -> u32 = (x << n) | (x >> (n & u32(7)))
byte_shift: (x: u8, n: u8) -> u8 = (x << n) ^ (x >> u8(1))
udiv: (a, b: u64) -> u64 = a / b + a % b
cmp_u: (a, b: u32) -> u32 = a > b ? u32(1) | (a <= b ? u32(2) | u32(3))
cmp_s: (a, b: i32) -> i32 = a > b ? i32(1) | (a <= b ? i32(2) | i32(3))
either: (a, b: Bool) -> Bool = a || b
many: (n: u32) -> u32 {
  a: u32 = n + u32(1)
  b: u32 = a + u32(1)
  c: u32 = b + u32(1)
  d: u32 = c + u32(1)
  e: u32 = d + u32(1)
  f: u32 = e + u32(1)
  g: u32 = f + u32(1)
  h: u32 = g + u32(1)
  i: u32 = h + u32(1)
  j: u32 = i + u32(1)
  k: u32 = j + u32(1)
  l: u32 = k + u32(1)
  a + b + c + d + e + f + g + h + i + j + k + l
}
mix2: (a, b: u32) -> u32 = a * u32(3) + b
nested: (a: u32) -> u32 = mix2(mix2(a, u32(1)), mix2(u32(2), a))
widen_u: (x: u32) -> u64 = u64(x) + u64(1)
widen_s: (x: i32) -> i64 = i64(x) * i64(2)
narrow8: (x: u64) -> u8 = u8_trunc_u64(x)
narrow_s8: (x: i64) -> i8 = i8_trunc_i64(x)
big_neg: (x: i64) -> i64 = x + i64(-5000000000)
flip: (x: u16) -> u16 = ^x
remu32: (a, b: u32) -> u32 = a % b

main: (): i32 {
  assert(wide(u64(1)) == u64(0x1234567880000000))
  assert(half(u16(300), u16(300)) == u16(24465))
  assert(short_neg(i16(-32768)) == i16(32767))
  assert(shifts(u32(0x80000001), u32(4)) == u32(0x08000010))
  assert(byte_shift(u8(0x81), u8(1)) == u8(0x42))
  assert(udiv(u64(0x7FFFFFFFFFFFFFFF), u64(2)) == u64(0x4000000000000000))
  assert(cmp_u(u32(0x80000000), u32(1)) == u32(1))
  assert(cmp_u(u32(1), u32(0x80000000)) == u32(2))
  assert(cmp_s(i32(-1), i32(1)) == i32(2))
  assert(cmp_s(i32(1), i32(-1)) == i32(1))
  assert(either(false, true))
  assert(!either(false, false))
  assert(many(u32(0)) == u32(78))
  assert(nested(u32(5)) == u32(59))
  assert(widen_u(u32(0x80000000)) == u64(0x80000001))
  assert(widen_s(i32(-3)) == i64(-6))
  assert(narrow8(u64(0x1FF)) == u8(0xFF))
  assert(narrow_s8(i64(0x80)) == i8(-128))
  assert(big_neg(i64(1)) == i64(-4999999999))
  assert(flip(u16(0x00FF)) == u16(0xFF00))
  assert(remu32(u32(0x80000005), u32(0x80000000)) == u32(5))
  7
}
`

var nativeRV64ExtraFunctions = []string{"wide", "half", "short_neg", "shifts", "byte_shift", "udiv", "cmp_u", "cmp_s", "either", "many", "mix2", "nested", "widen_u", "widen_s", "narrow8", "narrow_s8", "big_neg", "flip", "remu32", "main"}

func TestE2ENativeRV64ExtraUnderQEMU(t *testing.T) {
	skipInShort(t)
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	native, infos := nativeRV64Lower(t, bare, nativeRV64Extra)
	joined := strings.Join(infos, "\n")
	for _, fn := range nativeRV64ExtraFunctions {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Fatalf("%s was not lowered by the rv64 lane; diagnostics:\n%s", fn, joined)
		}
	}
	// The rest are trusted (calls) or agree on every witness (the u16
	// product's BDD). A variable shift count is proven below the width,
	// where the guarded native shift is Oak's (docs/spec/94-assembler.md
	// §8, variable shift counts).
	for _, fn := range []string{"wide", "short_neg", "shifts", "byte_shift", "cmp_u", "cmp_s", "either", "many", "mix2", "widen_u", "widen_s", "narrow8", "narrow_s8", "big_neg", "flip"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s must be proven equal to its Oak body; diagnostics:\n%s", fn, joined)
		}
	}
	if out := runNativeRV64Bare(t, "native_rv64_extra", native); !strings.Contains(out, "00000007\n") {
		t.Fatalf("native bodies under QEMU did not exit 7:\n%s", out)
	}
	cOnly, err := New().WithSource("native.oak", nativeRV64Extra).WithTarget(bare).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if out := runNativeRV64Bare(t, "native_rv64_extra_c", NativeOutput{C: cOnly}); !strings.Contains(out, "00000007\n") {
		t.Fatalf("C backend under QEMU did not exit 7:\n%s", out)
	}
}

// The same corpus through the AArch64 lane on an arm64 host: one program,
// two native lanes, the C backend as the oracle for both.
func TestE2ENativeRV64ExtraOnArm64(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("native.oak", nativeRV64Extra).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	if _, code, abnormal := buildAndRunFrom(t, "native_extra_arm64", comp); abnormal || code != 7 {
		t.Fatalf("arm64 native bodies: exit = (%d, abnormal=%v), want 7\n%s", code, abnormal, strings.Join(infos, "\n"))
	}
	// The variable shift counts are proven on this lane too: the guarded
	// w-register shift below the width is Oak's (docs/spec/94-assembler.md
	// §8, variable shift counts).
	joined := strings.Join(infos, "\n")
	for _, fn := range []string{"shifts", "byte_shift"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s must be proven equal to its Oak body; diagnostics:\n%s", fn, joined)
		}
	}
}

// A hosted RISC-V build of the natively lowered corpus runs under the
// user-mode emulator `oak run -target linux/riscv64` would use: the static
// musl binary zig links, with the Oak companion object inside, exits with
// the program's code. Skips without a cross compiler or an emulator (the
// CI cross-targets job installs qemu-user-static).
func TestE2ENativeRV64UnderUserQEMU(t *testing.T) {
	emulator, err := toolchain.ResolveEmulator(rv64Linux, nil, nil)
	if err != nil {
		t.Skipf("no emulator: %v", err)
	}
	for _, program := range []struct {
		name, source string
		want         int
	}{{"corpus", nativeProgram, 42}, {"extra", nativeRV64Extra, 7}} {
		t.Run(program.name, func(t *testing.T) {
			bin := crossLink(t, rv64Linux, New().WithSource("native.oak", program.source).WithNativeBodies())
			cmd := exec.Command(emulator.Path, append(append([]string{}, emulator.Args...), bin)...)
			out, err := cmd.CombinedOutput()
			code := 0
			if exitErr, isExit := err.(*exec.ExitError); isExit {
				code = exitErr.ExitCode()
			} else if err != nil {
				t.Fatalf("%s: %v\n%s", emulator.Command(), err, out)
			}
			if code != program.want {
				t.Fatalf("exit %d under %s, want %d\n%s", code, emulator.Command(), program.want, out)
			}
		})
	}
}

// Spans and views on the rv64 lane (docs/spec/94-assembler.md §9): the
// AArch64 lane's span corpus — a view sum, a byte total with
// zero-extending loads, a fill through a span of halfwords, an element
// read, the tail self-call as a loop — lowered through the checker's
// guarded element idiom (the normalized length, `bgeu idx, norm, trap`,
// the scaled add, the access at offset 0), run under QEMU against the C
// backend; an index at the length traps in the native realization.
func TestE2ENativeRV64SpansUnderQEMU(t *testing.T) {
	skipInShort(t)
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	native, infos := nativeRV64Lower(t, bare, nativeSpanProgram)
	joined := strings.Join(infos, "\n")
	for _, fn := range []string{"sum", "byte_total", "fill", "at", "count_down"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Fatalf("%s was not lowered by the rv64 lane; diagnostics:\n%s", fn, joined)
		}
	}
	// The guarded element load, the coupled loops, and the tail recursion
	// as a loop are proven, as on the AArch64 lane.
	for _, fn := range []string{"at", "sum", "byte_total", "count_down"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s must be proven equal to its Oak body; diagnostics:\n%s", fn, joined)
		}
	}
	if out := runNativeRV64Bare(t, "native_rv64_spans", native); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("native spans under QEMU did not exit 42:\n%s", out)
	}
	cOnly, err := New().WithSource("native.oak", nativeSpanProgram).WithTarget(bare).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if out := runNativeRV64Bare(t, "native_rv64_spans_c", NativeOutput{C: cOnly}); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("C backend under QEMU did not exit 42:\n%s", out)
	}
	native, infos = nativeRV64Lower(t, bare, nativeOutOfRangeProgram)
	if !strings.Contains(strings.Join(infos, "\n"), "asm unit at:") {
		t.Fatalf("at was not lowered; diagnostics:\n%s", strings.Join(infos, "\n"))
	}
	if out := runNativeRV64Bare(t, "native_rv64_range", native); !strings.Contains(out, "TRAP\n") || strings.Contains(out, "00000000\n") {
		t.Fatalf("an index at the length must trap natively:\n%s", out)
	}
}

// Owned arrays in the frame on the rv64 lane: the AArch64 lane's array
// corpus without its float function (floating point is the next
// increment) — a histogram bucketed by a computed index, a literal array
// passed to a leaf through view, zero-filled storage filled through span
// and read back by literal index, signed bytes with sign extension — run
// under QEMU against the C backend.
var nativeRV64ArrayProgram = strings.Replace(strings.Replace(nativeArrayProgram, "  assert(float_total() == 42.0)\n", "", 1), floatTotalSource, "", 1)

const floatTotalSource = `// Float elements in the frame.
float_total: () -> f64 {
  xs: [3]f64 = [0.5, 1.5, 40.0]
  i: u32 = u32(0)
  acc: f64 = 0.0
  while i < len(xs) {
    acc = acc + xs[i]
    i = i + u32(1)
  }
  acc
}
`

func TestE2ENativeRV64ArraysUnderQEMU(t *testing.T) {
	skipInShort(t)
	if strings.Contains(nativeRV64ArrayProgram, "float_total") {
		t.Fatal("the float function was not cut from the corpus")
	}
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	native, infos := nativeRV64Lower(t, bare, nativeRV64ArrayProgram)
	joined := strings.Join(infos, "\n")
	for _, fn := range []string{"sum", "fill", "buckets", "squares", "filled", "signed_bytes", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Fatalf("%s was not lowered by the rv64 lane; diagnostics:\n%s", fn, joined)
		}
	}
	if out := runNativeRV64Bare(t, "native_rv64_arrays", native); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("native arrays under QEMU did not exit 42:\n%s", out)
	}
	cOnly, err := New().WithSource("native.oak", nativeRV64ArrayProgram).WithTarget(bare).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if out := runNativeRV64Bare(t, "native_rv64_arrays_c", NativeOutput{C: cOnly}); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("C backend under QEMU did not exit 42:\n%s", out)
	}
	// An index at the length of an owned array traps natively.
	outOfRange := strings.Replace(nativeRV64ArrayProgram, "assert(signed_bytes(u32(2)) == i32(-3))", "assert(signed_bytes(u32(3)) == i32(-3))", 1)
	native, _ = nativeRV64Lower(t, bare, outOfRange)
	if out := runNativeRV64Bare(t, "native_rv64_arrays_range", native); !strings.Contains(out, "TRAP\n") || strings.Contains(out, "0000002a") {
		t.Fatalf("an index at the array's length must trap natively:\n%s", out)
	}
}

// Floating point on the rv64 lane (LP64D): the AArch64 lane's float corpus
// — f32/f64 arithmetic, IEEE comparisons in a clamp, negation and abs,
// fma, widening and rounding between the precisions, trunc and saturating
// conversions to integers, int to float, bit reinterpretation, a float
// span reduction, a fill through a span of f64, float locals across a call
// — lowered for linux/riscv64 (the target whose libc is lp64d) and run on
// the bare machine under lp64d with the FPU on, against the C backend; the
// out-of-range trunc traps.
func TestE2ENativeRV64FloatsUnderQEMU(t *testing.T) {
	skipInShort(t)
	native, infos := nativeRV64Lower(t, rv64Linux, nativeFloatProgram)
	joined := strings.Join(infos, "\n")
	for _, fn := range []string{"scale", "halve", "clamp", "neg_abs", "least", "most", "hypot_sq", "widen_round", "to_int", "sat_int", "from_int", "bits_of", "total", "fill_f64", "combine", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Fatalf("%s was not lowered by the rv64 lane; diagnostics:\n%s", fn, joined)
		}
	}
	// The NaN-propagating min/max lower behind two NaN tests (rvMinMax) and
	// the verifier proves them against Oak's min/max up to the NaN payload.
	// The float span reduction is proven through the loop recognizer: flw
	// through the span element address, the accumulator in fs0.
	for _, fn := range []string{"least", "most", "total"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s was not proven by the verifier; diagnostics:\n%s", fn, joined)
		}
	}
	if out := runNativeRV64BareABI(t, "native_rv64_floats", native, true); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("native floats under QEMU did not exit 42:\n%s", out)
	}
	cOnly, err := New().WithSource("native.oak", nativeFloatProgram).WithTarget(rv64Linux).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if out := runNativeRV64BareABI(t, "native_rv64_floats_c", NativeOutput{C: cOnly}, true); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("C backend under QEMU did not exit 42:\n%s", out)
	}
	native, infos = nativeRV64Lower(t, rv64Linux, nativeFloatTrapProgram)
	if !strings.Contains(strings.Join(infos, "\n"), "asm unit to_int:") {
		t.Fatalf("to_int was not lowered; diagnostics:\n%s", strings.Join(infos, "\n"))
	}
	if out := runNativeRV64BareABI(t, "native_rv64_float_trap", native, true); !strings.Contains(out, "TRAP\n") || strings.Contains(out, "00000000\n") {
		t.Fatalf("an out-of-range trunc must trap natively:\n%s", out)
	}
	// The soft-float freestanding target keeps every float body with C.
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	_, infos = nativeRV64Lower(t, bare, nativeFloatProgram)
	joined = strings.Join(infos, "\n")
	if !strings.Contains(joined, "scale left to the C backend (floating point on a soft-float target") {
		t.Fatalf("freestanding/riscv64 must leave float bodies to the C backend:\n%s", joined)
	}
}

// Record locals on the rv64 lane: the AArch64 lane's record corpus — a
// Point updated through its fields, a five-field record of mixed widths
// updated in a loop with a Bool field written from a comparison and read
// as a condition, a copy diverging from its source, whole-record
// assignment, a float field — placed by the C backend's own layout and run
// under QEMU (lp64d: the corpus has an f64 field) against the C backend.
func TestE2ENativeRV64RecordsUnderQEMU(t *testing.T) {
	skipInShort(t)
	native, infos := nativeRV64Lower(t, rv64Linux, nativeRecordProgram)
	joined := strings.Join(infos, "\n")
	for _, fn := range []string{"manhattan", "accumulate", "copy_point", "swap_in", "scaled", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Fatalf("%s was not lowered by the rv64 lane; diagnostics:\n%s", fn, joined)
		}
	}
	if out := runNativeRV64BareABI(t, "native_rv64_records", native, true); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("native records under QEMU did not exit 42:\n%s", out)
	}
	cOnly, err := New().WithSource("native.oak", nativeRecordProgram).WithTarget(rv64Linux).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if out := runNativeRV64BareABI(t, "native_rv64_records_c", NativeOutput{C: cOnly}, true); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("C backend under QEMU did not exit 42:\n%s", out)
	}
}

// Tagged unions on the rv64 lane, as locals (unions do not cross calls on
// this lane yet): variants built with scalar and record payloads, value
// and statement matches with payload bindings and a wildcard arm, a
// record-valued Bool conditional over variants, a literal-pattern match
// over a scalar, and reassignment of a union local — run under QEMU
// against the C backend.
const nativeRV64UnionProgram = `
Shape: type =
  | Circle: i32
  | Square: i32
  | Empty

Point: type = struct {
  x: i32
  y: i32
}

Hit: type =
  | At: Point
  | Miss

area_sum: (r: i32, w: i32) -> i32 {
  c: Shape = .Circle(r)
  q: Shape = .Square(w)
  e: Shape = .Empty
  a: i32 = c ?
    | .Circle(x) -> x * 3
    | .Square(x) -> x * x
    | .Empty -> 0
  b: i32 = q ?
    | .Circle(x) -> x * 3
    | .Square(x) -> x * x
    | .Empty -> 0
  d: i32 = e ?
    | .Circle(x) -> x * 3
    | .Square(x) -> x * x
    | .Empty -> 0
  a + b + d
}

score: (x: i32, y: i32, miss: Bool) -> i32 {
  h: Hit = miss ? .Miss | .At(Point { x: x, y: y })
  h ?
    | .At(p) -> 10 + p.x * p.y
    | _ -> 9
}

tally: (x: i32, y: i32, k: i32) -> i32 {
  acc: i32 = k
  h: Hit = .At(Point { x: x, y: y })
  h ?
    | .At(p) -> { acc = acc + p.x + p.y }
    | .Miss -> { acc = acc - 1 }
  m: Hit = .Miss
  m ?
    | .At(p) -> { acc = acc + p.x + p.y }
    | .Miss -> { acc = acc - 1 }
  acc
}

name_len: (n: u32) -> u32 = n ?
  | 1 -> u32(3)
  | 2 -> u32(5)
  | _ -> u32(0)

reassign: (n: i32) -> i32 {
  e: Shape = .Empty
  e = .Circle(n)
  e ?
    | .Circle(x) -> x * 3
    | _ -> 0
}

main: (): i32 {
  assert(area_sum(5, 4) == 31)
  assert(score(3, 4, false) == 22)
  assert(score(3, 4, true) == 9)
  assert(tally(3, 4, 10) == 16)
  assert(name_len(u32(2)) + name_len(u32(9)) == u32(5))
  assert(reassign(2) == 6)
  42
}
`

func TestE2ENativeRV64UnionsUnderQEMU(t *testing.T) {
	skipInShort(t)
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	native, infos := nativeRV64Lower(t, bare, nativeRV64UnionProgram)
	joined := strings.Join(infos, "\n")
	for _, fn := range []string{"area_sum", "score", "tally", "name_len", "reassign", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Fatalf("%s was not lowered by the rv64 lane; diagnostics:\n%s", fn, joined)
		}
	}
	if out := runNativeRV64Bare(t, "native_rv64_unions", native); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("native unions under QEMU did not exit 42:\n%s", out)
	}
	cOnly, err := New().WithSource("native.oak", nativeRV64UnionProgram).WithTarget(bare).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if out := runNativeRV64Bare(t, "native_rv64_unions_c", NativeOutput{C: cOnly}); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("C backend under QEMU did not exit 42:\n%s", out)
	}
}

// The same corpus through the AArch64 lane on an arm64 host.
func TestE2ENativeRV64UnionsOnArm64(t *testing.T) {
	requireArm64Host(t)
	comp := New().WithSource("native.oak", nativeRV64UnionProgram).WithNativeBodies().WithNativeAsm()
	if _, code, abnormal := buildAndRunFrom(t, "native_unions_arm64", comp); abnormal || code != 42 {
		t.Fatalf("arm64 native bodies: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// Spans in functions that call, on the rv64 lane: the AArch64 lane's
// span-call corpus — a view forwarded twice with len read after the calls,
// a store loop calling a helper for every element, two views parked in
// callee-saved registers with a leaf called before and inside the loop —
// run under QEMU against the C backend.
func TestE2ENativeRV64SpanCallsUnderQEMU(t *testing.T) {
	skipInShort(t)
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	native, infos := nativeRV64Lower(t, bare, nativeSpanCallProgram)
	joined := strings.Join(infos, "\n")
	for _, fn := range []string{"at", "mul", "ends", "scale", "dot_after", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Fatalf("%s was not lowered by the rv64 lane; diagnostics:\n%s", fn, joined)
		}
	}
	if out := runNativeRV64Bare(t, "native_rv64_span_calls", native); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("native span calls under QEMU did not exit 42:\n%s", out)
	}
	cOnly, err := New().WithSource("native.oak", nativeSpanCallProgram).WithTarget(bare).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if out := runNativeRV64Bare(t, "native_rv64_span_calls_c", NativeOutput{C: cOnly}); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("C backend under QEMU did not exit 42:\n%s", out)
	}
}

// Records and unions across the call boundary on the rv64 lane, under the
// LP64 psABI's integer calling convention: the AArch64 lane's record-ABI
// corpus — a one-chunk record in and out, a two-chunk record swapped, a
// 24-byte record in by reference and out through the caller's area whose
// address is the hidden first argument, a record argument that is a
// call's result, a record result chosen by a condition — and its union
// corpus (unions as parameters and results, matched by the caller on the
// call itself), both run under QEMU against the C backend.
func TestE2ENativeRV64RecordABIUnderQEMU(t *testing.T) {
	skipInShort(t)
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	for _, program := range []struct {
		name, source string
		functions    []string
	}{
		{"record_abi", nativeRecordABIProgram, []string{"shift", "swap", "bump", "wide_sum", "pick", "small_total", "chain", "main"}},
		{"adts", nativeADTProgram, []string{"area2", "score", "classify", "tally", "name_len", "main"}},
	} {
		t.Run(program.name, func(t *testing.T) {
			native, infos := nativeRV64Lower(t, bare, program.source)
			joined := strings.Join(infos, "\n")
			for _, fn := range program.functions {
				if !strings.Contains(joined, "asm unit "+fn+":") {
					t.Fatalf("%s was not lowered by the rv64 lane; diagnostics:\n%s", fn, joined)
				}
			}
			if out := runNativeRV64Bare(t, "native_rv64_"+program.name, native); !strings.Contains(out, "0000002a\n") {
				t.Fatalf("native bodies under QEMU did not exit 42:\n%s", out)
			}
			cOnly, err := New().WithSource("native.oak", program.source).WithTarget(bare).EmitC().Get()
			if err != nil {
				t.Fatal(err)
			}
			if out := runNativeRV64Bare(t, "native_rv64_"+program.name+"_c", NativeOutput{C: cOnly}); !strings.Contains(out, "0000002a\n") {
				t.Fatalf("C backend under QEMU did not exit 42:\n%s", out)
			}
		})
	}
}

// rv64LoopVerdicts lowers the loop corpora on the rv64 lane and returns
// the verifier's verdict per function (docs/spec/94-assembler.md §8: the
// loop recognizer and the coupling on this lane's shapes).
func rv64LoopVerdicts(t *testing.T) map[string]string {
	t.Helper()
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	verdicts := map[string]string{}
	for _, source := range []string{nativeProgram, nativeSpanProgram, nativeRV64ArrayProgram, nativeSpanCallProgram, nativeRV64Extra} {
		_, infos := nativeRV64Lower(t, bare, source)
		for _, info := range infos {
			var name string
			if n, _ := fmt.Sscanf(info, "native backend: asm unit %s", &name); n == 1 {
				verdicts[strings.TrimSuffix(name, ":")] = strings.TrimPrefix(info, "native backend: ")
			}
		}
	}
	return verdicts
}

// The verifier's loop recognizer on this lane's shapes (docs/spec/
// 94-assembler.md §8): an operand-setup instruction before the exit
// branch, `ebreak` as the trap block, byte elements addressed unscaled —
// the span loops and the tail recursion couple inductively, and the
// 64-bit product's proof exceeds the budget as it does on AArch64.
func TestE2ENativeRV64LoopVerdicts(t *testing.T) {
	verdicts := rv64LoopVerdicts(t)
	names := make([]string, 0, len(verdicts))
	for name := range verdicts {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		t.Logf("%s", verdicts[name])
	}
	for _, fn := range []string{"sum", "byte_total", "count_down"} {
		if !strings.Contains(verdicts[fn], "coupled inductively") {
			t.Errorf("%s must be proven by loop coupling: %s", fn, verdicts[fn])
		}
	}
	// fact's 64-bit product exceeded the proof budget until the identity
	// masks folded (asm/verify.go binaryTerm); it is proven by coupling now,
	// and evidence remains acceptable should the budget move.
	if !strings.Contains(verdicts["fact"], "coupled inductively") && !strings.Contains(verdicts["fact"], "agrees with its Oak body") {
		t.Errorf("fact must be proven by coupling or witnessed: %s", verdicts["fact"])
	}
	// A unit body without effects (check_all: an assert over a call) is
	// proven: neither side writes package state or a span memory
	// (docs/spec/94-assembler.md §8, unit bodies without effects).
	if !strings.Contains(verdicts["check_all"], "proven equal to its Oak body") {
		t.Errorf("check_all must be proven as a unit body without effects: %s", verdicts["check_all"])
	}
	// A load from an owned array at a data-dependent index reads the
	// elements merged under the guarded index on this lane too, the bound
	// following the index term through the scaled add
	// (docs/spec/94-assembler.md §8, frame loads at a data-dependent index).
	if !strings.Contains(verdicts["signed_bytes"], "proven equal to its Oak body") {
		t.Errorf("signed_bytes must be proven through the guarded element load: %s", verdicts["signed_bytes"])
	}
	// A caller passing a span over its own array to a looping callee is
	// proven through the summary: the callee's parameter is the array's
	// contents, its loop carries the elements (docs/spec/94-assembler.md
	// §8, span arguments over owned arrays).
	for _, fn := range []string{"filled", "squares"} {
		if !strings.Contains(verdicts[fn], "proven equal to its Oak body") || !strings.Contains(verdicts[fn], "callees taken at their Oak bodies") {
			t.Errorf("%s must be proven through its callee's summary over the owned array: %s", fn, verdicts[fn])
		}
	}
}
