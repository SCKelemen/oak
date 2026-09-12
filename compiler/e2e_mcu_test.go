package compiler

import (
	"bytes"
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/target"
	"github.com/SCKelemen/oak/toolchain"
)

// Microcontroller targets (docs/spec/90-backend.md §2a): an Oak package
// compiled as a freestanding ILP32 object for a Cortex-M3 and for an RV32
// core, linked by the resolved cross compiler with a bare-metal harness
// that calls oak_main and prints its result over the machine's UART, and
// executed under qemu-system-arm (-M mps2-an385) and qemu-system-riscv32
// (-M virt). Skips without zig and the emulators.

const mcuOak = `
import(std)
import("time")
import("timehost")

sum: (v: []u32) -> u32 {
  total: u32 = u32(0)
  i: u32 = u32(0)
  while i < len(v) {
    total = total + v[i]
    i = i + u32(1)
  }
  total
}

fill: (s: [*]u32) {
  s[0] = u32(5)
  s[3] = u32(11)
  s[7] = u32(26)
}

scale: (x: f32) -> f32 {
  x * f32(1.5)
}

main: (): i32 {
  data: [8]u32
  fill(span(&data))
  total: u32 = sum(view(&data))
  assert(scale(f32(2.0)) == f32(3.0))
  // The host's clocks through the freestanding boundary (timehost): the
  // harness advances a counter on every read, so the monotonic reading
  // moves and never backwards.
  source: [1]time.TimeSource
  timehost.timehost_source(span(&source))
  first: time.Duration = time.time_monotonic(span(&source))
  refreshed: Bool = timehost.timehost_refresh(span(&source))
  assert(refreshed)
  second: time.Duration = time.time_monotonic(span(&source))
  assert(second.nanos >= first.nanos)
  i32_bits_u32(total)
}
`

// mcuFailOak trips an assertion: the message must reach the harness's
// oak_host_write before the trap.
const mcuFailOak = `
main: (): i32 {
  x: u32 = u32(7)
  assert(x == u32(8))
  0
}
`

type mcuMachine struct {
	tgt      target.Target
	cpu      string
	qemu     string
	machine  []string
	uart     string // the UART data register
	uartInit string // C statements enabling the UART, if the device needs it
	exitCode string // the harness's exit sequence, as C
	startAsm string // _start / vector table
	origin   string // link address
	extra    []string
}

func TestE2EMicrocontrollerTargetsUnderQEMU(t *testing.T) {
	skipInShort(t)
	machines := []mcuMachine{
		{
			tgt: target.Target{OS: target.OSFreestanding, Arch: target.ArchArm}, cpu: "cortex_m3",
			qemu: "qemu-system-arm", machine: []string{"-M", "mps2-an385", "-cpu", "cortex-m3", "-semihosting-config", "enable=on,target=native"},
			uart: "0x40004000",
			// CMSDK APB UART: the transmitter is enabled through CTRL (+8, bit 0).
			uartInit: `*(volatile unsigned *)0x40004008 = 1;`,
			// Semihosting SYS_EXIT (0x18) with ADP_Stopped_ApplicationExit.
			exitCode: `register unsigned r0 __asm__("r0") = 0x18; register unsigned r1 __asm__("r1") = 0x20026; __asm__ volatile("bkpt #0xAB" : : "r"(r0), "r"(r1) : "memory");`,
			startAsm: ".section .vectors,\"a\"\n.word _stack_top\n.word _start\n.text\n.thumb_func\n.globl _start\n_start:\n  bl cmain\n1: b 1b\n",
			origin:   "0x00000000",
		},
		{
			tgt: target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv32}, cpu: "generic_rv32",
			qemu: "qemu-system-riscv32", machine: []string{"-M", "virt", "-bios", "none"},
			uart:     "0x10000000",
			exitCode: `*(volatile unsigned *)0x100000 = 0x5555; /* sifive_test: exit 0 */`,
			startAsm: ".section .text.init\n.globl _start\n_start:\n  la sp, _stack_top\n  call cmain\n1: j 1b\n",
			origin:   "0x80000000",
		},
	}
	for _, m := range machines {
		t.Run(m.tgt.String(), func(t *testing.T) {
			if _, err := exec.LookPath(m.qemu); err != nil {
				t.Skipf("%s not present", m.qemu)
			}
			drv, err := toolchain.Resolve(m.tgt, toolchain.Options{CPU: m.cpu}, nil, nil)
			if err != nil || drv.Kind != "zig" {
				t.Skipf("no zig for %s (%v)", m.tgt, err)
			}
			for _, program := range []struct{ name, source, want string }{
				{"mcu.oak", mcuOak, "0000002a\n"},
				{"fail.oak", mcuFailOak, "oak: assertion failed at fail.oak:4\n"},
			} {
				// Library imports (time, timehost) resolve through a module root.
				comp := New().WithPackageDir(writeModule(t, map[string]string{"oak.mod": "module example.com/mcu\noak 0.1.0\n", program.name: program.source})).WithTarget(m.tgt)
				code, err := comp.EmitC().Get()
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
				oakC := write("program.c", code)
				// The Oak object exactly as `oak build -target` produces it.
				objArgs := append(append([]string{}, drv.Args...), "-std=c99", "-O1", "-ffp-contract=off", "-c", "-o", filepath.Join(dir, "program.o"), oakC)
				if out, err := exec.Command(drv.Path, objArgs...).CombinedOutput(); err != nil {
					t.Fatalf("oak object: %v\n%s", err, out)
				}
				harness := "extern int oak_main(void);\n" +
					"static void putc_(char c) { *(volatile unsigned char *)" + m.uart + " = c; }\n" +
					// The freestanding host boundary: diagnostics over the UART,
					// the two clocks over a counter that advances per read.
					"long long oak_host_write(long long fd, const unsigned char *buf, unsigned long len) { (void)fd; for (unsigned long i = 0; i < len; i++) putc_((char)buf[i]); return (long long)len; }\n" +
					"static long long ticks = 1000;\n" +
					"long long oak_time_host_realtime_nanos(void) { return 1700000000000000000LL + ticks; }\n" +
					"long long oak_time_host_monotonic_nanos(void) { ticks += 250; return ticks; }\n" +
					"static void puthex(unsigned v) { for (int i = 28; i >= 0; i -= 4) putc_(\"0123456789abcdef\"[(v >> i) & 15]); putc_('\\n'); }\n" +
					"void cmain(void) { " + m.uartInit + " puthex((unsigned)oak_main()); " + m.exitCode + " for (;;) {} }\n" +
					"__asm__(" + quoteAsm(m.startAsm) + ");\n"
				harnessC := write("harness.c", harness)
				// The unwind index and note sections are discarded so the vector
				// table is the first word of the image, where a Cortex-M reads it.
				link := write("link.ld", "ENTRY(_start)\nSECTIONS {\n  /DISCARD/ : { *(.ARM.exidx*) *(.ARM.extab*) *(.note*) *(.comment) }\n  . = "+m.origin+";\n  .vectors : { KEEP(*(.vectors)) }\n  .text : { *(.text.init) *(.text*) }\n  .rodata : { *(.rodata*) *(.srodata*) }\n  .data : { *(.data*) *(.sdata*) }\n  .bss : { *(.bss*) *(.sbss*) }\n  . = ALIGN(16);\n  . += 0x8000;\n  _stack_top = .;\n}\n")
				image := filepath.Join(dir, "image.elf")
				// The harness links the object the way an OS or firmware would:
				// no libc and no startup files (the harness is the startup), but
				// the compiler's runtime library — compiler-rt from zig, libgcc
				// from a GNU toolchain — for the __aeabi_*, __udiv*, and memset
				// builtins the object references.
				linkArgs := []string{"cc", "--target=" + m.tgt.ZigTriple(), "-mcpu=" + m.cpu, "-ffreestanding", "-nostartfiles", "-fno-unwind-tables", "-fno-asynchronous-unwind-tables", "-O1", "-Wl,--build-id=none", "-T", link, "-o", image, harnessC, filepath.Join(dir, "program.o")}
				if out, err := exec.Command(drv.Path, linkArgs...).CombinedOutput(); err != nil {
					t.Fatalf("link: %v\n%s", err, out)
				}
				ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
				defer cancel()
				args := append(append([]string{}, m.machine...), "-nographic", "-monitor", "none", "-kernel", image)
				cmd := exec.CommandContext(ctx, m.qemu, args...)
				var out bytes.Buffer
				cmd.Stdout, cmd.Stderr = &out, &out
				_ = cmd.Run() // the exit path is the harness's; the output is the verdict
				if !strings.Contains(out.String(), program.want) {
					t.Fatalf("%s: %s did not print %q:\n%s", program.name, m.qemu, program.want, out.String())
				}
			}
		})
	}
}

// quoteAsm spells assembly text as a C string literal.
func quoteAsm(text string) string {
	return `"` + strings.ReplaceAll(strings.ReplaceAll(text, `"`, `\"`), "\n", `\n`) + `"`
}

// timehost compiles for hosted targets too (the hooks are then the
// program's to link); the host boundary is a compile-time fact, not a
// target-specific one.
func TestTimehostCompilesEverywhere(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": "module example.com/mcu\noak 0.1.0\n", "main.oak": mcuOak})
	for _, tgt := range target.Supported() {
		code, err := New().WithPackageDir(root).WithTarget(tgt).EmitC().Get()
		if err != nil {
			t.Fatalf("%s: %v", tgt, err)
		}
		for _, want := range []string{"oak_time_host_realtime_nanos", "oak_time_host_monotonic_nanos"} {
			if !strings.Contains(code, want) {
				t.Fatalf("%s: C lacks the hook %s", tgt, want)
			}
		}
		if !strings.Contains(code, "oak_host_write") {
			t.Fatalf("%s: C lacks the host boundary block", tgt)
		}
	}
}
