package compiler

import (
	"bytes"
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/target"
	"github.com/SCKelemen/oak/toolchain"
)

// The RISC-V Vector realization of the fixed simd vectors
// (docs/spec/93-simd.md §1.4, §5): the same programs the NEON and portable
// witnesses run — every byte-classification and floating-point vector
// operation folded into one checksum — are compiled for riscv64 with the V
// extension, linked with the bare-metal harness, and run under
// qemu-system-riscv64 at two hardware vector lengths; each run must print
// the interpreter's value. Fixed 128-bit vectors run unchanged on every
// VLEN >= 128, and the run at 256 shows it. Skips without zig or QEMU.
func TestE2ERVVAgreesWithInterpreter(t *testing.T) {
	if _, err := exec.LookPath("qemu-system-riscv64"); err != nil {
		t.Skip("qemu-system-riscv64 not present")
	}
	tgt := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	drv, err := toolchain.Resolve(tgt, toolchain.Options{CPU: "generic_rv64+m+v"}, nil, nil)
	if err != nil || drv.Kind != "zig" {
		t.Skipf("no zig for %s (%v)", tgt, err)
	}
	for _, program := range []struct{ name, source string }{{"simd_bytes", simdBytesProgram}, {"simd_float", floatSimdProgram}, {"scalable", scalableProgram}} {
		t.Run(program.name, func(t *testing.T) {
			want := uint32(interpretChecked(t, program.source))
			code, err := New().WithSource(program.name+".oak", program.source).WithTarget(tgt).EmitC().Get()
			if err != nil {
				t.Fatal(err)
			}
			if !strings.Contains(code, "__riscv_vle") && !strings.Contains(code, "__riscv_vsetvl") {
				t.Fatal("the emitted C carries no RVV realization")
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
			objArgs := append(append([]string{}, drv.Args...), "-std=c99", "-O2", "-ffp-contract=off", "-Wno-parentheses-equality", "-c", "-o", filepath.Join(dir, "program.o"), oakC)
			if out, err := exec.Command(drv.Path, objArgs...).CombinedOutput(); err != nil {
				t.Fatalf("oak object with V: %v\n%s", err, out)
			}
			// mstatus.FS and mstatus.VS both Initial: the vector unit and
			// the FPU are off at reset.
			harness := "extern unsigned int oak_main(void);\n" +
				"static void putc_(char c) { *(volatile unsigned char *)0x10000000 = c; }\n" +
				"static void puthex(unsigned v) { for (int i = 28; i >= 0; i -= 4) putc_(\"0123456789abcdef\"[(v >> i) & 15]); putc_('\\n'); }\n" +
				"void cmain(void) { puthex(oak_main()); *(volatile unsigned *)0x100000 = 0x5555; for (;;) {} }\n" +
				"__asm__(\".section .text.init\\n.globl _start\\n_start:\\n  li t0, 0x6600\\n  csrs mstatus, t0\\n  la sp, _stack_top\\n  call cmain\\n1: j 1b\\n\");\n"
			harnessC := write("harness.c", harness)
			link := write("link.ld", "ENTRY(_start)\nSECTIONS {\n  . = 0x80000000;\n  .text : { *(.text.init) *(.text*) }\n  .rodata : { *(.rodata*) *(.srodata*) }\n  .data : { *(.data*) *(.sdata*) }\n  .bss : { *(.bss*) *(.sbss*) }\n  . = ALIGN(16);\n  . += 0x20000;\n  _stack_top = .;\n}\n")
			image := filepath.Join(dir, "image.elf")
			linkArgs := []string{"cc", "--target=" + tgt.ZigTriple(), "-mcpu=generic_rv64+m+v", "-mcmodel=medany", "-ffreestanding", "-nostartfiles", "-fno-unwind-tables", "-fno-asynchronous-unwind-tables", "-O1", "-Wl,--build-id=none", "-T", link, "-o", image, harnessC, filepath.Join(dir, "program.o")}
			if out, err := exec.Command(drv.Path, linkArgs...).CombinedOutput(); err != nil {
				t.Fatalf("link: %v\n%s", err, out)
			}
			for _, vlen := range []int{128, 256} {
				ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
				cmd := exec.CommandContext(ctx, "qemu-system-riscv64", "-M", "virt", "-cpu", fmt.Sprintf("rv64,v=true,vlen=%d", vlen), "-bios", "none", "-nographic", "-monitor", "none", "-kernel", image)
				var out bytes.Buffer
				cmd.Stdout, cmd.Stderr = &out, &out
				_ = cmd.Run()
				cancel()
				if !strings.Contains(out.String(), fmt.Sprintf("%08x\n", want)) {
					t.Fatalf("VLEN %d: expected %08x (the interpreter's value):\n%s", vlen, want, out.String())
				}
			}
		})
	}
}
