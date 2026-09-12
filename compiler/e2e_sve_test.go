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

// The SVE realization of the scalable API (docs/spec/93-simd.md §1.4, §4,
// §5): the extent-independence program the portable and RVV witnesses run
// is compiled for arm64 with `-cpu generic+sve`, linked with a bare-metal
// harness that enables SVE at EL1 (CPACR_EL1.ZEN and ZCR_EL1.LEN), and run
// under qemu-system-aarch64 at three hardware vector lengths — 128, 256,
// and 512 bits — selected with the `sve-max-vq` knob; each run must print
// the interpreter's value. The fixed 128-bit simd programs run alongside
// through their NEON realization, which the SVE processor keeps. Skips
// without zig or QEMU.
func TestE2ESVEAgreesWithInterpreter(t *testing.T) {
	if _, err := exec.LookPath("qemu-system-aarch64"); err != nil {
		t.Skip("qemu-system-aarch64 not present")
	}
	tgt := target.Target{OS: target.OSFreestanding, Arch: target.ArchArm64}
	drv, err := toolchain.Resolve(tgt, toolchain.Options{CPU: "generic+sve"}, nil, nil)
	if err != nil || drv.Kind != "zig" {
		t.Skipf("no zig for %s (%v)", tgt, err)
	}
	for _, program := range []struct{ name, source, marker string }{{"scalable", scalableProgram, "svwhilelt_b8"}, {"masked", maskedProgram, "svcntp_b8"}, {"simd_bytes", simdBytesProgram, "vld1q_u8"}, {"simd_float", floatSimdProgram, "vld1q_f32"}} {
		t.Run(program.name, func(t *testing.T) {
			want := uint32(interpretChecked(t, program.source))
			code, err := New().WithSource(program.name+".oak", program.source).WithTarget(tgt).EmitC().Get()
			if err != nil {
				t.Fatal(err)
			}
			if !strings.Contains(code, program.marker) {
				t.Fatalf("the emitted C carries no %s realization", program.marker)
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
				t.Fatalf("oak object with SVE: %v\n%s", err, out)
			}
			// The PL011 UART of QEMU's virt machine at 0x09000000; exit
			// through semihosting SYS_EXIT with ADP_Stopped_ApplicationExit.
			// _start enables FP/SIMD and SVE traps off (CPACR_EL1.FPEN and
			// ZEN both 0b11) and lets the hardware pick the largest vector
			// length (ZCR_EL1.LEN = 15) before calling the C harness.
			harness := "extern unsigned int oak_main(void);\n" +
				"static void putc_(char c) { *(volatile unsigned int *)0x09000000 = (unsigned)c; }\n" +
				"static void puthex(unsigned v) { for (int i = 28; i >= 0; i -= 4) putc_(\"0123456789abcdef\"[(v >> i) & 15]); putc_('\\n'); }\n" +
				"void cmain(void) { puthex(oak_main());\n" +
				"  register unsigned long x0 __asm__(\"x0\") = 0x18; register unsigned long x1 __asm__(\"x1\") = 0x20026;\n" +
				"  __asm__ volatile(\"hlt #0xf000\" : : \"r\"(x0), \"r\"(x1) : \"memory\"); for (;;) {} }\n" +
				"__asm__(\".section .text.init\\n.globl _start\\n_start:\\n  mov x0, #(3 << 20)\\n  orr x0, x0, #(3 << 16)\\n  msr cpacr_el1, x0\\n  mov x0, #0xf\\n  msr S3_0_C1_C2_0, x0\\n  isb\\n  ldr x0, =_stack_top\\n  mov sp, x0\\n  bl cmain\\n1: b 1b\\n\");\n"
			harnessC := write("harness.c", harness)
			link := write("link.ld", "ENTRY(_start)\nSECTIONS {\n  . = 0x40000000;\n  .text : { *(.text.init) *(.text*) }\n  .rodata : { *(.rodata*) }\n  .data : { *(.data*) }\n  .bss : { *(.bss*) }\n  . = ALIGN(16);\n  . += 0x20000;\n  _stack_top = .;\n}\n")
			image := filepath.Join(dir, "image.elf")
			linkArgs := []string{"cc", "--target=" + tgt.ZigTriple(), "-mcpu=generic+sve", "-ffreestanding", "-nostartfiles", "-fno-unwind-tables", "-fno-asynchronous-unwind-tables", "-O1", "-Wl,--build-id=none", "-T", link, "-o", image, harnessC, filepath.Join(dir, "program.o")}
			if out, err := exec.Command(drv.Path, linkArgs...).CombinedOutput(); err != nil {
				t.Fatalf("link: %v\n%s", err, out)
			}
			for _, vq := range []int{1, 2, 4} {
				ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
				cmd := exec.CommandContext(ctx, "qemu-system-aarch64", "-M", "virt", "-cpu", fmt.Sprintf("max,sve-max-vq=%d", vq), "-semihosting-config", "enable=on,target=native", "-nographic", "-monitor", "none", "-kernel", image)
				var out bytes.Buffer
				cmd.Stdout, cmd.Stderr = &out, &out
				_ = cmd.Run()
				cancel()
				if !strings.Contains(out.String(), fmt.Sprintf("%08x\n", want)) {
					t.Fatalf("SVE %d bits: expected %08x (the interpreter's value):\n%s", 128*vq, want, out.String())
				}
			}
		})
	}
}
