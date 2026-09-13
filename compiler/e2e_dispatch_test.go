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

	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/target"
	"github.com/SCKelemen/oak/toolchain"
)

// Processor-feature dispatch (docs/spec/93-simd.md section 6): one
// program, a scalar body and an SVE realization over the scalable API,
// witnessed four ways — the interpreter with the empty feature set (the
// body), the interpreter with `sve` (the realization's Oak meaning),
// native C on this host (whose probe selects the body where SVE is
// absent, the realization where it is), and QEMU with SVE at three vector
// lengths (whose probe selects the realization) — all one answer. That
// agreement is the differential check of the slot's claim.
const dispatchProgram = `
count_sevens: (input: []u8) -> u32 dispatch { sve: count_sevens_sve } {
  i: u32 = u32(0)
  n: u32 = u32(0)
  while i < len(input) {
    n = n + (input[i] == u8(7) ? u32(1) | u32(0))
    i = i + u32(1)
  }
  n
}

count_sevens_sve: (input: []u8) -> u32 {
  remaining: u32 = len(input)
  offset: u32 = u32(0)
  total: u32 = u32(0)
  while remaining != u32(0) {
    active: simd.Active = simd.active_u8(remaining)
    chunk: simd.ScalableU8 = simd.load_active_u8(input, offset, active)
    mask: simd.ScalableU8 = simd.eq_active_u8(chunk, simd.splat_active_u8(u8(7), active), active)
    total = total + simd.count_nonzero_active_u8(mask, active)
    count: u32 = simd.count(active)
    offset = offset + count
    remaining = remaining - count
  }
  total
}

main: (): i32 {
  data: [40]u8
  i: u32 = u32(0)
  while i < u32(40) {
    data[i] = u8_trunc_u32(i % u32(8))
    i = i + u32(1)
  }
  whole: []u8 = view(&data)
  i32_bits_u32(count_sevens(whole) * u32(10) + count_sevens(subslice(whole, u32(3), u32(20))))
}
`

func TestE2EDispatchAgrees(t *testing.T) {
	previous := evaluator.Features
	defer func() { evaluator.Features = previous }()
	evaluator.Features = map[string]bool{}
	body := interpretChecked(t, dispatchProgram)
	evaluator.Features = map[string]bool{"sve": true}
	realization := interpretChecked(t, dispatchProgram)
	evaluator.Features = map[string]bool{}
	if body != realization {
		t.Fatalf("the sve realization disagrees with the body in the interpreter: %d vs %d", realization, body)
	}
	if body != 52 {
		t.Fatalf("expected 52 (5 sevens in 40, 2 in the window), got %d", body)
	}
	code, abnormal := buildAndRun(t, "dispatch", dispatchProgram)
	if abnormal || int64(code) != body {
		t.Fatalf("native run: exit (%d, abnormal %v), want %d", code, abnormal, body)
	}
	emitted, err := New().WithSource("dispatch.oak", dispatchProgram).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(emitted, "  oak_cpu_init();\n  return (int)oak_main();") {
		t.Fatalf("main does not probe before running:\n%s", emitted)
	}
}

// Under QEMU with SVE the probe selects the realization; the answer is the
// interpreter's. The C harness plays the host: it calls oak_cpu_init before
// oak_main, as a C host without an Oak main must.
func TestE2EDispatchSelectsSVEUnderQEMU(t *testing.T) {
	if _, err := exec.LookPath("qemu-system-aarch64"); err != nil {
		t.Skip("qemu-system-aarch64 not present")
	}
	tgt := target.Target{OS: target.OSFreestanding, Arch: target.ArchArm64}
	// The baseline lacks SVE: the realization is reached only through the probe.
	drv, err := toolchain.Resolve(tgt, toolchain.Options{CPU: "generic"}, nil, nil)
	if err != nil || drv.Kind != "zig" {
		t.Skipf("no zig for %s (%v)", tgt, err)
	}
	previous := evaluator.Features
	evaluator.Features = map[string]bool{}
	want := uint32(interpretChecked(t, dispatchProgram))
	evaluator.Features = previous
	code, err := New().WithSource("dispatch.oak", dispatchProgram).WithTarget(tgt).EmitC().Get()
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
	objArgs := append(append([]string{}, drv.Args...), "-std=c99", "-O2", "-ffp-contract=off", "-Wno-parentheses-equality", "-c", "-o", filepath.Join(dir, "program.o"), oakC)
	if out, err := exec.Command(drv.Path, objArgs...).CombinedOutput(); err != nil {
		t.Fatalf("oak object at the generic baseline: %v\n%s", err, out)
	}
	harness := "extern int oak_main(void);\nextern void oak_cpu_init(void);\n" +
		"static void putc_(char c) { *(volatile unsigned int *)0x09000000 = (unsigned)c; }\n" +
		"static void puthex(unsigned v) { for (int i = 28; i >= 0; i -= 4) putc_(\"0123456789abcdef\"[(v >> i) & 15]); putc_('\\n'); }\n" +
		"void cmain(void) { oak_cpu_init(); puthex((unsigned)oak_main());\n" +
		"  register unsigned long x0 __asm__(\"x0\") = 0x18; register unsigned long x1 __asm__(\"x1\") = 0x20026;\n" +
		"  __asm__ volatile(\"hlt #0xf000\" : : \"r\"(x0), \"r\"(x1) : \"memory\"); for (;;) {} }\n" +
		"__asm__(\".section .text.init\\n.globl _start\\n_start:\\n  mov x0, #(3 << 20)\\n  orr x0, x0, #(3 << 16)\\n  msr cpacr_el1, x0\\n  mov x0, #0xf\\n  msr S3_0_C1_C2_0, x0\\n  isb\\n  ldr x0, =_stack_top\\n  mov sp, x0\\n  bl cmain\\n1: b 1b\\n\");\n"
	harnessC := write("harness.c", harness)
	link := write("link.ld", "ENTRY(_start)\nSECTIONS {\n  . = 0x40000000;\n  .text : { *(.text.init) *(.text*) }\n  .rodata : { *(.rodata*) }\n  .data : { *(.data*) }\n  .bss : { *(.bss*) }\n  . = ALIGN(16);\n  . += 0x20000;\n  _stack_top = .;\n}\n")
	image := filepath.Join(dir, "image.elf")
	linkArgs := []string{"cc", "--target=" + tgt.ZigTriple(), "-mcpu=generic", "-ffreestanding", "-nostartfiles", "-fno-unwind-tables", "-fno-asynchronous-unwind-tables", "-O1", "-Wl,--build-id=none", "-T", link, "-o", image, harnessC, filepath.Join(dir, "program.o")}
	if out, err := exec.Command(drv.Path, linkArgs...).CombinedOutput(); err != nil {
		t.Fatalf("link: %v\n%s", err, out)
	}
	// The realization must be in the image for the probe to reach it.
	if out, err := exec.Command("nm", image).CombinedOutput(); err == nil && !bytes.Contains(out, []byte("oak_count_sevens_sve")) {
		t.Fatalf("the sve realization is not in the image:\n%s", out)
	}
	// (A processor without SVE is the host run of TestE2EDispatchAgrees:
	// this harness's _start writes ZCR_EL1, which such a processor lacks.)
	for _, cpu := range []string{"max,sve-max-vq=1", "max,sve-max-vq=2", "max,sve-max-vq=4"} {
		ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
		cmd := exec.CommandContext(ctx, "qemu-system-aarch64", "-M", "virt", "-cpu", cpu, "-semihosting-config", "enable=on,target=native", "-nographic", "-monitor", "none", "-kernel", image)
		var out bytes.Buffer
		cmd.Stdout, cmd.Stderr = &out, &out
		_ = cmd.Run()
		cancel()
		if !strings.Contains(out.String(), fmt.Sprintf("%08x\n", want)) {
			t.Fatalf("-cpu %s: expected %08x (the interpreter's value):\n%s", cpu, want, out.String())
		}
	}
}
