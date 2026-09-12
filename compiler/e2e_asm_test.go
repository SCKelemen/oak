package compiler

import (
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"testing"
)

// The typed assembler (docs/spec/94-assembler.md): asm units provide the
// bodies of definition-less Oak declarations, the seam checker enforces
// bindings/widths/clobbers/flags/frame/alignment, and the C backend emits
// top-level assembly blocks. The host is AArch64, so these execute natively.

func requireArm64Host(t *testing.T) {
	t.Helper()
	if runtime.GOARCH != "arm64" {
		t.Skip("asm units execute natively only on an AArch64 host")
	}
}

func TestE2EAsmAdd(t *testing.T) {
	requireArm64Host(t)
	comp := New().WithSource("asmadd.oak", `
add_asm: (left, right: u32) -> u32

main: (): i32 {
  assert(add_asm(u32(40), u32(2)) == u32(42))
  42
}
`).WithAsmUnit("add.arm64.oakasm", `
add_asm: (left, right: u32) -> u32 = {
  bind w0 = left
  bind w1 = right
  add w0, w0, w1
  ret
}
`)
	output, err := comp.EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, want := range []string{"OAK_ASM_SYMBOL(oak_add_asm)", "add w0, w0, w1", "u32 oak_add_asm( u32 left, u32 right );"} {
		if !strings.Contains(output, want) {
			t.Fatalf("emitted C lacks %q:\n%s", want, output)
		}
	}
	_, code, abnormal := buildAndRunFrom(t, "asmadd", comp)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// A declared frame, pre/post-index pairs, and the static sp displacement:
// the trap-frame shape (save x0–x17 as pairs, restore, return).
func TestE2EAsmFrameSaveRestore(t *testing.T) {
	requireArm64Host(t)
	comp := New().WithSource("asmframe.oak", `
swap_sum: (a, b: u64) -> u64
save_all: (seed: u64) -> u64

main: (): i32 {
  assert(swap_sum(u64(40), u64(2)) == u64(42))
  assert(save_all(u64(42)) == u64(42))
  42
}
`).WithAsmUnit("frame.arm64.oakasm", `
swap_sum: (a, b: u64) -> u64 = {
  bind x0 = a
  bind x1 = b
  frame 16
  stp x0, x1, [sp, #-16]!
  ldp x1, x0, [sp], #16
  add x0, x0, x1
  ret
}

save_all: (seed: u64) -> u64 = {
  bind x0 = seed
  clobber x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17
  frame 160
  mov x1, #1
  mov x2, #2
  mov x3, #3
  mov x4, #4
  mov x5, #5
  mov x6, #6
  mov x7, #7
  mov x8, #8
  mov x9, #9
  mov x10, #10
  mov x11, #11
  mov x12, #12
  mov x13, #13
  mov x14, #14
  mov x15, #15
  mov x16, #16
  mov x17, #17
  sub sp, sp, #160
  stp x0, x1, [sp, #0]
  stp x2, x3, [sp, #16]
  stp x4, x5, [sp, #32]
  stp x6, x7, [sp, #48]
  stp x8, x9, [sp, #64]
  stp x10, x11, [sp, #80]
  stp x12, x13, [sp, #96]
  stp x14, x15, [sp, #112]
  stp x16, x17, [sp, #128]
  mov x0, #0
  ldp x16, x17, [sp, #128]
  ldp x14, x15, [sp, #112]
  ldp x12, x13, [sp, #96]
  ldp x10, x11, [sp, #80]
  ldp x8, x9, [sp, #64]
  ldp x6, x7, [sp, #48]
  ldp x4, x5, [sp, #32]
  ldp x2, x3, [sp, #16]
  ldp x0, x1, [sp, #0]
  add sp, sp, #160
  ret
}
`)
	_, code, abnormal := buildAndRunFrom(t, "asmframe", comp)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// Flags dataflow and label displacement merging through a loop.
func TestE2EAsmFlagsLoop(t *testing.T) {
	requireArm64Host(t)
	comp := New().WithSource("asmloop.oak", `
count_down: (n: u32) -> u32

main: (): i32 {
  assert(count_down(u32(42)) == u32(42))
  assert(count_down(u32(0)) == u32(0))
  42
}
`).WithAsmUnit("loop.arm64.oakasm", `
count_down: (n: u32) -> u32 = {
  bind w0 = n
  clobber w9
  mov w9, #0
loop:
  cmp w0, #0
  b.eq done
  sub w0, w0, #1
  add w9, w9, #1
  b loop
done:
  mov w0, w9
  ret
}
`)
	_, code, abnormal := buildAndRunFrom(t, "asmloop", comp)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// The exception vector table: 2 KiB-aligned, sixteen 128-byte entries,
// each entry's extent proven to fit its slot; eret under the system
// capability. Assembled (not executed — EL2 instructions) by cc -c.
func TestE2EAsmVectorTableAssembles(t *testing.T) {
	requireArm64Host(t)
	var unit strings.Builder
	unit.WriteString("vectors: () -> never = {\n  system\n  align 2048\n")
	for i := 0; i < 16; i++ {
		unit.WriteString("  align 128\n  eret\n")
	}
	unit.WriteString("}\n")
	comp := New().WithSource("vectors.oak", `
vectors: () -> never

main: (): i32 {
  42
}
`).WithAsmUnit("vectors.arm64.oakasm", unit.String())
	output, err := comp.EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if !strings.Contains(output, ".balign 2048") || strings.Count(output, ".balign 128") != 16 {
		t.Fatalf("vector table alignment not emitted as expected:\n%s", output)
	}
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("no C compiler on PATH")
	}
	dir := t.TempDir()
	cPath := filepath.Join(dir, "vectors.c")
	if err := os.WriteFile(cPath, []byte(output), 0o644); err != nil {
		t.Fatal(err)
	}
	if combined, err := exec.Command(cc, "-std=c99", "-c", cPath, "-o", filepath.Join(dir, "vectors.o")).CombinedOutput(); err != nil {
		t.Fatalf("cc -c failed: %v\n%s\n--- generated C ---\n%s", err, combined, output)
	}
}

// Body-less declarations without a unit, and units without declarations,
// are rejected at the asm gate.
func TestAsmStitchingRejections(t *testing.T) {
	_, err := New().WithSource("nounit.oak", "lonely: (x: u32) -> u32\nmain: (): i32 = 0\n").EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "no asm unit provides its body") {
		t.Fatalf("body-less declaration without a unit must be rejected, got %v", err)
	}
	_, err = New().WithSource("nodecl.oak", "main: (): i32 = 0\n").
		WithAsmUnit("orphan.arm64.oakasm", "orphan: (x: u32) -> u32 = {\n  bind w0 = x\n  ret\n}\n").EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "has no Oak declaration") {
		t.Fatalf("unit function without a declaration must be rejected, got %v", err)
	}
	_, err = New().WithSource("mismatch.oak", "f: (x: u32) -> u32\nmain: (): i32 = 0\n").
		WithAsmUnit("f.arm64.oakasm", "f: (x: u64) -> u64 = {\n  bind x0 = x\n  ret\n}\n").EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "signature mismatch") {
		t.Fatalf("signature mismatch must be rejected, got %v", err)
	}
}

// Typed pointer memory: a handler reads its caller's span under a
// dominating length guard — the trap-frame-through-a-parameter shape.
func TestE2EAsmSpanParameter(t *testing.T) {
	requireArm64Host(t)
	comp := New().WithSource("asmspan.oak", `
first_two: (frame: [*]u64) -> u64
byte_sum: (bytes: []u8) -> u64

main: (): i32 {
  regs: [4]u64
  regs[u32(0)] = u64(40)
  regs[u32(1)] = u64(2)
  sp: [*]u64 = span(&regs)
  assert(first_two(sp) == u64(42))

  data: [4]u8
  data[u32(0)] = u8(42)
  v: []u8 = view(&data)
  assert(byte_sum(v) == u64(42))
  42
}
`).WithAsmUnit("span.arm64.oakasm", `
first_two: (frame: [*]u64) -> u64 = {
  bind x0, w1 = frame
  clobber x9
  cmp w1, #2
  b.lo short
  ldr x9, [x0, #8]
  ldr x0, [x0]
  add x0, x0, x9
  ret
short:
  mov x0, #0
  ret
}

byte_sum: (bytes: []u8) -> u64 = {
  bind x0, w1 = bytes
  clobber x9
  cmp w1, #4
  b.lo short
  ldr w9, [x0]
  mov x0, x9
  ret
short:
  mov x0, #0
  ret
}
`)
	_, code, abnormal := buildAndRunFrom(t, "asmspan", comp)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// Callee-saved obligations: x19/x20 saved before use and restored before
// ret; a bl with the link register saved in the frame, calling an Oak
// function and returning its result.
func TestE2EAsmCalleeSavedAndCall(t *testing.T) {
	requireArm64Host(t)
	comp := New().WithSource("asmsaved.oak", `
scratch: (a: u64) -> u64
caller: (a: u64) -> u64
helper: (a: u64): u64 = a + u64(2)

main: (): i32 {
  assert(scratch(u64(0)) == u64(42))
  assert(caller(u64(40)) == u64(42))
  42
}
`).WithAsmUnit("saved.arm64.oakasm", `
scratch: (a: u64) -> u64 = {
  bind x0 = a
  clobber x19, x20
  frame 16
  stp x19, x20, [sp, #-16]!
  mov x19, #40
  mov x20, #2
  add x0, x19, x20
  ldp x19, x20, [sp], #16
  ret
}

caller: (a: u64) -> u64 = {
  bind x0 = a
  clobber x29, x30
  frame 16
  stp x29, x30, [sp, #-16]!
  bl helper
  ldp x29, x30, [sp], #16
  ret
}
`)
	_, code, abnormal := buildAndRunFrom(t, "asmsaved", comp)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// An Oak fallback body beside the asm unit: the asm realizes the signature
// on AArch64, the Oak body everywhere else (and under the portable
// lowering) — executed both ways on this host.
func TestE2EAsmFallbackBody(t *testing.T) {
	requireArm64Host(t)
	comp := New().WithSource("asmfallback.oak", `
add_asm: (left, right: u32) -> u32 = left + right

main: (): i32 {
  assert(add_asm(u32(40), u32(2)) == u32(42))
  42
}
`).WithAsmUnit("add.arm64.oakasm", `
add_asm: (left, right: u32) -> u32 = {
  bind w0 = left
  bind w1 = right
  add w0, w0, w1
  ret
}
`)
	output, err := comp.EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if !strings.Contains(output, "#if !(defined(__aarch64__)) || defined(OAK_PORTABLE_INTRINSICS)") || strings.Contains(output, "#error") {
		t.Fatalf("fallback body not emitted under the complementary condition:\n%s", output)
	}
	for _, flags := range [][]string{nil, {"-DOAK_PORTABLE_INTRINSICS"}} {
		_, code, abnormal := buildAndRunFrom(t, "asmfallback", comp, flags...)
		if abnormal || code != 42 {
			t.Fatalf("flags %v: exit = (%d, abnormal=%v), want 42", flags, code, abnormal)
		}
	}
}
