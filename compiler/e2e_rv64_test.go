package compiler

import (
	"encoding/binary"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/target"
)

// rv64Linux is the target whose lane the units below belong to
// (docs/spec/90-backend.md §2a): on any other target they would yield to
// their Oak bodies or fail closed.
var rv64Linux = target.Target{OS: target.OSLinux, Arch: target.ArchRiscv64}

// An rv64 unit (docs/spec/94-assembler.md §9) stitches like an AArch64
// one: the `.rv64.oakasm` path selects the lane, the seam checker's
// findings reject at compile time, the C carries the unit under the
// `__riscv` guard (fail closed elsewhere), and the companion object is an
// EM_RISCV ELF. Execution is covered by the assembler's QEMU differential.

const rv64PickOak = `
pick_rv: (x, y: u64) -> u64

main: (): i32 {
  0
}
`

const rv64PickUnit = `
pick_rv: (x, y: u64) -> u64 = {
  bind a0 = x
  bind a1 = y
  bltu a0, a1, small
  mv a0, a1
small:
  ret
}
`

func TestE2ERV64UnitStitches(t *testing.T) {
	comp := New().WithSource("pick.oak", rv64PickOak).WithAsmUnit("pick.rv64.oakasm", rv64PickUnit).WithTarget(rv64Linux)
	output, err := comp.EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"#if (defined(__riscv) && (__riscv_xlen == 64)) && !defined(OAK_PORTABLE_INTRINSICS)", `"  bltu a0, a1, 1f\n"`, "requires an RV64 target"} {
		if !strings.Contains(output, want) {
			t.Errorf("C lacks %q", want)
		}
	}
	native, err := comp.EmitNative(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	if machine := binary.LittleEndian.Uint16(native.Object[18:20]); machine != 243 {
		t.Fatalf("companion object e_machine %d, want EM_RISCV (243)", machine)
	}
	if !strings.Contains(native.C, "encoded by the Oak assembler into the companion object") {
		t.Error("native C lacks the extern prototype comment")
	}
	if _, err := comp.EmitNative(asm.MachO).Get(); err == nil || !strings.Contains(err.Error(), "ELF") {
		t.Fatalf("Mach-O for an rv64 unit: %v", err)
	}
}

func TestE2ERV64CheckerFindingsReject(t *testing.T) {
	bad := strings.Replace(rv64PickUnit, "  mv a0, a1\n", "  mv t0, a1\n  mv a0, t0\n", 1)
	_, err := New().WithSource("pick.oak", rv64PickOak).WithAsmUnit("pick.rv64.oakasm", bad).WithTarget(rv64Linux).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "write to t0") {
		t.Fatalf("checker finding not reported: %v", err)
	}
}

// With an Oak fallback body, the verifier proves the rv64 unit against it
// and a disagreeing body rejects.
func TestE2ERV64VerifiesAgainstFallback(t *testing.T) {
	source := `
umin_rv: (x, y: u64) -> u64 {
  x < y ? x | y
}

main: (): i32 {
  0
}
`
	unit := strings.ReplaceAll(rv64PickUnit, "pick_rv", "umin_rv")
	if _, err := New().WithSource("umin.oak", source).WithAsmUnit("umin.rv64.oakasm", unit).WithTarget(rv64Linux).EmitC().Get(); err != nil {
		t.Fatal(err)
	}
	wrong := strings.Replace(source, "x < y ? x | y", "x < y ? y | x", 1)
	_, err := New().WithSource("umin.oak", wrong).WithAsmUnit("umin.rv64.oakasm", unit).WithTarget(rv64Linux).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "disagrees") {
		t.Fatalf("mismatch not reported: %v", err)
	}
}

// An F/D unit binds the LP64D contract; a hosted RISC-V target carries it
// (the companion object already declares lp64d), the freestanding one is
// refused with the alternative named.
func TestE2ERV64FloatUnitNeedsLP64D(t *testing.T) {
	source := "fma_rv: (a, b, c: f64) -> f64\n\nmain: (): i32 {\n  0\n}\n"
	unit := "fma_rv: (a, b, c: f64) -> f64 = {\n  bind fa0 = a\n  bind fa1 = b\n  bind fa2 = c\n  fmadd.d fa0, fa0, fa1, fa2\n  ret\n}\n"
	if _, err := New().WithSource("fma.oak", source).WithAsmUnit("fma.rv64.oakasm", unit).WithTarget(rv64Linux).EmitC().Get(); err != nil {
		t.Fatalf("linux/riscv64: %v", err)
	}
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	_, err := New().WithSource("fma.oak", source).WithAsmUnit("fma.rv64.oakasm", unit).WithTarget(bare).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "LP64D") {
		t.Fatalf("freestanding/riscv64 with an F/D unit: %v", err)
	}
}
