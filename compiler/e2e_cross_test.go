package compiler

import (
	"debug/elf"
	"encoding/binary"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/target"
	"github.com/SCKelemen/oak/toolchain"
)

// Cross builds (docs/spec/90-backend.md §2a): the target selects the
// assembler lane whose units apply and the companion object's format; a
// unit of another lane falls back to its Oak body or, without one, fails
// closed at compile time. The linking tests drive the resolved cross
// compiler (zig on this host) and skip when none can target the platform.

const crossPickOak = `
pick: (x, y: u64) -> u64 {
  x < y ? x | y
}

main: (): i32 {
  assert(pick(u64(3), u64(9)) == u64(3))
  assert(pick(u64(40), u64(2)) == u64(2))
  0
}
`

const crossPickRV64 = `
pick: (x, y: u64) -> u64 = {
  bind a0 = x
  bind a1 = y
  bltu a0, a1, small
  mv a0, a1
small:
  ret
}
`

const crossPickArm64 = `
pick: (x, y: u64) -> u64 = {
  bind x0 = x
  bind x1 = y
  cmp x0, x1
  csel x0, x0, x1, lo
  ret
}
`

func crossComp(tgt target.Target) Compilation {
	return New().WithSource("pick.oak", crossPickOak).WithAsmUnit("pick.rv64.oakasm", crossPickRV64).WithAsmUnit("pick.arm64.oakasm", crossPickArm64).WithTarget(tgt)
}

// The target picks the lane: one unit per lane may realize a signature,
// the other lane's unit yields to the Oak body under the right guard.
func TestCrossTargetSelectsLane(t *testing.T) {
	rv := target.Target{OS: target.OSLinux, Arch: target.ArchRiscv64}
	code, err := crossComp(rv).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(code, `"  bltu a0, a1, 1f\n"`) || strings.Contains(code, "csel x0") {
		t.Fatalf("linux/riscv64 C should carry the rv64 unit only:\n%s", code)
	}
	if !strings.Contains(code, "#if !(defined(__riscv) && (__riscv_xlen == 64)) || defined(OAK_PORTABLE_INTRINSICS)") {
		t.Fatal("the Oak fallback body must be guarded by the rv64 lane's negation")
	}
	arm := target.Target{OS: target.OSLinux, Arch: target.ArchArm64}
	code, err = crossComp(arm).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(code, "bltu a0") || !strings.Contains(code, "csel x0, x0, x1, lo") || !strings.Contains(code, "#if !(defined(__aarch64__)) || defined(OAK_PORTABLE_INTRINSICS)") {
		t.Fatalf("linux/arm64 C should carry the arm64 unit and its guard:\n%s", code)
	}
	amd := target.Target{OS: target.OSLinux, Arch: target.ArchAmd64}
	code, err = crossComp(amd).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(code, "__asm__") || strings.Contains(code, "OAK_PORTABLE_INTRINSICS") {
		t.Fatalf("linux/amd64 has no lane: the Oak body compiles unguarded:\n%s", code)
	}
	// Two units of one lane are still one too many.
	_, err = New().WithSource("pick.oak", crossPickOak).WithAsmUnit("a.rv64.oakasm", crossPickRV64).WithAsmUnit("b.rv64.oakasm", crossPickRV64).WithTarget(rv).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "one unit per lane") {
		t.Fatalf("duplicate rv64 units: %v", err)
	}
}

// Without an Oak body, a unit of another lane has no realization for the
// target: the build fails at compile time, not in the C compiler.
func TestCrossTargetForeignLaneWithoutFallbackFails(t *testing.T) {
	src := "pick: (x, y: u64) -> u64\n\nmain: (): i32 {\n  0\n}\n"
	_, err := New().WithSource("pick.oak", src).WithAsmUnit("pick.arm64.oakasm", crossPickArm64).WithTarget(target.Target{OS: target.OSLinux, Arch: target.ArchRiscv64}).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "no Oak fallback body") {
		t.Fatalf("foreign lane without fallback: %v", err)
	}
	// The native body backend is AArch64: another target compiles the C.
	if _, err := New().WithSource("pick.oak", crossPickOak).WithNativeBodies().WithTarget(target.Target{OS: target.OSLinux, Arch: target.ArchRiscv64}).EmitC().Get(); err != nil {
		t.Fatalf("native bodies on a non-arm64 target: %v", err)
	}
}

// crossLink builds the compilation for tgt through the resolved cross
// compiler and returns the executable's path; skips when the host has no
// compiler for the target.
func crossLink(t *testing.T, tgt target.Target, comp Compilation) string {
	t.Helper()
	drv, err := toolchain.Resolve(tgt, toolchain.Options{}, nil, nil)
	if err != nil || drv.Kind == "host" {
		t.Skipf("no cross compiler for %s on this host (%v)", tgt, err)
	}
	native, err := comp.EmitNative(ObjectFormat(tgt)).Get()
	if err != nil {
		t.Fatal(err)
	}
	dir := t.TempDir()
	cPath, objPath, bin := filepath.Join(dir, "p.c"), filepath.Join(dir, "asm.o"), filepath.Join(dir, "p")
	if err := os.WriteFile(cPath, []byte(native.C), 0o644); err != nil {
		t.Fatal(err)
	}
	args := append(append([]string{}, drv.Args...), "-std=c99", "-O1", "-ffp-contract=off")
	if drv.Static {
		args = append(args, "-static")
	}
	args = append(args, "-o", bin, cPath)
	if native.Object != nil {
		if err := os.WriteFile(objPath, native.Object, 0o644); err != nil {
			t.Fatal(err)
		}
		args = append(args, objPath)
	}
	args = append(args, "-lm")
	if out, err := exec.Command(drv.Path, args...).CombinedOutput(); err != nil {
		t.Fatalf("%s: %v\n%s", drv.Command(), err, out)
	}
	return bin
}

// From any host, a Linux binary for each lane: the assembled unit inside a
// static ELF of the target's machine.
func TestCrossBuildLinuxTargets(t *testing.T) {
	cases := []struct {
		tgt     target.Target
		machine elf.Machine
		flags   uint32
	}{
		{target.Target{OS: target.OSLinux, Arch: target.ArchRiscv64}, elf.EM_RISCV, 0x4},
		{target.Target{OS: target.OSLinux, Arch: target.ArchArm64}, elf.EM_AARCH64, 0},
		{target.Target{OS: target.OSLinux, Arch: target.ArchAmd64}, elf.EM_X86_64, 0},
	}
	for _, c := range cases {
		t.Run(c.tgt.String(), func(t *testing.T) {
			bin := crossLink(t, c.tgt, crossComp(c.tgt))
			file, err := elf.Open(bin)
			if err != nil {
				t.Fatal(err)
			}
			defer file.Close()
			if file.Machine != c.machine {
				t.Fatalf("machine %v, want %v", file.Machine, c.machine)
			}
			if file.Section(".interp") != nil {
				t.Fatal("a cross-built Linux executable links statically")
			}
			raw, err := os.ReadFile(bin)
			if err != nil {
				t.Fatal(err)
			}
			if eflags := binary.LittleEndian.Uint32(raw[48:52]); c.machine == elf.EM_RISCV && eflags&0x6 != c.flags {
				t.Fatalf("RISC-V float ABI flags %#x, want lp64d (%#x)", eflags&0x6, c.flags)
			}
			symbols, err := file.Symbols()
			if err != nil {
				t.Fatal(err)
			}
			found := false
			for _, sym := range symbols {
				if sym.Name == "oak_pick" {
					found = true
				}
			}
			if !found {
				t.Fatal("oak_pick is not in the linked image")
			}
		})
	}
}

// The companion object for a hosted RISC-V target declares the lp64d ABI
// its libc uses; the bare-metal object stays lp64.
func TestCrossObjectFlags(t *testing.T) {
	rv := crossComp(target.Target{OS: target.OSLinux, Arch: target.ArchRiscv64})
	object, err := rv.EmitAsmObject(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	if object[48] != 0x4 {
		t.Fatalf("hosted riscv64 object e_flags %#x, want EF_RISCV_FLOAT_ABI_DOUBLE", object[48])
	}
	bare := crossComp(target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64})
	object, err = bare.EmitAsmObject(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	if object[48] != 0 {
		t.Fatalf("freestanding riscv64 object e_flags %#x, want soft-float", object[48])
	}
}

// A cross-built Linux program runs from the tooling through a user-mode
// emulator (`oak run -target`, docs/spec/90-backend.md §2a): the binary
// zig linked for linux/riscv64 executes under qemu-riscv64 and its exit
// code is the program's. Skips without a cross compiler or an emulator
// (macOS has no user-mode QEMU; the CI job installs qemu-user-static).
func TestCrossRunUnderEmulator(t *testing.T) {
	for _, tgt := range []target.Target{
		{OS: target.OSLinux, Arch: target.ArchRiscv64},
		{OS: target.OSLinux, Arch: target.ArchArm64},
		{OS: target.OSLinux, Arch: target.ArchAmd64},
	} {
		t.Run(tgt.String(), func(t *testing.T) {
			if tgt.IsHost() {
				t.Skip("the host target runs directly")
			}
			emulator, err := toolchain.ResolveEmulator(tgt, nil, nil)
			if err != nil {
				t.Skipf("no emulator: %v", err)
			}
			// pick(40, 2) == 2 and pick(3, 9) == 3 are asserted; the program
			// returns 0 on success, and a failed assertion traps.
			bin := crossLink(t, tgt, crossComp(tgt))
			argv := append(append([]string{}, emulator.Args...), bin)
			cmd := exec.Command(emulator.Path, argv...)
			out, err := cmd.CombinedOutput()
			if err != nil {
				t.Fatalf("%s under %s: %v\n%s", tgt, emulator.Command(), err, out)
			}
			// A program whose assertion fails must fail under the emulator too.
			wrong := New().WithSource("pick.oak", strings.Replace(crossPickOak, "== u64(3))", "== u64(4))", 1)).WithAsmUnit("pick.rv64.oakasm", crossPickRV64).WithAsmUnit("pick.arm64.oakasm", crossPickArm64).WithTarget(tgt)
			bad := crossLink(t, tgt, wrong)
			if err := exec.Command(emulator.Path, append(append([]string{}, emulator.Args...), bad)...).Run(); err == nil {
				t.Fatal("a failed assertion exited 0 under the emulator")
			}
		})
	}
}
