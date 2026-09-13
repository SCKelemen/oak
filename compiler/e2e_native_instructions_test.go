package compiler

import (
	"encoding/binary"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

// Instruction functions on the native lane (docs/spec/94-assembler.md §9):
// the machine library's system-register accessors, barriers, event
// control, scalar instructions, and exception return lower to the
// instructions they name, through the assembler's parser, under the
// checker's system capability.

// The user-mode readable registers and the scalar instructions execute on
// an arm64 host; the barriers are legal at every level.
const nativeInstructionProgram = `
ticks: () -> u64 = arm64.read_cntvct_el0()

frequency: () -> u64 = arm64.read_cntfrq_el0()

// A barrier pair around a read: the instructions in sequence.
fenced_ticks: () -> u64 {
  arm64.dmb_ish()
  t: u64 = arm64.read_cntvct_el0()
  arm64.isb()
  t
}

swap_bytes: (x: u32) -> u32 = arm64.rev32(x)

leading_zeros: (x: u64) -> u64 = arm64.clz64(x)

reversed_bits: (x: u32) -> u32 = arm64.rbit32(x)

main: (): i32 {
  first: u64 = ticks()
  second: u64 = fenced_ticks()
  assert(second >= first)
  assert(frequency() > u64(0))
  assert(swap_bytes(u32(0x11223344)) == u32(0x44332211))
  assert(leading_zeros(u64(1)) == u64(63))
  assert(reversed_bits(u32(1)) == u32(0x80000000))
  42
}
`

func TestE2ENativeInstructionFunctions(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("instr.oak", nativeInstructionProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_instructions", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native instruction functions: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"ticks", "frequency", "fenced_ticks", "swap_bytes", "leading_zeros", "reversed_bits", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	for _, fn := range []string{"swap_bytes", "leading_zeros", "reversed_bits"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s must be proven equal to its Oak body (the verifier's instruction terms); diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_instructions_c", New().WithSource("instr.oak", nativeInstructionProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// The EL2 register program of the hypervisor adapter: system-register
// writes, the DAIF mask, a barrier, and an exception return with its
// carried register — lowered natively for freestanding/arm64, admitted by
// the checker under the system capability, and encoded into the companion
// object (it cannot run in user mode; the pilot runs it at EL2).
const nativeEL2Program = `
prepare: (hcr: u64, vttbr: u64, vtcr: u64, sp: u64, pc: u64, pstate: u64) -> () {
  arm64.daifset_irq()
  arm64.write_hcr_el2(hcr)
  arm64.write_vttbr_el2(vttbr)
  arm64.write_vtcr_el2(vtcr)
  arm64.write_sp_el1(sp)
  arm64.write_elr_el2(pc)
  arm64.write_spsr_el2(pstate)
  arm64.isb()
}

current_hcr: () -> u64 = arm64.read_hcr_el2()

enter: (arg: u64) -> never {
  arm64.isb()
  arm64.eret_x0(arg)
}

main: (): i32 {
  0
}
`

func TestE2ENativeEL2ProgramLowers(t *testing.T) {
	var infos []string
	comp := New().WithSource("el2.oak", nativeEL2Program).WithTarget(target.Target{OS: target.OSFreestanding, Arch: target.ArchArm64}).WithNativeBodies().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	native, err := comp.EmitNative(asm.ELF).Get()
	joined := strings.Join(infos, "\n")
	if err != nil {
		t.Fatalf("native EL2 program: %v\n%s", err, joined)
	}
	for _, fn := range []string{"prepare", "current_hcr", "enter", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	if machine := binary.LittleEndian.Uint16(native.Object[18:20]); machine != 183 {
		t.Fatalf("companion object e_machine %d, want EM_AARCH64", machine)
	}
	// The C shell keeps only prototypes for the lowered bodies: no inline
	// asm helpers for the register writes are needed on this path.
	if strings.Contains(native.C, "oak_arm64_write_hcr_el2(") && !strings.Contains(native.C, "encoded by the Oak assembler") {
		t.Fatal("the C still realizes the register program")
	}
}
