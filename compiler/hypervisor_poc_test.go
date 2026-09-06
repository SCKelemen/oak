package compiler

import (
	"os"
	"os/exec"
	"path/filepath"
	"testing"
)

// buildAndRunStrict exercises the complete Oak pipeline under the strict
// discipline profile, compiles the generated C, and executes it. Hypervisor
// POCs use this rather than parser/typechecker-only tests: if a construct
// cannot survive lowering to running machine code, it is not yet useful to
// the core OS experiment.
func buildAndRunStrict(t *testing.T, name, src string) (exitCode int, abnormal bool) {
	t.Helper()
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("no C compiler on PATH")
	}

	output, err := New().WithProfile("strict").WithSource(name+".oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("strict Oak compilation failed: %v", err)
	}

	dir := t.TempDir()
	cPath := filepath.Join(dir, name+".c")
	binPath := filepath.Join(dir, name)
	if err := os.WriteFile(cPath, []byte(output), 0o644); err != nil {
		t.Fatal(err)
	}
	compile := exec.Command(cc, "-std=c99", "-O2", "-o", binPath, cPath)
	if combined, err := compile.CombinedOutput(); err != nil {
		t.Fatalf("cc failed: %v\n%s\n--- generated C ---\n%s", err, combined, output)
	}

	run := exec.Command(binPath)
	err = run.Run()
	if err == nil {
		return 0, false
	}
	if exitErr, ok := err.(*exec.ExitError); ok {
		if exitErr.ExitCode() >= 0 {
			return exitErr.ExitCode(), false
		}
		return -1, true
	}
	t.Fatalf("failed to run binary: %v", err)
	return 0, false
}

// Edge-triggered virtual IRQ lifecycle. ActivePending is the important state:
// an edge that arrives while the interrupt is active must survive the EOI and
// become pending again rather than being lost.
func TestHypervisorPOCVirtualIrqLifecycle(t *testing.T) {
	code, abnormal := buildAndRunStrict(t, "hypervisor_virq", `
IrqState: type =
  | Disabled
  | Idle
  | Pending
  | Active
  | ActivePending

raise: (s: IrqState): IrqState = s ?
  | .Disabled -> .Disabled
  | .Idle -> .Pending
  | .Pending -> .Pending
  | .Active -> .ActivePending
  | .ActivePending -> .ActivePending

ack: (s: IrqState): IrqState = s ?
  | .Pending -> .Active
  | .Disabled -> .Disabled
  | .Idle -> .Idle
  | .Active -> .Active
  | .ActivePending -> .ActivePending

eoi: (s: IrqState): IrqState = s ?
  | .Active -> .Idle
  | .ActivePending -> .Pending
  | .Disabled -> .Disabled
  | .Idle -> .Idle
  | .Pending -> .Pending

state_code: (s: IrqState): i32 = s ?
  | .Disabled -> 3
  | .Idle -> 5
  | .Pending -> 17
  | .Active -> 19
  | .ActivePending -> 23

main: (): i32 {
  s0: IrqState = .Idle
  s1: IrqState = raise(s0)
  s2: IrqState = ack(s1)
  s3: IrqState = raise(s2)
  s4: IrqState = eoi(s3)
  state_code(s4)
}
`)
	if abnormal || code != 17 {
		t.Fatalf("exit = (%d, abnormal=%v), want 17 (edge while active re-pends after EOI)", code, abnormal)
	}
}

// Bounded priority selection over fixed caller-owned storage. The loop shape
// is intentionally accepted by Oak's strict Power-of-Ten/TigerStyle profile:
// fixed storage, no allocation, monotonically increasing counter, immutable
// loop bound, and no recursion. Matches remain value-producing expressions;
// the loop performs the state update after those values have been selected.
func TestHypervisorPOCBoundedIrqSelection(t *testing.T) {
	code, abnormal := buildAndRunStrict(t, "hypervisor_irq_select", `
main: (): i32 {
  eligible_storage: [4]u8
  priority_storage: [4]u8
  eligible: [*]u8 = span(&eligible_storage)
  priority: [*]u8 = span(&priority_storage)

  eligible[0] = u8(1)
  eligible[1] = u8(1)
  eligible[2] = u8(0)
  eligible[3] = u8(1)

  priority[0] = u8(50)
  priority[1] = u8(10)
  priority[2] = u8(1)
  priority[3] = u8(20)

  mask: u8 = u8(40)
  best: i32 = -1
  best_priority: u8 = mask
  n: u32 = len(eligible)
  i: u32 = 0

  while i < n {
    candidate: u8 = eligible[i] ?
      | 1 -> priority[i]
      | _ -> mask
    better: Bool = candidate < best_priority
    next_best: i32 = better ?
      | .True -> i32(i)
      | .False -> best
    next_priority: u8 = better ?
      | .True -> candidate
      | .False -> best_priority
    best = next_best
    best_priority = next_priority
    i = i + 1
  }

  best
}
`)
	if abnormal || code != 1 {
		t.Fatalf("exit = (%d, abnormal=%v), want IRQ slot 1", code, abnormal)
	}
}

// Stage-2 arithmetic POC. This deliberately stays on the pure side of the
// future page-table API: address decomposition and alignment should be proved
// and generated from one semantic definition before Oak is allowed to own
// descriptor writes, TLBI, or other AArch64-specific effects.
func TestHypervisorPOCStageTwoPageArithmetic(t *testing.T) {
	code, abnormal := buildAndRunStrict(t, "hypervisor_stage2_math", `
page_base: (addr: u64): u64 = (addr / u64(4096)) * u64(4096)
page_offset: (addr: u64): u64 = addr - page_base(addr)
page_index: (addr: u64): u64 = addr / u64(4096)

main: (): i32 {
  addr: u64 = u64(74565)
  base: u64 = page_base(addr)
  off: u64 = page_offset(addr)
  index: u64 = page_index(addr)

  assert(base == u64(73728))
  assert(off == u64(837))
  assert(index == u64(18))
  assert(base + off == addr)
  29
}
`)
	if abnormal || code != 29 {
		t.Fatalf("exit = (%d, abnormal=%v), want 29 after stage-2 arithmetic assertions", code, abnormal)
	}
}