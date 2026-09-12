package compiler

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// The kernel adapter's EL0 entry (docs/spec/100-aarch64-control-transfer.md,
// the register handoff; the OS pilot's R6 follow-up) in both forms: Oak
// source through the R6 registers and eret_x0, and an .oakasm unit under the
// system capability. Neither is executed (EL1 instructions); the source form
// is checked for its lowering, the unit form is assembled by cc -c.
func TestE2EEL0EntryBothForms(t *testing.T) {
	source, err := New().WithSource("el0.oak", `
el0_enter: (sp: u64, pc: u64, pstate: u64, arg: u64) -> never {
  arm64.write_sp_el0(sp)
  arm64.write_elr_el1(pc)
  arm64.write_spsr_el1(pstate)
  arm64.isb()
  arm64.eret_x0(arg)
}

main: (): i32 {
  42
}
`).EmitC().Get()
	if err != nil {
		t.Fatalf("Oak-source EL0 entry failed to compile: %v", err)
	}
	for _, want := range []string{
		"oak_arm64_write_sp_el0( sp )",
		"oak_arm64_write_elr_el1( pc )",
		"oak_arm64_write_spsr_el1( pstate )",
		"oak_arm64_eret_x0( arg )",
		`register u64 x0_value0 __asm__("x0") = value0;`,
		`__asm__ volatile("eret" :: "r"(x0_value0) : "memory");`,
	} {
		if !strings.Contains(source, want) {
			t.Errorf("Oak-source EL0 entry lacks %q:\n%s", want, source)
		}
	}

	unit, err := New().WithSource("el0.oak", `
el0_enter: (sp: u64, pc: u64, pstate: u64, arg: u64) -> never

main: (): i32 {
  42
}
`).WithAsmUnit("el0.arm64.oakasm", `
el0_enter: (sp: u64, pc: u64, pstate: u64, arg: u64) -> never = {
  system
  bind x0 = sp
  bind x1 = pc
  bind x2 = pstate
  bind x3 = arg
  msr sp_el0, x0
  msr elr_el1, x1
  msr spsr_el1, x2
  mov x0, x3
  isb
  eret
}
`).EmitC().Get()
	if err != nil {
		t.Fatalf("assembly-unit EL0 entry failed the asm gate: %v", err)
	}
	flat := strings.Join(strings.Fields(unit), " ")
	cursor := 0
	for _, want := range []string{`"  msr sp_el0, x0\n"`, `"  msr elr_el1, x1\n"`, `"  msr spsr_el1, x2\n"`, `"  mov x0, x3\n"`, `"  isb\n"`, `"  eret\n"`} {
		rel := strings.Index(flat[cursor:], strings.Join(strings.Fields(want), " "))
		if rel < 0 {
			t.Fatalf("assembly-unit EL0 entry lacks ordered %s:\n%s", want, unit)
		}
		cursor += rel
	}

	requireArm64Host(t)
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("no C compiler on PATH")
	}
	dir := t.TempDir()
	for name, text := range map[string]string{"unit": unit, "source": source} {
		cPath := filepath.Join(dir, name+".c")
		if err := os.WriteFile(cPath, []byte(text), 0o644); err != nil {
			t.Fatal(err)
		}
		if combined, err := exec.Command(cc, "-std=c11", "-c", cPath, "-o", filepath.Join(dir, name+".o")).CombinedOutput(); err != nil {
			t.Fatalf("cc -c of the %s form failed: %v\n%s\n--- generated C ---\n%s", name, err, combined, text)
		}
	}
}
