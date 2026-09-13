package compiler

import (
	"strings"
	"testing"
)

// Package globals on the RV64 lane (docs/spec/94-assembler.md §9): a
// global's cell is addressed with `la` (auipc then addi, relocated as
// R_RISCV_PCREL_HI20 / PCREL_LO12_I against the C emitter's label) and
// read or written whole at its width; the RV64 checker admits that shape
// alone and the verifier proves readers and writers over the cells as the
// AArch64 lane does. The same program as the AArch64 globals test.
func TestE2ENativeRV64Globals(t *testing.T) {
	_, infos := nativeRV64Lower(t, rv64Linux, nativeGlobalsProgram)
	joined := strings.Join(infos, "\n")
	for _, fn := range []string{"set_state", "sum_state", "read_state", "bump"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s must lower on the rv64 lane over package globals; diagnostics:\n%s", fn, joined)
		}
	}
	for _, want := range []string{
		"asm unit sum_state: proven",
		"asm unit set_state: proven equal to its Oak body in the package state it writes (level, st, trans_pa, walk_null)",
		"asm unit bump: proven",
	} {
		if !strings.Contains(joined, want) {
			t.Errorf("want %q on the rv64 lane; diagnostics:\n%s", want, joined)
		}
	}
}
