package asm

import (
	"bytes"
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
	"time"
)

// The second execution oracle (docs/spec/94-assembler.md §9): the Sail
// RISC-V model, the ratified golden model, run as its C emulator over the
// same differential units. The harness reports through the HTIF tohost
// device — a 64-bit store of device 1, command 1, and the character
// prints it; device 0 with an odd payload exits — and the emulator finds
// the device by the ELF's `tohost` symbol. Skips when the emulator is not
// built (external/sail-riscv is a gitignored checkout).

var sailRiscvSim = filepath.Join("..", "external", "sail-riscv", "build", "c_emulator", "sail_riscv_sim")

var rv64Sail = rv64Machine{
	name:       "sail_riscv_sim",
	globals:    "volatile unsigned long long tohost __attribute__((aligned(8), section(\".tohost\")));\nvolatile unsigned long long fromhost __attribute__((aligned(8), section(\".tohost\")));\n",
	putc:       "tohost = (1ull << 56) | (1ull << 48) | (unsigned char)c;",
	exit:       "tohost = 1; /* device 0: exit code 0 */",
	start:      ".section .text.init\n.globl _start\n_start:\n  li t0, 0x6600\n  csrs mstatus, t0\n  la sp, _stack_top\n  call cmain\n1: j 1b\n",
	linkScript: "ENTRY(_start)\nSECTIONS {\n  . = 0x80000000;\n  .text : { *(.text.init) *(.text*) }\n  .rodata : { *(.rodata*) *(.srodata*) }\n  . = ALIGN(4096);\n  .tohost : { *(.tohost) }\n  .data : { *(.data*) *(.sdata*) }\n  .bss : { *(.bss*) *(.sbss*) }\n  . = ALIGN(16);\n  . += 0x10000;\n  _stack_top = .;\n}\n",
	run: func(t *testing.T, image string) string {
		ctx, cancel := context.WithTimeout(context.Background(), 120*time.Second)
		defer cancel()
		cmd := exec.CommandContext(ctx, sailRiscvSim, image)
		var out bytes.Buffer
		cmd.Stdout, cmd.Stderr = &out, &out
		if err := cmd.Run(); err != nil {
			t.Fatalf("sail_riscv_sim: %v\n%s", err, out.String())
		}
		return out.String()
	},
}

func TestRV64SailDifferential(t *testing.T) {
	requireRV64Tools(t, "riscv64-elf-gcc")
	if _, err := os.Stat(sailRiscvSim); err != nil {
		t.Skip("sail_riscv_sim not built under external/sail-riscv")
	}
	runRV64Differential(t, rv64Sail)
}
