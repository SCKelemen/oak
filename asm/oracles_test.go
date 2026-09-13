package asm

import (
	"os"
	"os/exec"
	"testing"
)

// The external oracles (docs/spec/94-assembler.md §8–§9): Sail, the Sail
// RISC-V emulator, Arm's decode tree, the RISC-V GNU tools, QEMU, llvm-mc.
// A test that needs one skips when it is absent — a developer's machine
// need not carry them — unless OAK_REQUIRE_ORACLES is set, as the
// `formal-sail` workflow sets it, where an absent oracle is a failure:
// silence there would be indistinguishable from a passing check.

// requireOracle skips the test, or fails it under OAK_REQUIRE_ORACLES.
func requireOracle(t *testing.T, msg string) {
	t.Helper()
	if os.Getenv("OAK_REQUIRE_ORACLES") != "" {
		t.Fatalf("oracle required by OAK_REQUIRE_ORACLES: %s", msg)
	}
	t.Skip(msg)
}

// rv64ToolPrefixes are the spellings of the RISC-V GNU toolchain: Homebrew's
// riscv64-elf-*, Debian's riscv64-unknown-elf-*, and the Linux cross tools.
var rv64ToolPrefixes = []string{"riscv64-elf-", "riscv64-unknown-elf-", "riscv64-linux-gnu-"}

// rv64Tool resolves a RISC-V GNU tool (as, gcc, objcopy, objdump) to the
// spelling on PATH, defaulting to Homebrew's when none is found (the
// caller's exec then reports the absence).
func rv64Tool(name string) string {
	for _, prefix := range rv64ToolPrefixes {
		if _, err := exec.LookPath(prefix + name); err == nil {
			return prefix + name
		}
	}
	return rv64ToolPrefixes[0] + name
}
