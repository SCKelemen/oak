package compiler

import (
	"os/exec"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/target"
	"github.com/SCKelemen/oak/toolchain"
)

// Parameters beyond the register contract on the rv64 lane
// (docs/spec/94-assembler.md §9): a scalar past a0–a7 arrives widened in
// an XLEN-sized slot of the caller's outgoing area (the LP64 psABI), read
// in the prologue; a native caller stores its stack arguments into the
// area at the frame's bottom. A span or a record beyond the registers
// stays with the C backend in this increment. The verifier binds the slots
// as frame slots, so `nine` is proven; the program runs under user-mode
// QEMU against the C backend's realization.
func TestE2ENativeRV64StackArgs(t *testing.T) {
	_, infos := nativeRV64Lower(t, rv64Linux, nativeStackArgsProgram)
	joined := strings.Join(infos, "\n")
	for _, fn := range []string{"nine", "twelve", "through_c"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the rv64 lane; diagnostics:\n%s", fn, joined)
		}
	}
	if !strings.Contains(joined, "asm unit nine: proven") {
		t.Errorf("nine was not proven by the verifier; diagnostics:\n%s", joined)
	}
	for _, fn := range []string{"tail_sum", "records_last"} {
		if !strings.Contains(joined, fn+" left to the C backend") || !strings.Contains(joined, "beyond the register contract stays with the C backend") {
			t.Errorf("%s (a span or record on the stack) must stay with the C backend with the reason; diagnostics:\n%s", fn, joined)
		}
	}
	// through_c passes ten arguments to a C function: its variable and
	// constant arguments are read at the move and the two beyond the
	// registers go through the outgoing area.
	if !strings.Contains(joined, "asm unit through_c:") {
		t.Errorf("through_c should be lowered; diagnostics:\n%s", joined)
	}
	// Executed on the bare machine under QEMU against the C backend's
	// realization (the harness of the span corpus), and under a user-mode
	// emulator when the host has one.
	skipInShort(t)
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	bareNative, bareInfos := nativeRV64Lower(t, bare, nativeStackArgsProgram)
	if bareJoined := strings.Join(bareInfos, "\n"); !strings.Contains(bareJoined, "asm unit nine: proven") {
		t.Errorf("nine was not proven on the freestanding target; diagnostics:\n%s", bareJoined)
	}
	if out := runNativeRV64BareABI(t, "native_rv64_stack_args", bareNative, false); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("the stack-argument corpus under QEMU did not exit 42:\n%s", out)
	}
	emulator, err := toolchain.ResolveEmulator(rv64Linux, nil, nil)
	if err != nil {
		t.Skipf("no user-mode emulator: %v", err)
	}
	bin := crossLink(t, rv64Linux, New().WithSource("stackargs.oak", nativeStackArgsProgram).WithNativeBodies())
	cmd := exec.Command(emulator.Path, append(append([]string{}, emulator.Args...), bin)...)
	out, err := cmd.CombinedOutput()
	code := 0
	if exitErr, isExit := err.(*exec.ExitError); isExit {
		code = exitErr.ExitCode()
	} else if err != nil {
		t.Fatalf("%s: %v\n%s", emulator.Command(), err, out)
	}
	if code != 42 {
		t.Fatalf("exit %d under %s, want 42\n%s", code, emulator.Command(), out)
	}
}
