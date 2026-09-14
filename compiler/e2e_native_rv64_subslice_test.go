package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/target"
)

// subslice on the rv64 lane (docs/spec/94-assembler.md §9): the derived
// pair {base + start·elem, n} under the C helper's check — `bltu norm,
// start, trap`, `sub rest, norm, start`, `bltu rest, n, trap` — as a span
// local in callee-saved registers or as a call argument in scratch
// registers; the checker follows the idiom into a derived span. The
// AArch64 lane's subslice corpus lowers whole and runs on the bare machine
// under QEMU with the C backend's exit code.
func TestE2ENativeRV64Subslice(t *testing.T) {
	_, infos := nativeRV64Lower(t, rv64Linux, nativeSubsliceProgram)
	joined := strings.Join(infos, "\n")
	for _, fn := range []string{"sum", "fields", "clear_middle", "edge", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the rv64 lane; diagnostics:\n%s", fn, joined)
		}
	}
	if !strings.Contains(joined, "asm unit sum: proven") {
		t.Errorf("sum was not proven by the verifier; diagnostics:\n%s", joined)
	}
	skipInShort(t)
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	bareNative, _ := nativeRV64Lower(t, bare, nativeSubsliceProgram)
	if out := runNativeRV64BareABI(t, "native_rv64_subslice", bareNative, false); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("the subslice program under QEMU did not exit 42:\n%s", out)
	}
}
