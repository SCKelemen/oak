package compiler

// A 64-bit address computed from a narrow parameter — the OS pilot's
// page_pa, `pool_base + u64(index) * page_size` over a u16 index — is
// decided in the linear normal form: the Oak side's `index and 0xFFFF` and
// the machine's read of the argument register under `and 65535` are both
// the parameter (docs/spec/94-assembler.md §8, the linear normal form). At
// the bit level the 64-bit sum of two unknowns exceeded the node budget and
// the unit was evidence, not proof.

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

const nativeLinearMaskProgram = `page_size: u64 = u64(4096)

Regime: type = struct {
  root: u16
  pool_base: u64
}

page_pa: (pool_base: u64, index: u16): u64 { pool_base + u64(index) * page_size }

get_root_pa: (s: [*]Regime, dom: u32): u64 { dom < len(s) ? { page_pa(s[dom].pool_base, s[dom].root) } | { u64(0) } }

main: (): i32 {
  r: [1]Regime = [Regime { root: 3, pool_base: u64(65536) }]
  (get_root_pa(span(&r), u32(0)) == u64(65536 + 3 * 4096)) ? 42 | 1
}
`

func TestE2ENativePagePaLinearForm(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("page_pa.oak", nativeLinearMaskProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "page_pa", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if !strings.Contains(joined, "asm unit page_pa: proven equal to its Oak body (linear normal form 4096*index + 1*pool_base + 0 (mod 2^64))") {
		t.Errorf("page_pa must be proven in the linear normal form; diagnostics:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit get_root_pa: proven") {
		t.Errorf("get_root_pa must be proven; diagnostics:\n%s", joined)
	}
}
