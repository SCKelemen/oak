package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// If-conversion speculates both arms of a conditional chain
// (nativegen/select.go), so an arm may only hold what cannot trap on the
// other arm's inputs. A shift by a variable count is guarded at the width,
// and here the else arm's count `(k - 8) * 8` wraps past it whenever the
// then arm is the one taken: speculated, the guard trapped on `k < 8`
// (the prover's src_name, which killed the natively built prover on its
// first name). Only a literal count is speculable; the body lowers with
// its branches, runs, and is proven — the verifier's witness inputs
// would otherwise report the machine trapping where Oak yields a value.
const nativeSelectGuardProgram = `
place: (x: u64, k: u32) -> u64 {
  lo: u64 = 0
  hi: u64 = 0
  k < u32(8) ? { lo = x << u64(k * u32(8)) } | { hi = x >> u64((k - u32(8)) * u32(8)) }
  lo | hi
}

main: (): i32 {
  a: u64 = place(u64(3), u32(1))
  b: u64 = place(u64(768), u32(9))
  i32_bits_u32(u32_trunc_u64(a + b) & u32(255))
}
`

func TestE2ENativeSelectDoesNotSpeculateAGuardedShift(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("guard.oak", nativeSelectGuardProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_select_guard", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 3 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 3 (a speculated shift guard traps)\n%s", code, abnormal, joined)
	}
	if !strings.Contains(joined, "asm unit place: proven equal to its Oak body") {
		t.Errorf("place must be proven, not if-converted over a trapping arm; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_select_guard_c", New().WithSource("guard.oak", nativeSelectGuardProgram)); abnormal || code != 3 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 3", code, abnormal)
	}
}
