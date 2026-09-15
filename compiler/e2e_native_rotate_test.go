package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Rotations spelled with shifts (docs/spec/94-assembler.md §9 "Rotates"):
// `(x >> k) | (x << (u32(32) - k))` — the hash library's `rotr32` once its
// literal count is inlined — lowers to one `ror` on the AArch64 lane, with
// the difference folded so no variable-shift guard remains; the mirrored
// left rotation and the 64-bit form follow. The verifier proves each body
// against its Oak spelling (`Oak.AssemblerSemantics.ror_spelling`); the C
// backend's realization is the oracle.
const nativeRotateProgram = `
rotr32: (x: u32, n: u32): u32 = (x >> n) | (x << (u32(32) - n))
rotl64: (x: u64, n: u64): u64 = (x << n) | (x >> (u64(64) - n))

sigma0: (x: u32): u32 = rotr32(x, u32(7)) ^ rotr32(x, u32(18)) ^ (x >> u32(3))
mix64: (x: u64): u64 = rotl64(x, u64(13)) ^ rotl64(x, u64(59))

main: (): i32 {
  assert(rotr32(u32(0x80000001), u32(1)) == u32(0xC0000000))
  assert(sigma0(u32(0x12345678)) == u32(0xE7FCE6EE))
  assert(rotl64(u64(1), u64(63)) == u64(0x8000000000000000))
  assert(mix64(u64(0x0123456789ABCDEF)) == (u64(0x0123456789ABCDEF) << u64(13) | u64(0x0123456789ABCDEF) >> u64(51)) ^ (u64(0x0123456789ABCDEF) << u64(59) | u64(0x0123456789ABCDEF) >> u64(5)))
  42
}
`

func TestE2ENativeRotates(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("rotate.oak", nativeRotateProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_rotate", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native rotates: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"sigma0", "mix64"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s must be proven equal to its Oak body (the rotates as ror); diagnostics:\n%s", fn, joined)
		}
		if !strings.Contains(joined, fn+": 2 rotation(s)") {
			t.Errorf("%s must lower both rotations to ror; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_rotate_c", New().WithSource("rotate.oak", nativeRotateProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
