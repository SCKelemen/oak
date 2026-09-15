package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Vector arguments beyond v0–v7 (docs/spec/94-assembler.md §9, the vector
// class of the argument layout): the ninth and later vector-class
// arguments travel in the caller's outgoing area, sixteen bytes each at a
// sixteen-byte alignment, on the one stack cursor the integer class shares
// (asm.LayoutArguments); the callee loads them whole with `ldr q` in its
// prologue, the seam checker binds them as stack parameters, and the
// verifier reads their lanes from the frame. A native caller reaches a
// native callee, and the C-compiled shim under the Oak name reaches the
// same native entry with the platform C compiler's layout, so the C
// compiler is the oracle for the layout; the C build of the whole program
// is the oracle for the values.
const nativeVectorStackArgsProgram = `
// Ten vectors: the ninth and tenth arrive on the stack.
ten: (a: simd.U8x16, b: simd.U8x16, c: simd.U8x16, d: simd.U8x16, e: simd.U8x16, f: simd.U8x16, g: simd.U8x16, h: simd.U8x16, i: simd.U8x16, j: simd.U8x16): simd.U8x16 {
  simd.or_u8x16(simd.or_u8x16(simd.or_u8x16(simd.or_u8x16(a, b), simd.or_u8x16(c, d)), simd.or_u8x16(simd.or_u8x16(e, f), simd.or_u8x16(g, h))), simd.or_u8x16(i, j))
}

// Nine words and ten vectors: the ninth word and the last two vectors
// share the stack area in declaration order; the two stack vectors are
// read directly and passed on to ten, whose result is tested for any lane.
mixed: (w0: u32, w1: u32, w2: u32, w3: u32, w4: u32, w5: u32, w6: u32, w7: u32, a: simd.U8x16, b: simd.U8x16, c: simd.U8x16, d: simd.U8x16, e: simd.U8x16, f: simd.U8x16, g: simd.U8x16, h: simd.U8x16, w8: u32, i: simd.U8x16, j: simd.U8x16): u32 {
  s: simd.U8x16 = ten(a, b, c, d, e, f, g, h, i, j)
  w0 + w1 + w2 + w3 + w4 + w5 + w6 + w7 + w8 + simd.movemask_u8x16(simd.and_u8x16(i, j)) + (simd.any_u8x16(s) ? u32(1) | u32(0))
}

main: (): i32 {
  one: simd.U8x16 = simd.splat_u8x16(u8(1))
  two: simd.U8x16 = simd.splat_u8x16(u8(2))
  s: simd.U8x16 = ten(one, one, one, one, one, one, one, one, two, two)
  assert(simd.movemask_u8x16(simd.eq_u8x16(s, simd.splat_u8x16(u8(3)))) == u32(65535))
  assert(mixed(u32(1), u32(2), u32(3), u32(4), u32(5), u32(6), u32(7), u32(8), one, one, one, one, one, one, one, one, u32(100), two, two) == u32(137))
  42
}
`

func TestE2ENativeVectorStackArgs(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("vecstack.oak", nativeVectorStackArgsProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_vector_stack_args", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native vector stack args: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"ten_neon_abi", "mixed_neon_abi", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	// The stack vectors are read from their frame slots as lanes: the
	// straight-line vector body is proven on both halves.
	if !strings.Contains(joined, "asm unit ten_neon_abi: proven equal to its Oak body at the bit level (128-bit vector result, both halves)") {
		t.Errorf("ten must be proven on both halves; diagnostics:\n%s", joined)
	}
	// mixed's ninth word and last two vectors share the stack area; the
	// native run above and the witnesses agree on the layout (its proof,
	// a nine-word sum beside a call summary over ten vectors, exceeds the
	// diagram budget).
	if !strings.Contains(joined, "asm unit mixed_neon_abi: proven") && !strings.Contains(joined, "asm unit mixed_neon_abi: agrees with its Oak body on every witness input") {
		t.Errorf("mixed must be proven or witnessed; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_vector_stack_args_c", New().WithSource("vecstack.oak", nativeVectorStackArgsProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
