package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// The little-endian word idiom (docs/spec/94-assembler.md §9,
// nativegen/wide_load.go): an or-chain of a byte span's consecutive bytes,
// each converted to the result type and shifted into place, lowers to one
// load under one slack guard, and the verifier reads the wide load as the
// bytes' concatenation, so the body is proven. Four spellings: a guarded
// variable base (stdlib/hash.oak's crc32c_word_at), a 32-bit result, a
// constant base, and a loop whose condition proves the eight bytes so the
// guard is elided. Exit code: the words' bytes summed as the C backend
// computes them.
const nativeWideLoadProgram = `
word_at: (chunk: []u8, at: u32): u64 {
  len(chunk) >= at + u32(8) ? {
    u64(chunk[at]) | (u64(chunk[at + u32(1)]) << u64(8)) | (u64(chunk[at + u32(2)]) << u64(16)) | (u64(chunk[at + u32(3)]) << u64(24)) |
      (u64(chunk[at + u32(4)]) << u64(32)) | (u64(chunk[at + u32(5)]) << u64(40)) | (u64(chunk[at + u32(6)]) << u64(48)) | (u64(chunk[at + u32(7)]) << u64(56))
  } | { u64(0) }
}

half_at: (v: []u8, i: u32): u32 {
  len(v) >= u32(4) && i <= len(v) - u32(4) ? (u32(v[i]) | (u32(v[i + u32(1)]) << u32(8)) | (u32(v[i + u32(2)]) << u32(16)) | (u32(v[i + u32(3)]) << u32(24))) | u32(0)
}

first_word: (v: []u8): u64 {
  len(v) >= u32(8) ? (u64(v[0]) | (u64(v[1]) << u64(8)) | (u64(v[2]) << u64(16)) | (u64(v[3]) << u64(24)) | (u64(v[4]) << u64(32)) | (u64(v[5]) << u64(40)) | (u64(v[6]) << u64(48)) | (u64(v[7]) << u64(56))) | u64(0)
}

sum_words: (v: []u8): u64 {
  acc: u64 = 0
  i: u32 = 0
  while len(v) >= u32(8) && i <= len(v) - u32(8) {
    acc = acc + (u64(v[i]) | (u64(v[i + u32(1)]) << u64(8)) | (u64(v[i + u32(2)]) << u64(16)) | (u64(v[i + u32(3)]) << u64(24)) | (u64(v[i + u32(4)]) << u64(32)) | (u64(v[i + u32(5)]) << u64(40)) | (u64(v[i + u32(6)]) << u64(48)) | (u64(v[i + u32(7)]) << u64(56)))
    i = i + u32(8)
  }
  acc
}

// The inlined helper with a constant base: word_at's guard and offsets fold
// to constants under the caller's length, every byte is proven, and the
// lowering is one load at an immediate offset with no guard.
second_word: (v: []u8): u64 = word_at(v, u32(8))

main: (): i32 {
  buf: [16]u8 = [u8(1), u8(2), u8(3), u8(4), u8(5), u8(6), u8(7), u8(8), u8(9), u8(10), u8(11), u8(12), u8(13), u8(14), u8(15), u8(16)]
  v: []u8 = view(&buf)
  w: u64 = word_at(v, u32(4))
  h: u32 = half_at(v, u32(2))
  f: u64 = first_word(v)
  s: u64 = sum_words(v)
  x: u64 = second_word(v)
  // (12 + 5) + 6 + 1 + (1 + 9) + 9 = 43; a short span reads as zero.
  i32_bits_u32(u32_trunc_u64((w >> u64(56)) + (w & u64(255)))) + i32_bits_u32(h >> u32(24)) + i32_bits_u32(u32_trunc_u64(f & u64(255))) + i32_bits_u32(u32_trunc_u64(s & u64(255))) + i32_bits_u32(u32_trunc_u64(word_at(v, u32(9)))) + i32_bits_u32(u32_trunc_u64(x & u64(255)))
}
`

func TestE2ENativeWideLoad(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("wide_load.oak", nativeWideLoadProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_wide_load", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 43 {
		t.Fatalf("native wide load: exit = (%d, abnormal=%v), want 43\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"word_at", "half_at", "first_word"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven equal to its Oak body at the bit level") {
			t.Errorf("%s must be proven (the wide load is the bytes' concatenation); diagnostics:\n%s", fn, joined)
		}
	}
	// The constant base through the inlined helper: the eight bytes proven,
	// the load at an immediate offset without a guard.
	if !strings.Contains(joined, "second_word: 8 element guard(s) elided") {
		t.Errorf("second_word must elide the eight byte guards under the folded constants; diagnostics:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit second_word: proven equal to its Oak body at the bit level") {
		t.Errorf("second_word must be proven; diagnostics:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit sum_words:") || strings.Contains(joined, "asm unit sum_words: not verified") {
		t.Errorf("sum_words must be lowered and decided; diagnostics:\n%s", joined)
	}
	// The C backend computes the same exit code.
	if _, code, abnormal := buildAndRunFrom(t, "native_wide_load_c", New().WithSource("wide_load.oak", nativeWideLoadProgram)); abnormal || code != 43 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 43", code, abnormal)
	}
}
