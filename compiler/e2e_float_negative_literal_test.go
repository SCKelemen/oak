package compiler

import "testing"

// f32(-0.5) is the literal -0.5 at f32 width, exactly as f32(0.5) is the
// positive one (docs/spec/20-types.md section 11.3.4): the sign is part of
// the literal's spelling, not an f64 negation the constructor would have
// to narrow. Observed as the bit pattern 0xBF000000 in the compiled
// program and the interpreter.
func TestE2EFloatNegativeLiteralConstructor(t *testing.T) {
	const program = `
main: (): i32 {
  a1: f32 = f32(-0.5)
  a2: f32 = f32(0.5)
  score: i32 = 0
  score = u32_bits_f32(a1) == u32(3204448256) ? score + 1 | score
  score = u32_bits_f32(a1 + a2) == u32(0) ? score + 1 | score
  score = u64_bits_f64(f64(-2.5)) == u64(13836183955189006336) ? score + 1 | score
  score
}
`
	code, abnormal := buildAndRun(t, "negfloat", program)
	if abnormal {
		t.Fatalf("compiled program trapped")
	}
	if code != 3 {
		t.Fatalf("compiled program scored %d of 3 checks", code)
	}
	if got := interpretChecked(t, program); got != 3 {
		t.Fatalf("interpreter scored %d of 3 checks", got)
	}
}
