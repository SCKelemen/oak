package compiler

import "testing"

// Text for emitters (stdlib/README.md, "Text for emitters"; the ml pilot's
// F8): a line of generated code — a name, a float in its shortest
// round-trip spelling, an integer — built into a caller-owned buffer from
// the pieces the standard library has, no allocation and no format string.
const emitterTextProgram = `import(std)

// A line of text for an emitter: a name, a float, an integer, into a
// caller-owned buffer, with the float's digits rendered into a small
// scratch and appended as text.
emit_binding: (dst: [*]u8, name: []u8, value: f64, index: u32): Result[u32, TextError] = {
  digits: [32]u8
  n: u32 = 0
  true ? {
    scratch: [*]u8 = span(&digits)
    n = float_written(float_format(scratch, value))
  }
  text: []u8 = view(&digits)
  b: TextBuilder = text_builder()
  b = append_text(b, dst, name)
  b = append_text(b, dst, text_literal(" = "))
  b = append_text(b, dst, text[u32(0):n])
  b = append_text(b, dst, text_literal(" // #"))
  b = append_u64(b, dst, u64(index))
  b = append_rune(b, dst, u32(10))
  finish_text(b)
}

main: (): i32 = {
  out: [64]u8
  dst: [*]u8 = span(&out)
  written: Result[u32, TextError] = emit_binding(dst, text_literal("y"), 1.5e-05, 7)
  expected: []u8 = text_literal("y = 1.5e-05 // #7\n")
  ok: Bool = text_result_ok(written) && text_result_value(written) == len(expected)
  i: u32 = 0
  while i < len(expected) && ok {
    ok = dst[i] == expected[i]
    i = i + 1
  }
  ok ? 42 | 1
}`

func TestE2EEmitterText(t *testing.T) {
	code, abnormal := buildAndRun(t, "emitter_text", emitterTextProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
