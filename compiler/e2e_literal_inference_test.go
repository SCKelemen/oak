package compiler

import (
	"strings"
	"testing"
)

// Integer literals take their type from context (docs/spec/25-type-inference.md
// §3a): a literal next to a typed operand has exactly the type, range, and
// overflow behavior of the explicitly cast spelling. Each assertion below
// compares the bare literal against the cast form, including u32 wraparound
// and u8 wraparound at a store, in running machine code. Expression-level
// narrow arithmetic and signed overflow follow the backend's existing C
// semantics for both spellings and are not asserted here.
func TestE2ELiteralInferenceMatchesCasts(t *testing.T) {
	code, abnormal := buildAndRun(t, "literal_inference", `
bump: (at: u32): u32 {
  at + 1
}
bump_cast: (at: u32): u32 {
  at + u32(1)
}
scale: (at: u32): u32 {
  at * 2 + 1
}
scale_cast: (at: u32): u32 {
  at * u32(2) + u32(1)
}
narrow: (n: u8): u8 {
  n + 1
}
narrow_cast: (n: u8): u8 {
  n + u8(1)
}
signed_step: (n: i32): i32 {
  n + -1
}
signed_step_cast: (n: i32): i32 {
  n + i32(-1)
}
main: (): i32 {
  top: u32 = 4294967295
  assert(bump(top) == bump_cast(top))
  assert(bump(top) == 0)
  assert(scale(top) == scale_cast(top))
  assert(scale(top) == 4294967295)
  assert(2 * top == top * u32(2))
  assert(1 + top == 0)

  full: u8 = 255
  assert(narrow(full) == narrow_cast(full))
  assert(narrow(full) == 0)
  half: u8 = 127
  assert(half * 2 + 1 == 255)
  assert(half * 2 + 2 == half * u8(2) + u8(2))
  stored: u8 = half * 2 + 2
  assert(stored == 0)

  low: i32 = -100
  assert(signed_step(low) == signed_step_cast(low))
  assert(signed_step(low) == -101)
  assert(low * 2 - 1 == -201)

  i: u32 = 0
  total: u32 = 0
  while i < 10 {
    total = total + i * 2
    i = i + 1
  }
  assert(total == 90)

  values: [4]u32
  values[0] = 40
  values[1] = 2
  assert(values[0] + values[1] == 42)
  assert(values[0] - 1 == 39)

  hcr: u64 = 0x19
  assert(0x10 & hcr == 0x10)
  assert(1 << 4 == hcr & 0x10)

  42
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// A literal that does not fit the type its context requires is an error at
// the literal, never a silent fallback to a wider signed type.
func TestLiteralInferenceRejectsOutOfRangeLiterals(t *testing.T) {
	cases := []struct {
		name, src, want string
	}{
		{"unsigned-negative", "f: (at: u32): u32 { at + -1 }", "literal -1 does not fit in type u32"},
		{"unsigned-overflow", "f: (at: u32): u32 { at + 4294967296 }", "literal 4294967296 does not fit in type u32"},
		{"narrow-declaration", "main: (): i32 { n: u8 = 300\n 0 }", "literal 300 does not fit in type u8"},
		{"narrow-assignment", "main: (): i32 { n: u8 = 1\n n = n + 300\n 0 }", "literal 300 does not fit in type u8"},
		{"signed-underflow", "main: (): i32 { k: i8 = -129\n 0 }", "literal -129 does not fit in type i8"},
		{"comparison", "f: (at: u32): Bool { at < -1 }", "literal -1 does not fit in type u32"},
		{"argument", "g: (n: u8): u8 { n }\nmain: (): i32 { n: u8 = g(256)\n 0 }", "literal 256 does not fit in type u8"},
		{"index", "main: (): i32 { a: [4]u32\n a[-1] = 0\n 0 }", "literal -1 does not fit in type u32"},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			_, err := New().WithSource(c.name+".oak", c.src).Check().Get()
			if err == nil {
				t.Fatalf("%s: expected a type error", c.name)
			}
			if !strings.Contains(err.Error(), c.want) {
				t.Fatalf("%s: error %q does not mention %q", c.name, err.Error(), c.want)
			}
		})
	}
}

// Mixing a typed int variable with a fixed-width unsigned operand is still
// rejected, and the diagnostic now carries the operator's source position.
func TestLiteralInferenceKeepsSignednessRule(t *testing.T) {
	_, err := New().WithSource("mix.oak", "f: (at: u32): u32 {\n  i: int = 3\n  at + i\n}").Check().Get()
	if err == nil {
		t.Fatal("expected a signedness error")
	}
	if !strings.Contains(err.Error(), "cannot mix signed and unsigned types: u32 and int") {
		t.Fatalf("unexpected error: %v", err)
	}
	if strings.Contains(err.Error(), "0:0") {
		t.Fatalf("signedness diagnostic lost its position: %v", err)
	}
}
