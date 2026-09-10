package compiler

import (
	"strings"
	"testing"
)

// Floating-point fields and layout queries (docs/spec/20-types.md sections
// 11.3.1 and 11.3.8): f32/f64 fields are placed at their natural LP64 size
// and alignment, f16/bf16 in their uint16_t carriers, records over them get
// the proven layout (the emitted sizeof/offsetof assertions make cc ratify
// it), and size_of/align_of/offset_of answer over them. Record values with
// float fields flow through calls and returns like any other record.
func TestE2EFloatRecordLayout(t *testing.T) {
	src := `
Sample: type = struct {
  tag: u8
  half: f16
  brain: bf16
  single: f32
  wide: f64
}

Pair: type = struct { hi: f64, lo: f64 }

static_assert(size_of[f32]() == u32(4))
static_assert(size_of[f64]() == u32(8))
static_assert(size_of[f16]() == u32(2))
static_assert(size_of[bf16]() == u32(2))
static_assert(align_of[f64]() == u32(8))
static_assert(size_of[Sample]() == u32(24))
static_assert(offset_of[Sample](half) == u32(2))
static_assert(offset_of[Sample](brain) == u32(4))
static_assert(offset_of[Sample](single) == u32(8))
static_assert(offset_of[Sample](wide) == u32(16))
static_assert(size_of[Pair]() == u32(16))

split: (x: f64): Pair {
  hi: f64 = f64_bits_u64(u64_bits_f64(x) & u64(18446744069414584320))
  Pair { hi: hi, lo: x - hi }
}

main: (): i32 {
  assert(size_of[f64]() == u32(8))
  assert(offset_of[Pair](lo) == u32(8))
  p: Pair = split(1.0000001)
  assert(p.hi + p.lo == 1.0000001)
  assert(p.lo != 0.0)
  s: Sample = Sample { tag: u8(1), half: f16_round_f32(1.5), brain: bf16_round_f32(1.5), single: 1.5, wide: 2.5 }
  assert(f32(s.half) == 1.5)
  assert(f32(s.brain) == 1.5)
  assert(f64(s.single) + s.wide == 4.0)
  42
}
`
	output, err := New().WithSource("floatlayout.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, want := range []string{"sizeof(f64)", "sizeof(oak_Sample)", "offsetof(oak_Sample, wide)", "offsetof(oak_Pair, lo)"} {
		if !strings.Contains(output, want) {
			t.Fatalf("emitted C lacks %q:\n%s", want, output)
		}
	}
	if strings.Contains(output, "OAK_UNSUPPORTED_RECORD_LAYOUT") {
		t.Fatalf("a float record was not placed:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "floatlayout", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
