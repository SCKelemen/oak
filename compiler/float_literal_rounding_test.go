package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

// Actual code generation already rounds source text at the target width.
// Its correct native constants must be accepted by the source verifier too.
func TestNativeSourceFloatLiteralRounding(t *testing.T) {
	const source = `
pub rounded: (a: f32) -> f32 = 1.00000005960464477550
pub negative: (a: f32) -> f32 = -1.00000005960464477550
pub below_midpoint: (a: f32) -> f32 = 1.00000017881393432617
pub below_overflow: (a: f32) -> f32 = 0x1.fffffeffffffffffffffp127
pub wide: (a: f64) -> f64 = 1e39
main: () -> i32 = 0
`
	for _, arch := range []string{target.ArchArm64, target.ArchRiscv64} {
		t.Run(arch, func(t *testing.T) {
			var infos []string
			out, err := New().WithSource("float_literal.oak", source).
				WithTarget(target.Target{OS: target.OSLinux, Arch: arch}).
				WithNativeBodies().WithVerifyFresh().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
				if d.Source == "native" {
					infos = append(infos, d.Message)
				}
			}).EmitNative(asm.ELF).Get()
			if err != nil {
				t.Fatal(err)
			}
			if len(out.Object) == 0 {
				t.Fatal("no native object emitted")
			}
			joined := strings.Join(infos, "\n")
			for _, name := range []string{"rounded", "negative", "below_midpoint", "below_overflow", "wide"} {
				if !strings.Contains(joined, "asm unit "+name+": proven") {
					t.Errorf("%s did not retain a proof:\n%s", name, joined)
				}
			}
		})
	}
}

func TestE2ESourceFloatLiteralRounding(t *testing.T) {
	const source = `
main: () -> i32 {
  above: f32 = 1.00000005960464477550
  below: f32 = 1.00000017881393432617
  negative: f32 = f32(-1.00000005960464477550)
  hex: f32 = 0x1.00000100000000000001p0
  zero: f32 = -1e-100
  subnormal: f32 = 0x1.0000000000000001p-150
  finite: f32 = 0x1.fffffeffffffffffffffp127
  wide: f64 = 1e39
  score: i32 = 0
  score = u32_bits_f32(above) == u32(1065353217) ? score + 1 | score
  score = u32_bits_f32(below) == u32(1065353217) ? score + 1 | score
  score = u32_bits_f32(negative) == u32(3212836865) ? score + 1 | score
  score = u32_bits_f32(hex) == u32(1065353217) ? score + 1 | score
  score = u32_bits_f32(zero) == u32(2147483648) ? score + 1 | score
  score = u32_bits_f32(subnormal) == u32(1) ? score + 1 | score
  score = u32_bits_f32(finite) == u32(2139095039) ? score + 1 | score
  score = is_finite(wide) ? score + 1 | score
  score
}
`
	if code, abnormal := buildAndRun(t, "source_float_rounding", source); abnormal || code != 8 {
		t.Fatalf("C backend: exit=(%d, abnormal=%t), want 8", code, abnormal)
	}
	if got := interpretChecked(t, source); got != 8 {
		t.Fatalf("interpreter scored %d of 8", got)
	}
}
