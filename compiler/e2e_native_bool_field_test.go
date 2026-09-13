package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

// A record passed by reference is copied through the frame in 8-byte words;
// a Bool field (the 4-byte C enum, a 1-bit leaf in the verifier's model) at
// the start of a word must be read as that field. The verifier once dropped
// such a leaf as zero-width and refuted the standard library's correct
// `!parsed.scheme.present` (docs/spec/94-assembler.md §8); every native
// verdict here must be a proof or evidence, never a mismatch, and the
// program runs the same natively and through C.
const nativeBoolFieldProgram = `Range: type = struct { start: u32, end: u32, present: Bool }
Pair: type = struct { a: Range, b: Range }

first_absent: (p: Pair): Bool = !p.a.present
second_present: (p: Pair): Bool = p.b.present && !p.a.present

main: (): i32 {
  p: Pair = Pair { a: Range { start: u32(1), end: u32(2), present: true }, b: Range { start: u32(3), end: u32(4), present: false } }
  q: Pair = Pair { a: Range { start: u32(0), end: u32(0), present: false }, b: Range { start: u32(0), end: u32(9), present: true } }
  first_absent(p) ? i32(1) | second_present(p) ? i32(2) | !first_absent(q) ? i32(3) | !second_present(q) ? i32(4) | i32(0)
}
`

func TestE2ENativeBoolFieldAtWordStart(t *testing.T) {
	tgt, err := target.Parse("freestanding/arm64")
	if err != nil {
		t.Fatal(err)
	}
	var native []string
	sink := func(d *diagnostic.Diagnostic) {
		if strings.HasPrefix(d.Message, "native backend: ") {
			native = append(native, d.Message)
		}
	}
	comp := New().WithSource("boolfield.oak", nativeBoolFieldProgram).WithTarget(tgt).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(sink)
	if _, err := comp.EmitC().Get(); err != nil {
		t.Fatalf("native build: %v", err)
	}
	for _, fn := range []string{"first_absent", "second_present"} {
		found := false
		for _, m := range native {
			if !strings.Contains(m, "asm unit "+fn+":") && !strings.Contains(m, "asm unit "+fn+" ") {
				continue
			}
			found = true
			if strings.Contains(m, "disagrees") || strings.Contains(m, "not verified") {
				t.Errorf("%s: want a proof or evidence, got: %s", fn, m)
			}
		}
		if !found {
			t.Errorf("%s: no native verdict (left to the C backend?):\n%s", fn, strings.Join(native, "\n"))
		}
	}
	if _, exit, abnormal := buildAndRunFrom(t, "native_bool_field", New().WithSource("boolfield.oak", nativeBoolFieldProgram)); abnormal || exit != 0 {
		t.Fatalf("program: exit = (%d, abnormal=%v), want 0", exit, abnormal)
	}
}
