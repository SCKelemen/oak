package compiler

import (
	"os"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// TestE2ENativeLiteralsVerdicts pins the verifier's verdicts on the
// literal scanner's kernel (stdlib/literals.oak): `verify_first` and
// `verify_count`, whose bodies read a frame array at the loop's index and
// call `literal_at` inside a nested loop, are proven by coupling their
// three loops, and `build`, whose loop body asserts and stores through
// its table span, is proven with the memory it writes
// (docs/spec/94-assembler.md §8, "The literal scanner's kernel").
func TestE2ENativeLiteralsVerdicts(t *testing.T) {
	requireArm64Host(t)
	src, err := os.ReadFile("../stdlib/literals.oak")
	if err != nil {
		t.Skip(err)
	}
	var infos []string
	comp := New().WithSource("literals.oak", string(src)+"\nmain: (): u32 = u32(0)\n").WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	if _, err := comp.EmitNative(HostObjectFormat()).Get(); err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	joined := strings.Join(infos, "\n")
	for _, fn := range []string{"verify_first_neon_abi", "verify_count_neon_abi"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven equal to its Oak body at the bit level — 3 nested data-dependent loops coupled inductively") {
			t.Errorf("%s must be proven by loop coupling; diagnostics:\n%s", fn, joined)
		}
	}
	if !strings.Contains(joined, "asm unit build: proven equal to its Oak body at the bit level — 2 data-dependent loops coupled inductively") || !strings.Contains(joined, "and the span memory it writes (tables)") {
		t.Errorf("build must be proven with the memory it writes; diagnostics:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit verify_first_neon_abi: proven") || strings.Contains(joined, "verify_first_neon_abi: proven equal to its Oak body at the bit level — 3 nested data-dependent loops coupled inductively (l↔r17, found↔r16, j↔r14, found↔r16, k↔k, same↔same), 0 concrete inputs") {
		t.Errorf("verify_first must be proven with witnesses (vector lanes and long spans); diagnostics:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit longest: proven") {
		t.Errorf("longest must be proven; diagnostics:\n%s", joined)
	}
	// classify takes ten vectors: the ninth and tenth arrive on the stack
	// (the vector class of asm.LayoutArguments), and its straight-line body
	// is proven on both halves; its callers, which pass thirteen vectors
	// beside their spans, are lowered natively too.
	if !strings.Contains(joined, "asm unit classify_neon_abi: proven equal to its Oak body at the bit level (128-bit vector result, both halves)") {
		t.Errorf("classify must be proven on both halves; diagnostics:\n%s", joined)
	}
	for _, fn := range []string{"step_count_neon_abi", "step_first_neon_abi", "count", "find_from"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s must be lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	// The scanner's step functions: their group loop calls classify four
	// times and verify_* under four conditions; the loop bodies' forks
	// merge at their joins and the calls' loops are summarized, so the
	// thirteen loops couple. step_first's `here == n && any(cb)` chain
	// and `here < found ? here | found` meet the machine's negated
	// comparisons, csets, and zero tests through the canonical rules for
	// 1/0 values (docs/spec/94-assembler.md §8, "The scanner's step
	// functions").
	for _, fn := range []string{"step_count_neon_abi", "step_first_neon_abi"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven equal to its Oak body at the bit level — 13 nested data-dependent loops coupled inductively") {
			t.Errorf("%s must be proven by coupling its thirteen loops; diagnostics:\n%s", fn, joined)
		}
	}
	if strings.Contains(joined, "left to the C backend") {
		t.Errorf("every function of the module must be taken by the native backend; diagnostics:\n%s", joined)
	}
}
