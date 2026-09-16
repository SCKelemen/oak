package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A record result returned through memory is verified in one run for all
// of its words (docs/spec/94-assembler.md §9): the executor's ret
// assembles every word of the result area, the Oak body lowers once and
// packs every word, and one witness pass and one coupling decide them all
// — where a run per word ran the pipeline thirty-two times for a 256-byte
// record. The shape is the prover's add_bits: a wrapper returning a
// callee's record field, the callee filling the array in a loop.
const nativeRecordWordsProgram = `
Bits: type = struct { at: [64]u32 }
Sum: type = struct { bits: Bits, carry: u32 }

add_carry: (a: Bits, b: Bits, carry: u32, w: u32): Sum {
  out: Bits
  c: u32 = carry
  i: u32 = 0
  while i < w {
    s: u32 = a.at[i] + b.at[i] + c
    out.at[i] = s
    c = s >> u32(30)
    i = i + u32(1)
  }
  Sum { bits: out, carry: c }
}

add_bits: (a: Bits, b: Bits, carry: u32, w: u32): Bits = add_carry(a, b, carry, w).bits

main: (): i32 {
  a: Bits
  b: Bits
  a.at[0] = u32(1073741824)
  b.at[0] = u32(1073741824)
  a.at[1] = u32(5)
  r: Bits = add_bits(a, b, u32(0), u32(2))
  assert(r.at[0] == u32(2147483648))
  assert(r.at[1] == u32(7))
  42
}
`

func TestE2ENativeRecordWords(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("words.oak", nativeRecordWordsProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_record_words", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native record words: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	// The wrapper's thirty-two words: proven in one run, under the
	// callee's summary (its record stored into the frame at x8).
	if !strings.Contains(joined, "asm unit add_bits: proven equal to its Oak body") || !strings.Contains(joined, "(all 32 result chunks)") {
		t.Errorf("add_bits returns a 256-byte record through the result area and must be proven for all 32 words; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_record_words_c", New().WithSource("words.oak", nativeRecordWordsProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
