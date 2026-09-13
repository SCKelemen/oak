package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

// Aggregate results in the verifier (docs/spec/94-assembler.md §9, "Record
// results of two chunks, aggregate call summaries"): a record of 9 to 16
// bytes comes back in two register chunks and is verified chunk by chunk;
// a call to a function returning a record or a sum type is taken at the
// callee's aggregate value; the bytes of a frame slot no store reached are
// unknowns, not a refusal. Every function below is proven on both lanes.
const nativeVerdictAggregatesProgram = `Pair: type = struct {
  lo: u64
  hi: u64
}

Tagged: type = struct {
  value: u32
  kind: u8
}

Parsed: type =
  | Ok: u32
  | Err: u8

swap: (p: Pair) -> Pair = Pair { lo: p.hi, hi: p.lo }

make_pair: (a: u64, b: u64) -> Pair = Pair { lo: a + b, hi: a - b }

pair_sum: (a: u64, b: u64) -> u64 {
  p: Pair = make_pair(a, b)
  q: Pair = swap(p)
  p.lo + q.lo
}

classify: (v: u32) -> Parsed = v > u32(100) ? .Err(u8(1)) | .Ok(v * u32(2))

unwrap_or: (v: u32, d: u32) -> u32 = classify(v) ? | .Ok(x) => x | .Err(code) => d + u32(code)

tag_of: (t: Tagged) -> u32 = t.kind == u8(0) ? t.value | u32(t.kind)

main: (): i32 {
  i32_bits_u32(u32_trunc_u64(pair_sum(u64(7), u64(3))) + unwrap_or(u32(4), u32(9)) + unwrap_or(u32(200), u32(9)) + tag_of(Tagged { value: u32(5), kind: u8(0) }) - u32(14) - u32(8) - u32(10) - u32(5))
}
`

func TestE2ENativeAggregateVerdictsProven(t *testing.T) {
	for _, tname := range []string{"freestanding/arm64", "linux/riscv64"} {
		tgt, err := target.Parse(tname)
		if err != nil {
			t.Fatal(err)
		}
		var native []string
		sink := func(d *diagnostic.Diagnostic) {
			if strings.HasPrefix(d.Message, "native backend: ") {
				native = append(native, d.Message)
			}
		}
		comp := New().WithSource("aggregates.oak", nativeVerdictAggregatesProgram).WithTarget(tgt).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(sink)
		if _, err := comp.EmitC().Get(); err != nil {
			t.Fatalf("%s: native build: %v", tname, err)
		}
		joined := strings.Join(native, "\n")
		for _, fn := range []string{"swap", "make_pair", "pair_sum", "classify", "unwrap_or", "tag_of"} {
			verdict := ""
			for _, m := range native {
				if strings.Contains(m, "asm unit "+fn+":") {
					verdict = m
				}
			}
			if verdict == "" {
				t.Errorf("%s: %s: no native verdict:\n%s", tname, fn, joined)
				continue
			}
			if !strings.Contains(verdict, "proven equal") {
				t.Errorf("%s: %s is not proven: %s", tname, fn, verdict)
			}
		}
		for _, fn := range []string{"swap", "make_pair"} {
			for _, m := range native {
				if strings.Contains(m, "asm unit "+fn+":") && !strings.Contains(m, "both result chunks") {
					t.Errorf("%s: %s should be verified chunk by chunk: %s", tname, fn, m)
				}
			}
		}
		for _, m := range native {
			if strings.Contains(m, "asm unit unwrap_or:") && !strings.Contains(m, "callees taken at their Oak bodies: classify") {
				t.Errorf("%s: unwrap_or should take classify at its Oak body: %s", tname, m)
			}
		}
	}
	if _, exit, abnormal := buildAndRunFrom(t, "native_verdict_aggregates", New().WithSource("aggregates.oak", nativeVerdictAggregatesProgram)); abnormal || exit != 0 {
		t.Fatalf("program: exit = (%d, abnormal=%v), want 0", exit, abnormal)
	}
}
