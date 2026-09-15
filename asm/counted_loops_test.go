package asm

import (
	"strings"
	"testing"
)

// A counted loop whose body holds a loop is summarized rather than
// unrolled on the Oak side: one event for the outer loop, one for the
// inner, where sixteen unrolled copies would each summarize the inner
// loop again (docs/spec/94-assembler.md §8, "The literal scanner's kernel
// proven").
func TestOakCountedLoopOverLoopSummarized(t *testing.T) {
	decl := "hits_of: (v: []u8, first: u32, last: u32) -> u32"
	oak := "{\n  hits: u32 = u32(0)\n  l: u32 = u32(0)\n  while l < u32(16) {\n    j: u32 = first\n    while j < last {\n      v[l] == v[j] ? { hits = hits + u32(1) } | { }\n      j = j + u32(1)\n    }\n    l = l + u32(1)\n  }\n  hits\n}"
	spec, err := parseSignatureWithBody(decl + " = " + oak)
	if err != nil {
		t.Fatal(err)
	}
	lo := newLowering(spec)
	if _, reason, ok := lo.lower(spec.Body, 32); !ok {
		t.Fatalf("the body must lower with both loops summarized, got: %s", reason)
	}
	if len(lo.loops) != 2 {
		t.Fatalf("two loop events expected (the counted loop summarized over its inner loop), got %d", len(lo.loops))
	}
	if strings.Join(lo.loops[0].vars, ",") != "hits,l" && strings.Join(lo.loops[0].vars, ",") != "l,hits" {
		t.Fatalf("the outer event must carry hits and l, got %v", lo.loops[0].vars)
	}
	if lo.loops[1].parent != 1 {
		t.Fatalf("the inner event must nest under the outer, got parent %d", lo.loops[1].parent)
	}
	if !bodyHasLoop(spec.Body, nil) {
		t.Fatal("bodyHasLoop must see the loops")
	}
}

// A counted loop over a loop with few trips is unrolled as before: its
// copies are few, and a two-sided body keeps its inner events per side
// on the machine (docs/spec/94-assembler.md §8, countedUnrollLimit).
func TestOakShortCountedLoopOverLoopUnrolls(t *testing.T) {
	decl := "both_sides: (v: []u8, a: u32, b: u32) -> u32"
	oak := "{\n  n: u32 = u32(0)\n  side: u32 = u32(0)\n  while side < u32(2) {\n    c: u32 = side == u32(0) ? { a } | { b }\n    j: u32 = u32(0)\n    while j < c {\n      n = n + u32(v[j])\n      j = j + u32(1)\n    }\n    side = side + u32(1)\n  }\n  n\n}"
	spec, err := parseSignatureWithBody(decl + " = " + oak)
	if err != nil {
		t.Fatal(err)
	}
	lo := newLowering(spec)
	if _, reason, ok := lo.lower(spec.Body, 32); !ok {
		t.Fatalf("the body must lower, got: %s", reason)
	}
	if len(lo.loops) != 2 || lo.loops[0].parent != 0 || lo.loops[1].parent != 0 {
		t.Fatalf("two trips unroll: two top-level inner events expected, got %d", len(lo.loops))
	}
}

// A counted loop over a loop-free body is unrolled as before.
func TestOakCountedLoopWithoutLoopUnrolls(t *testing.T) {
	decl := "sum_of: (v: []u8) -> u32"
	oak := "{\n  acc: u32 = u32(0)\n  l: u32 = u32(0)\n  while l < u32(4) {\n    acc = acc + u32(v[l])\n    l = l + u32(1)\n  }\n  acc\n}"
	spec, err := parseSignatureWithBody(decl + " = " + oak)
	if err != nil {
		t.Fatal(err)
	}
	lo := newLowering(spec)
	if _, reason, ok := lo.lower(spec.Body, 32); !ok {
		t.Fatalf("the body must lower, got: %s", reason)
	}
	if len(lo.loops) != 0 {
		t.Fatalf("a counted loop over a loop-free body unrolls; got %d events", len(lo.loops))
	}
}

// A vector parameter's witnesses are its lanes, one of them set; a span
// indexed by scalar parameters gets a family of long spans with small
// scalars; a wide element of the fixed memory stays small.
func TestLoopWitnessInputsVectorLanesAndLongSpans(t *testing.T) {
	spec, err := parseSignatureWithBody("f: (cand: simd.U8x16, bytes: []u8, base: u32, first: u32) -> u32 = { base }")
	if err != nil {
		t.Fatal(err)
	}
	inputs := loopWitnessInputs(&Function{}, spec)
	long := 0
	for _, env := range inputs {
		set := 0
		for k := 0; k < 16; k++ {
			v, bound := env[spanElemName("cand", int64(k))]
			if !bound {
				t.Fatalf("lane %d of cand unbound in %v", k, env)
			}
			if v != 0 {
				set++
			}
		}
		if set != 1 {
			t.Fatalf("one lane of cand must be set, %d are in %v", set, env)
		}
		if env["len(bytes)"] == 80 && env["base"] <= 17 && env["first"] <= 18 {
			long++
		}
	}
	if long == 0 {
		t.Fatal("the long-span family is missing")
	}
	if elementValue("starts", 12, 32) >= 23 || elementValue("bytes", 12, 8) == elementValue("bytes", 13, 8) && elementValue("bytes", 12, 8) == elementValue("bytes", 14, 8) {
		t.Fatalf("wide elements stay small (%d) and bytes keep the mix", elementValue("starts", 12, 32))
	}
}

// Sibling loop events created out of layout order — a fork's first side
// summarizing the loop past the meeting point before the other side's
// loop — are what send the executor back to run with joins.
func TestLoopsInLayoutOrder(t *testing.T) {
	x := &pathExecutor{loops: []*loopEvent{{index: 1, at: 10}, {index: 2, parent: 1, at: 12}, {index: 3, at: 40}, {index: 4, at: 25}}}
	if x.loopsInLayoutOrder() {
		t.Fatal("a top-level loop at 25 created after one at 40 is out of order")
	}
	x.loops = []*loopEvent{{index: 1, at: 10}, {index: 2, parent: 1, at: 12}, {index: 3, at: 25}, {index: 4, parent: 3, at: 30}, {index: 5, parent: 3, at: 30}, {index: 6, at: 40}}
	if !x.loopsInLayoutOrder() {
		t.Fatal("siblings in increasing order, a call's loops at one place, are in order")
	}
}
