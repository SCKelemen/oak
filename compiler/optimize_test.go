package compiler

import (
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/opt"
)

func decision(report OptimizationReport, rule OptimizationRule, kind opt.RemarkKind, function, message string) (OptimizationDecision, bool) {
	for _, item := range report.Remarks {
		if item.Transform == rule && item.Kind == kind && item.Function == function && strings.Contains(item.Message, message) {
			return item, true
		}
	}
	return OptimizationDecision{}, false
}

// The source optimizer is opt-in with executable emission. Ordinary semantic
// checking remains the program as written; an optimization request returns a
// deterministic account of the beta reductions that actually happened.
func TestOptimizationReportTracksCheckedInlining(t *testing.T) {
	plain, err := New().WithSource("inline.oak", inlineHelperProgram).Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	if len(plain.Optimizations.Remarks) != 0 {
		t.Fatalf("semantic Check unexpectedly optimized the program: %+v", plain.Optimizations.Remarks)
	}

	comp := New().WithSource("inline.oak", inlineHelperProgram)
	first, err := comp.Optimizations().Get()
	if err != nil {
		t.Fatal(err)
	}
	second, err := comp.Optimizations().Get()
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(first, second) {
		t.Fatalf("optimization reports are not deterministic:\nfirst:  %+v\nsecond: %+v", first, second)
	}
	for _, edge := range []struct{ caller, callee string }{
		{"sum_guarded", "byte_at"},
		{"sum_guarded", "weighted"},
		{"first_small", "byte_at"},
	} {
		item, ok := decision(first, OptimizationInlineLeaf, opt.Passed, edge.caller, "inlined "+edge.callee+" 1 time(s)")
		if !ok || !strings.Contains(item.Message, "optimized program re-typechecked") || len(item.Facts) != 2 {
			t.Errorf("missing checked inline %s -> %s: %+v", edge.caller, edge.callee, first.Remarks)
		}
	}
}

// A public helper is outside the private-leaf rule even when it has the same
// body shape. A report cannot make it eligible.
func TestOptimizationReportDoesNotAuthorizeIneligibleInlining(t *testing.T) {
	report, err := New().WithSource("public.oak", `
pub visible: (x: u32): u32 = x + u32(1)
main: (): i32 = i32_bits_u32(visible(u32(41)))
`).Optimizations().Get()
	if err != nil {
		t.Fatal(err)
	}
	if _, ok := decision(report, OptimizationInlineLeaf, opt.Passed, "main", "inlined visible"); ok {
		t.Fatalf("public helper was reported as inlined: %+v", report.Remarks)
	}
}

// The post-specialization canonicalizer rewrites the tree the first checker
// already rewrote: `size_of[T]()` has become the plain `size_of()` with its
// query recorded by position. The validating checker adopts those records,
// so a program mixing layout builtins with a canonicalizable identity still
// compiles (the u128 and no_padding programs regressed on this).
func TestOptimizerRevalidationKeepsLayoutBuiltins(t *testing.T) {
	src := `
Frame: type = struct {
  op: u64
  size: u32
}
main: (): i32 {
  static_assert(size_of[Frame]() == u32(16))
  static_assert(offset_of[Frame](size) == u32(8))
  x: u32 = size_of[Frame]() + u32(0)
  x == u32(16) ? 42 | 1
}
`
	output, err := New().WithSource("layout.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if !strings.Contains(output, "sizeof(oak_Frame)") {
		t.Fatalf("emitted C lacks the layout query:\n%s", output)
	}
	report, err := New().WithSource("layout.oak", src).Optimizations().Get()
	if err != nil {
		t.Fatal(err)
	}
	if _, ok := decision(report, OptimizationCanonicalInteger, opt.Passed, "main", "add-zero=1"); !ok {
		t.Fatalf("the identity was not canonicalized (the test would not exercise the re-check): %+v", report.Remarks)
	}
}

// The byte-pack recognizer (codegen/byte_pack.go) reads the canonical
// spelling too: lane 0 without its `<< u32(0)` and its `+ u32(0)`, which
// the integer canonicalizer removes before the C backend runs. The pack
// still lowers to one helper with one range check, not four byte reads.
func TestCanonicalBytePackStaysRecognized(t *testing.T) {
	src := `
read32: (src: []u8, at: u32): u32 = ((u32(src[at + u32(0)]) << u32(0)) | (u32(src[at + u32(1)]) << u32(8)) | (u32(src[at + u32(2)]) << u32(16)) | (u32(src[at + u32(3)]) << u32(24)))
main: (): i32 {
  data: [4]u8 = [4]u8{1, 0, 0, 0}
  read32(view(&data), u32(0)) == u32(1) ? 42 | 1
}
`
	report, err := New().WithSource("pack.oak", src).Optimizations().Get()
	if err != nil {
		t.Fatal(err)
	}
	if _, ok := decision(report, OptimizationCanonicalInteger, opt.Passed, "read32", "shift-zero=1"); !ok {
		t.Fatalf("lane 0 was not canonicalized (the test would not exercise the canonical spelling): %+v", report.Remarks)
	}
	output, err := New().WithSource("pack.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if !strings.Contains(output, "oak_byte_pack_le_u32( src, at )") {
		t.Fatalf("the canonical pack was not recognized:\n%s", output)
	}
	if strings.Contains(output, "oak_view_index_u8( src") {
		t.Fatalf("the pack still reads byte by byte:\n%s", output)
	}
}
