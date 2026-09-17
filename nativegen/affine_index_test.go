package nativegen

import (
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/opt"
)

const affineFillAssembly = `  mov w6, wzr
  cmp w6, #2048
  b.hs done_1
  lsl w15, w2, #11
  movz w16, #49152
  cmp w6, #2048
  b.hs done_1
loop_1:
  add w7, w15, w6
  cmp w7, w16
  b.hs trap_1
  str xzr, [x0, w7, uxtw #3]
  add w6, w6, #1
  cmp w6, #2048
  b.lo loop_1
done_1:
  ret
trap_1:
  brk #1`

func affineFillItems(t *testing.T, body string) *asm.Function {
	t.Helper()
	unit, errs := asm.ParseUnit("affine.oakasm", "fill: (v: [*]u64, base: u32): () = {\n  bind x0, w1 = v\n  bind w2 = base\n  clobber w6, w7, w15, w16\n"+body+"\n}\n")
	if len(errs) > 0 {
		t.Fatal(errs)
	}
	return unit.Functions[0]
}

func TestCarryLoopIndices(t *testing.T) {
	for _, commuted := range []bool{false, true} {
		body := affineFillAssembly
		if commuted {
			body = strings.Replace(body, "w7, w15, w6", "w7, w6, w15", 1)
		}
		fn := affineFillItems(t, body)
		before := Describe(fn)
		out, n := carryLoopIndices(fn.Items)
		if Describe(fn) != before {
			t.Fatal("candidate mutated its parent's items")
		}
		fn.Items = out
		text := Describe(fn)
		if n != 1 || !strings.Contains(text, "add w6, w15, #2048") ||
			!strings.Contains(text, "loop_1:\n  cmp w7, w16") ||
			!strings.Contains(text, "add w7, w7, #1\n  cmp w7, w6\n  b.ne loop_1") {
			t.Fatalf("carried index (%d):\n%s", n, text)
		}
		if twice, n := carryLoopIndices(out); n != 0 || !reflect.DeepEqual(twice, out) {
			t.Fatal("pass must be idempotent")
		}
	}
	var found bool
	for _, transform := range Transforms() {
		if transform.Name() != TransformCarryIndex {
			continue
		}
		found = true
		gated, ok := transform.(opt.Gated)
		if !ok || !gated.NeedsVerdict() {
			t.Fatal("carried indices must require a proven verdict")
		}
	}
	if !found || PlainLane(Lane{CarryLoopIndices: true}).CarryLoopIndices {
		t.Fatal("missing candidate or identity fallback")
	}
}

func TestCarryLoopIndicesRefusals(t *testing.T) {
	for name, body := range map[string]string{
		"nonzero start":          strings.Replace(affineFillAssembly, "mov w6, wzr", "movz w6, #1", 1),
		"unknown start":          strings.Replace(affineFillAssembly, "mov w6, wzr", "mov w6, w2", 1),
		"zero trips":             strings.ReplaceAll(affineFillAssembly, "#2048", "#0"),
		"wide trips":             strings.ReplaceAll(affineFillAssembly, "#2048", "#4096"),
		"wide counter":           strings.ReplaceAll(affineFillAssembly, "w6", "x6"),
		"different tail":         strings.Replace(affineFillAssembly, "cmp w6, #2048\n  b.lo", "cmp w6, #2047\n  b.lo", 1),
		"wrong stride":           strings.Replace(affineFillAssembly, "w6, w6, #1", "w6, w6, #2", 1),
		"counter is base":        strings.Replace(affineFillAssembly, "w7, w15, w6", "w7, w6, w6", 1),
		"index is counter":       strings.ReplaceAll(affineFillAssembly, "w7", "w6"),
		"index is base":          strings.ReplaceAll(affineFillAssembly, "w7", "w15"),
		"guard reads counter":    strings.Replace(affineFillAssembly, "cmp w7, w16", "cmp w7, w6", 1),
		"store reads counter":    strings.Replace(affineFillAssembly, "str xzr", "str x6", 1),
		"store base is counter":  strings.Replace(affineFillAssembly, "[x0,", "[x6,", 1),
		"store base is index":    strings.Replace(affineFillAssembly, "[x0,", "[x7,", 1),
		"different memory index": strings.Replace(affineFillAssembly, "[x0, w7", "[x0, w15", 1),
		"observable exit":        strings.Replace(affineFillAssembly, "brk #1", "ret", 1),
		"counter live out":       strings.Replace(affineFillAssembly, "done_1:\n  ret", "done_1:\n  mov w0, w6\n  ret", 1),
		"index live out":         strings.Replace(affineFillAssembly, "done_1:\n  ret", "done_1:\n  mov w0, w7\n  ret", 1),
		"extra entry":            "  b loop_1\n" + affineFillAssembly,
		"entry before zero":      strings.Replace(affineFillAssembly, "  lsl w15", "entry:\n  lsl w15", 1),
		"call after zero":        strings.Replace(affineFillAssembly, "  lsl w15", "  bl helper\n  lsl w15", 1),
		"extra body instruction": strings.Replace(affineFillAssembly, "  str xzr", "  add w15, w15, #1\n  str xzr", 1),
	} {
		t.Run(name, func(t *testing.T) {
			fn := affineFillItems(t, body)
			before := Describe(fn)
			out, n := carryLoopIndices(fn.Items)
			fn.Items = out
			if n != 0 || Describe(fn) != before {
				t.Fatalf("unsafe shape changed (%d):\n%s", n, Describe(fn))
			}
		})
	}
}
