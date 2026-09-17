package nativegen

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/machine"
	"github.com/SCKelemen/oak/opt"
)

const recordBaseAssembly = `
  cmp w2, w1
  b.hs trap
  movz w9, #16384
  movk w9, #6, lsl #16
  umaddl x10, w2, w9, x0
  add x11, x10, #8
  ldr x4, [x11]
  cmp x4, #0
  b.eq skip
  add x4, x4, #1
skip:
  movz w9, #16384
  movk w9, #6, lsl #16
  umaddl x12, w2, w9, x0
  str x4, [x12, #16]
  mov x0, x4
  ret
trap:
  brk #1`

func recordBaseFunction(t *testing.T, body, clobbers string) *asm.Function {
	t.Helper()
	unit, errs := asm.ParseUnit("record_base.oakasm", "f: (v: [*]u64, i: u32): u64 = {\n  bind x0, w1 = v\n  bind w2 = i\n  clobber "+clobbers+"\n"+body+"\n}\n")
	if len(errs) > 0 {
		t.Fatal(errs)
	}
	return unit.Functions[0]
}

func TestShareRecordBase(t *testing.T) {
	// The stride temporary of the retained first definition may remain live;
	// only a later materialization which the pass deletes must be dead.
	body := strings.Replace(recordBaseAssembly, "  add x11, x10, #8", "  add w9, w9, #0\n  add x11, x10, #8", 1)
	fn := recordBaseFunction(t, body, "x4, x9, x10, x11, x12, x17, x0")
	fn.Arch = "" // The native AArch64 lane uses the default architecture tag.
	if n := shareRecordBase(fn); n != 1 {
		t.Fatalf("shared %d bases, want one:\n%s", n, Describe(fn))
	}
	text := Describe(fn)
	if strings.Count(text, "umaddl") != 1 || !strings.Contains(text, "umaddl x17, w2, w9, x0") ||
		!strings.Contains(text, "add x11, x17, #8") || !strings.Contains(text, "str x4, [x17, #16]") {
		t.Fatalf("record base was not carried in x17:\n%s", text)
	}
	if n := shareRecordBase(fn); n != 0 {
		t.Fatalf("pass is not idempotent: shared %d again", n)
	}
	transform, found := Registry().Lookup(TransformRecordBases)
	if !found {
		t.Fatal("missing record-base candidate")
	}
	if gated, ok := transform.(opt.Gated); !ok || !gated.NeedsVerdict() {
		t.Fatal("record-base sharing must require a semantic verdict")
	}
	if !transform.Apply(opt.Identity(PlainLane(Lane{Arch: asm.ArchArm64}))).Config.(Lane).ShareRecordBases ||
		PlainLane(Lane{ShareRecordBases: true}).ShareRecordBases {
		t.Fatal("candidate toggle or identity fallback")
	}
}

func TestReuseRecordBaseDestination(t *testing.T) {
	carried := strings.Replace(recordBaseAssembly, "skip:\n", "skip:\n  add x4, x4, x10\n", 1)
	fn := recordBaseFunction(t, carried, "x4, x9, x10, x11, x12, x17, x0")
	if n := reuseRecordBaseDestination(fn); n != 1 {
		t.Fatalf("reused %d existing destinations, want one:\n%s", n, Describe(fn))
	}
	text := Describe(fn)
	if strings.Count(text, "umaddl") != 1 || !strings.Contains(text, "umaddl x10, w2, w9, x0") ||
		!strings.Contains(text, "add x4, x4, x10") || !strings.Contains(text, "str x4, [x10, #16]") || strings.Contains(text, "umaddl x17") {
		t.Fatalf("first record base was not retained as the carrier:\n%s", text)
	}

	clobbered := strings.Replace(recordBaseAssembly, "skip:\n", "skip:\n  add x10, x0, #0\n", 1)
	fn = recordBaseFunction(t, clobbered, "x4, x9, x10, x11, x12, x17, x0")
	before := Describe(fn)
	if n := reuseRecordBaseDestination(fn); n != 0 || Describe(fn) != before {
		t.Fatalf("clobbered first destination was reused %d times:\n%s", n, Describe(fn))
	}

	for name, body := range map[string]string{
		"call between":         strings.Replace(recordBaseAssembly, "skip:\n", "skip:\n  bl helper\n", 1),
		"index changes":        strings.Replace(recordBaseAssembly, "skip:\n", "skip:\n  add w2, w2, #1\n", 1),
		"first not dominating": strings.Replace(recordBaseAssembly, "  movz w9, #16384", "  cbz w4, skip\n  movz w9, #16384", 1),
		"machine loop":         strings.Replace(recordBaseAssembly, "  cmp w2, w1", "loop:\n  cbnz w4, loop\n  cmp w2, w1", 1),
	} {
		t.Run(name, func(t *testing.T) {
			fn := recordBaseFunction(t, body, "x4, x9, x10, x11, x12, x17, x0")
			before := Describe(fn)
			if n := reuseRecordBaseDestination(fn); n != 0 || Describe(fn) != before {
				t.Fatalf("unsafe shape reused %d destinations:\n%s", n, Describe(fn))
			}
		})
	}

	transform, found := Registry().Lookup(TransformRecordBaseCarriers)
	if !found {
		t.Fatal("missing record-base carrier candidate")
	}
	if gated, ok := transform.(opt.Gated); !ok || !gated.NeedsVerdict() {
		t.Fatal("record-base carrier reuse must require a semantic verdict")
	}
	identity := opt.Identity(PlainLane(Lane{Arch: asm.ArchArm64}))
	if transform.Apply(identity) != nil {
		t.Fatal("record-base carrier candidate applied without its parent")
	}
	parent := identity.Config.(Lane)
	parent.Schedule, parent.ShareRecordBases = true, true
	next := transform.Apply(opt.Identity(parent))
	if next == nil || !next.Config.(Lane).ReuseRecordBaseDestinations || PlainLane(next.Config.(Lane)).ReuseRecordBaseDestinations {
		t.Fatal("record-base carrier candidate toggle or identity fallback")
	}
	closure, found := Registry().Lookup(TransformRecordBaseClosure)
	if !found {
		t.Fatal("missing remaining record-base carrier candidate")
	}
	if gated, ok := closure.(opt.Gated); !ok || !gated.NeedsVerdict() {
		t.Fatal("remaining record-base carrier reuse must require a semantic verdict")
	}
	if closure.Apply(identity) != nil {
		t.Fatal("remaining record-base carrier reuse applied without its parents")
	}
	parent.ReuseRecordBaseDestinations = true
	next = closure.Apply(opt.Identity(parent))
	if next == nil || !next.Config.(Lane).ReuseRemainingRecordBaseDestinations || PlainLane(next.Config.(Lane)).ReuseRemainingRecordBaseDestinations {
		t.Fatal("remaining record-base carrier toggle or identity fallback")
	}

	reschedule, found := Registry().Lookup(TransformRecordBaseSchedule)
	if !found {
		t.Fatal("missing record-base carrier rescheduling candidate")
	}
	if gated, ok := reschedule.(opt.Gated); !ok || !gated.NeedsVerdict() {
		t.Fatal("record-base carrier rescheduling must require a semantic verdict")
	}
	if reschedule.Apply(identity) != nil {
		t.Fatal("record-base carrier rescheduling applied without its parents")
	}
	parent.RescheduleRecordBaseCarriers = false
	parent.ReuseRecordBaseDestinations = true
	next = reschedule.Apply(opt.Identity(parent))
	if next == nil || !next.Config.(Lane).RescheduleRecordBaseCarriers || PlainLane(next.Config.(Lane)).RescheduleRecordBaseCarriers {
		t.Fatal("record-base carrier rescheduling toggle or identity fallback")
	}
}

func TestReuseRemainingRecordBaseDestinations(t *testing.T) {
	body := `
  movz w9, #16384
  movk w9, #6, lsl #16
  umaddl x10, w2, w9, x0
  ldr x4, [x10]
  movz w9, #16384
  movk w9, #6, lsl #16
  umaddl x11, w2, w9, x0
  add x4, x4, x11
  movz w9, #8192
  umaddl x12, w2, w9, x0
  ldr x5, [x12]
  movz w9, #8192
  umaddl x13, w2, w9, x0
  add x5, x5, x13
  add x0, x4, x5
  ret`
	fn := recordBaseFunction(t, body, "x4, x5, x9, x10, x11, x12, x13, x0")
	if n := reuseRecordBaseDestination(fn); n != 1 {
		t.Fatalf("parent reused %d groups, want one:\n%s", n, Describe(fn))
	}
	if n := reuseRemainingRecordBaseDestinations(fn); n != 1 {
		t.Fatalf("closure reused %d remaining groups, want one:\n%s", n, Describe(fn))
	}
	if text := Describe(fn); strings.Count(text, "umaddl") != 2 {
		t.Fatalf("remaining bases were not closed to a fixed point:\n%s", text)
	}
	if n := reuseRemainingRecordBaseDestinations(fn); n != 0 {
		t.Fatalf("fixed-point closure reused %d groups again", n)
	}
}

func TestRescheduleForFewerStalls(t *testing.T) {
	body := `
  ldr w9, [x0]
  add w10, w9, #1
  add w11, w1, #2
  add w12, w2, #3
  str w11, [x0, #8]
  cmp w10, w12
  b.hs done
  ret
done:
  ret`
	fn := recordBaseFunction(t, body, "x9, x10, x11, x12")
	beforeStalls, _ := machine.StallEstimate(fn)
	if moved, err := rescheduleForFewerStalls(fn); err != nil || moved == 0 {
		t.Fatalf("moved %d: %v", moved, err)
	}
	afterStalls, _ := machine.StallEstimate(fn)
	if afterStalls >= beforeStalls {
		t.Fatalf("stalls %d -> %d:\n%s", beforeStalls, afterStalls, Describe(fn))
	}

	neutral := recordBaseFunction(t, "  mov x0, x0\n  ret", "x0")
	before := Describe(neutral)
	if moved, err := rescheduleForFewerStalls(neutral); err != nil || moved != 0 || Describe(neutral) != before {
		t.Fatalf("neutral schedule moved %d: %v\n%s", moved, err, Describe(neutral))
	}
}

func TestShareRecordBasePreservesScheduledInterleaving(t *testing.T) {
	body := strings.Replace(recordBaseAssembly,
		"  movz w9, #16384\n  movk w9, #6, lsl #16\n  umaddl x10, w2, w9, x0",
		"  movz w9, #16384\n  add x11, x0, #0\n  movk w9, #6, lsl #16\n  orr w1, w1, w1\n  umaddl x10, w2, w9, x0", 1)
	body = strings.Replace(body,
		"  movz w9, #16384\n  movk w9, #6, lsl #16\n  umaddl x12, w2, w9, x0",
		"  movz w9, #16384\n  str x4, [x0]\n  movk w9, #6, lsl #16\n  add x11, x11, #0\n  umaddl x12, w2, w9, x0", 1)
	fn := recordBaseFunction(t, body, "x4, x9, x10, x11, x12, x17, x0")
	if n := shareRecordBase(fn); n != 1 {
		t.Fatalf("shared %d interleaved bases, want one:\n%s", n, Describe(fn))
	}
	text := Describe(fn)
	for _, kept := range []string{"add x11, x0, #0", "orr w1, w1, w1", "str x4, [x0]", "add x11, x11, #0"} {
		if !strings.Contains(text, kept) {
			t.Fatalf("scheduled instruction %q was not preserved:\n%s", kept, text)
		}
	}
	if strings.Count(text, "umaddl") != 1 || !strings.Contains(text, "umaddl x17, w2, w9, x0") ||
		!strings.Contains(text, "str x4, [x17, #16]") {
		t.Fatalf("interleaved record base was not carried in x17:\n%s", text)
	}
}

func TestShareRecordBaseRefusals(t *testing.T) {
	allScratchUsed := recordBaseAssembly
	for _, reg := range []string{"x9", "x10", "x11", "x12", "x13", "x14", "x15", "x16", "x17"} {
		allScratchUsed = strings.Replace(allScratchUsed, "  mov x0, x4", "  add "+reg+", "+reg+", #0\n  mov x0, x4", 1)
	}
	tooWide := strings.Repeat("  orr w4, w4, w4\n", recordBaseMaterializationSpan)
	for name, body := range map[string]string{
		"one site":                        strings.Replace(recordBaseAssembly, "  movz w9, #16384\n  movk w9, #6, lsl #16\n  umaddl x12, w2, w9, x0\n", "", 1),
		"index changes":                   strings.Replace(recordBaseAssembly, "skip:\n", "skip:\n  add w2, w2, #1\n", 1),
		"base changes":                    strings.Replace(recordBaseAssembly, "skip:\n", "skip:\n  add x0, x0, #8\n", 1),
		"call between":                    strings.Replace(recordBaseAssembly, "skip:\n", "skip:\n  bl helper\n", 1),
		"different low":                   strings.Replace(recordBaseAssembly, "  movz w9, #16384\n  movk w9, #6, lsl #16\n  umaddl x12", "  movz w9, #8\n  movk w9, #6, lsl #16\n  umaddl x12", 1),
		"different high":                  strings.Replace(recordBaseAssembly, "  movk w9, #6, lsl #16\n  umaddl x12", "  movk w9, #7, lsl #16\n  umaddl x12", 1),
		"destination live through label":  strings.Replace(recordBaseAssembly, "  add x11, x10, #8", "  b use_base\nuse_base:\n  add x11, x10, #8", 1),
		"deleted stride stays live":       strings.Replace(recordBaseAssembly, "  str x4, [x12, #16]", "  add w9, w9, #1\n  str x4, [x12, #16]", 1),
		"stride read before movk":         strings.Replace(recordBaseAssembly, "  movz w9, #16384\n  movk w9", "  movz w9, #16384\n  add w4, w9, #0\n  movk w9", 1),
		"stride write before movk":        strings.Replace(recordBaseAssembly, "  movz w9, #16384\n  movk w9", "  movz w9, #16384\n  add w9, w4, #0\n  movk w9", 1),
		"stride read before umaddl":       strings.Replace(recordBaseAssembly, "  movk w9, #6, lsl #16\n  umaddl x12", "  movk w9, #6, lsl #16\n  add w4, w9, #0\n  umaddl x12", 1),
		"branch inside materialization":   strings.Replace(recordBaseAssembly, "  movz w9, #16384\n  movk w9", "  movz w9, #16384\n  b materialization_tail\nmaterialization_tail:\n  movk w9", 1),
		"input changes inside later site": strings.Replace(recordBaseAssembly, "skip:\n  movz w9, #16384", "skip:\n  movz w9, #16384\n  add w2, w2, #1", 1),
		"materialization too wide":        strings.Replace(recordBaseAssembly, "  movz w9, #16384\n  movk w9", "  movz w9, #16384\n"+tooWide+"  movk w9", 1),
		"stride aliases index":            strings.ReplaceAll(recordBaseAssembly, "w9", "w2"),
		"stride aliases base":             strings.ReplaceAll(recordBaseAssembly, "w9", "w0"),
		"machine loop":                    strings.Replace(recordBaseAssembly, "  cmp w2, w1", "loop:\n  cbnz w4, loop\n  cmp w2, w1", 1),
		"no free scratch":                 allScratchUsed,
	} {
		t.Run(name, func(t *testing.T) {
			fn := recordBaseFunction(t, body, "x4, x9, x10, x11, x12, x13, x14, x15, x16, x17, x0")
			before := Describe(fn)
			if n := shareRecordBase(fn); n != 0 || Describe(fn) != before {
				t.Fatalf("unsafe shape shared %d bases:\n%s", n, Describe(fn))
			}
		})
	}
	fn := recordBaseFunction(t, recordBaseAssembly, "x4, x9, x10, x11, x12, x0")
	if n := shareRecordBase(fn); n != 0 {
		t.Fatalf("an undeclared scratch was used: %d", n)
	}
}
