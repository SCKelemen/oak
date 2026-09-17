package nativegen

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
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

func TestShareRecordBaseRefusals(t *testing.T) {
	allScratchUsed := recordBaseAssembly
	for _, reg := range []string{"x9", "x10", "x11", "x12", "x13", "x14", "x15", "x16", "x17"} {
		allScratchUsed = strings.Replace(allScratchUsed, "  mov x0, x4", "  add "+reg+", "+reg+", #0\n  mov x0, x4", 1)
	}
	for name, body := range map[string]string{
		"one site":                       strings.Replace(recordBaseAssembly, "  movz w9, #16384\n  movk w9, #6, lsl #16\n  umaddl x12, w2, w9, x0\n", "", 1),
		"index changes":                  strings.Replace(recordBaseAssembly, "skip:\n", "skip:\n  add w2, w2, #1\n", 1),
		"base changes":                   strings.Replace(recordBaseAssembly, "skip:\n", "skip:\n  add x0, x0, #8\n", 1),
		"call between":                   strings.Replace(recordBaseAssembly, "skip:\n", "skip:\n  bl helper\n", 1),
		"different low":                  strings.Replace(recordBaseAssembly, "  movz w9, #16384\n  movk w9, #6, lsl #16\n  umaddl x12", "  movz w9, #8\n  movk w9, #6, lsl #16\n  umaddl x12", 1),
		"different high":                 strings.Replace(recordBaseAssembly, "  movk w9, #6, lsl #16\n  umaddl x12", "  movk w9, #7, lsl #16\n  umaddl x12", 1),
		"destination live through label": strings.Replace(recordBaseAssembly, "  add x11, x10, #8", "  b use_base\nuse_base:\n  add x11, x10, #8", 1),
		"deleted stride stays live":      strings.Replace(recordBaseAssembly, "  str x4, [x12, #16]", "  add w9, w9, #1\n  str x4, [x12, #16]", 1),
		"machine loop":                   strings.Replace(recordBaseAssembly, "  cmp w2, w1", "loop:\n  cbnz w4, loop\n  cmp w2, w1", 1),
		"no free scratch":                allScratchUsed,
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
