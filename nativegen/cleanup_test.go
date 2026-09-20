package nativegen

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

func postScheduleCleanupText(t *testing.T, body string) (string, int) {
	t.Helper()
	unit, errs := asm.ParseUnit("c.oakasm", "f: (a: u32, b: u32) -> u32 = {\n  bind w0 = a\n  bind w1 = b\n  clobber w9, w10, w19\n"+body+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	fn := *unit.Functions[0]
	fn.Arch = ""
	n := postScheduleCleanup(&fn)
	return Describe(&fn), n
}

func cleanupText(t *testing.T, body string) (string, int) {
	t.Helper()
	unit, errs := asm.ParseUnit("c.oakasm", "f: (a: u32, b: u32) -> u32 = {\n  bind w0 = a\n  bind w1 = b\n  clobber w9, w10, w19\n"+body+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	items, n := cleanupItems(unit.Functions[0].Items)
	fn := *unit.Functions[0]
	fn.Items = items
	return Describe(&fn), n
}

// The late cleanup (nativegen/cleanup.go): a copy read once by the next
// instruction is forwarded, a definition copied once writes its
// destination, a branch to the following label goes, and a copy whose
// value is read again stays.
func TestCleanupCopies(t *testing.T) {
	// Rule 1: the copy feeds one compare-and-branch.
	out, n := cleanupText(t, "  mov w10, w1\n  cbz w10, zero\n  mov w0, w0\n  ret\nzero:\n  movz w0, #7\n  ret")
	if n != 2 || !strings.Contains(out, "cbz w1, zero") || strings.Contains(out, "mov w10, w1") || strings.Contains(out, "mov w0, w0") {
		t.Fatalf("the copy must be forwarded into cbz and the self-move dropped (%d removed):\n%s", n, out)
	}
	// Rule 1 does not fire when the copy is read again.
	out, n = cleanupText(t, "  mov w10, w1\n  add w9, w10, #1\n  add w0, w9, w10\n  ret")
	if n != 0 || !strings.Contains(out, "mov w10, w1") {
		t.Fatalf("a copy read twice must stay (%d removed):\n%s", n, out)
	}
	// Rule 1 does not fire across a W copy read as X.
	out, n = cleanupText(t, "  mov w10, w1\n  add x0, x10, #1\n  ret")
	if n != 0 {
		t.Fatalf("a W copy read at X width must stay (%d removed):\n%s", n, out)
	}
	// Rule 2: a definition copied once writes its destination.
	out, n = cleanupText(t, "  movz w10, #1\n  mov w9, w10\n  add w0, w9, w1\n  ret")
	if n != 1 || !strings.Contains(out, "movz w9, #1") || strings.Contains(out, "mov w9, w10") {
		t.Fatalf("the constant must land in its destination (%d removed):\n%s", n, out)
	}
	// Rule 2 does not fire when the source is read afterwards; rule 1
	// forwards the copy into its one reader instead.
	out, n = cleanupText(t, "  movz w10, #1\n  mov w9, w10\n  add w0, w9, w10\n  ret")
	if n != 1 || !strings.Contains(out, "movz w10, #1") || !strings.Contains(out, "add w0, w10, w10") {
		t.Fatalf("the definition must stay and its copy forward into the add (%d removed):\n%s", n, out)
	}
	// Rule 3: a branch to the next label.
	out, n = cleanupText(t, "  cbz w0, else\n  movz w9, #1\n  b endif\nelse:\n  movz w9, #2\n  b endif\nendif:\n  mov w0, w9\n  ret")
	if n != 1 || strings.Count(out, "b endif") != 1 {
		t.Fatalf("the branch to the following label must go (%d removed):\n%s", n, out)
	}
	// A copy live across a join stays: both arms write the scratch, the
	// join reads it.
	out, n = cleanupText(t, "  cbz w0, else\n  mov w9, w1\n  b endif\nelse:\n  mov w9, w0\nendif:\n  mov w0, w9\n  ret")
	if strings.Contains(out, "mov w0, w1") {
		t.Fatalf("a copy read after a join must not be forwarded:\n%s", out)
	}
	// A call reads its argument registers implicitly: the copy stays.
	out, n = cleanupText(t, "  mov w0, w1\n  bl g\n  ret")
	if n != 0 {
		t.Fatalf("an argument copy before a call must stay (%d removed):\n%s", n, out)
	}
}

func TestCleanupZeroIndexStore(t *testing.T) {
	out, n := cleanupText(t, "  mov x9, x2\n  mov w10, wzr\n  str x9, [x0, w10, uxtw #3]\n  ret")
	if n != 2 || !strings.Contains(out, "str x2, [x0]") ||
		strings.Contains(out, "mov x9") || strings.Contains(out, "mov w10") {
		t.Fatalf("zero-index store must consume both temporaries (%d removed):\n%s", n, out)
	}
	out, n = cleanupText(t, "  mov x9, xzr\n  mov w10, wzr\n  str x9, [x0, w10, uxtw #3]\n  ret")
	if n != 2 || !strings.Contains(out, "str xzr, [x0]") {
		t.Fatalf("zero data/index store must use XZR directly (%d removed):\n%s", n, out)
	}
	out, n = cleanupText(t, "  mov w9, w1\n  mov w10, wzr\n  str w9, [x0, w10, uxtw #2]\n  ret")
	if n != 2 || !strings.Contains(out, "str w1, [x0]") {
		t.Fatalf("32-bit zero-index store must use the matching scale (%d removed):\n%s", n, out)
	}

	dataMove := asm.Instruction{Mnemonic: "mov", Operands: []asm.Operand{
		asm.Register{Class: asm.ClassX, Num: 9}, asm.Register{Class: asm.ClassX, Num: 2},
	}}
	indexMove := asm.Instruction{Mnemonic: "mov", Operands: []asm.Operand{
		asm.Register{Class: asm.ClassW, Num: 10}, asm.Register{Class: asm.ClassW, Num: 31},
	}}
	index := asm.Register{Class: asm.ClassW, Num: 10}
	store := asm.Instruction{Mnemonic: "str", Operands: []asm.Operand{
		asm.Register{Class: asm.ClassX, Num: 9}, asm.Memory{
			Base: asm.Register{Class: asm.ClassX, Num: 0}, Index: &index,
			Mode: asm.MemOffset, Extend: "uxtw", Shift: 3,
		},
	}, CheckedFacts: []asm.CheckedFactRef{{ID: "stale", Operand: 1}}}
	folded, _, _, ok := foldZeroIndexStore(dataMove, indexMove, store)
	if !ok || folded.CheckedFacts != nil {
		t.Fatalf("direct store must fold while dropping stale indexed facts: %#v", folded.CheckedFacts)
	}

	for name, mutate := range map[string]func(*asm.Instruction, *asm.Instruction, *asm.Instruction){
		"decorated data move":  func(d, _, _ *asm.Instruction) { d.Cond = "eq" },
		"decorated index move": func(_, i, _ *asm.Instruction) { i.Cond = "eq" },
		"decorated store":      func(_, _, s *asm.Instruction) { s.Cond = "eq" },
		"nonzero offset": func(_, _, s *asm.Instruction) {
			m := s.Operands[1].(asm.Memory)
			m.Offset = 8
			s.Operands[1] = m
		},
		"pre-index mode": func(_, _, s *asm.Instruction) {
			m := s.Operands[1].(asm.Memory)
			m.Mode = asm.MemPreIndex
			s.Operands[1] = m
		},
		"mul-vl address": func(_, _, s *asm.Instruction) {
			m := s.Operands[1].(asm.Memory)
			m.MulVL = true
			s.Operands[1] = m
		},
	} {
		t.Run(name, func(t *testing.T) {
			d, i, s := dataMove, indexMove, store
			d.Operands = append([]asm.Operand(nil), dataMove.Operands...)
			i.Operands = append([]asm.Operand(nil), indexMove.Operands...)
			s.Operands = append([]asm.Operand(nil), store.Operands...)
			mutate(&d, &i, &s)
			if _, _, _, ok := foldZeroIndexStore(d, i, s); ok {
				t.Fatal("addressing near miss unexpectedly folded")
			}
		})
	}

	for name, body := range map[string]string{
		"wrong scale":   "  mov x9, x2\n  mov w10, wzr\n  str x9, [x0, w10, uxtw #2]",
		"wrong extend":  "  mov x9, x2\n  mov x10, xzr\n  str x9, [x0, x10, lsl #3]",
		"live data":     "  mov x9, x2\n  mov w10, wzr\n  str x9, [x0, w10, uxtw #3]\n  add x0, x9, #1",
		"live index":    "  mov x9, x2\n  mov w10, wzr\n  str x9, [x0, w10, uxtw #3]\n  add w0, w10, #1",
		"data is base":  "  mov x0, x2\n  mov w10, wzr\n  str x0, [x0, w10, uxtw #3]",
		"index is data": "  mov x10, x2\n  mov w10, wzr\n  str x10, [x0, w10, uxtw #3]",
	} {
		t.Run(name, func(t *testing.T) {
			out, _ := cleanupText(t, body+"\n  ret")
			if strings.Contains(out, "str x2, [x0]") {
				t.Fatalf("near miss unexpectedly became the direct source store:\n%s", out)
			}
		})
	}
}

// Rule 6: a Bool materialized only to be branched on becomes the branch
// on the flags; one read again, or one tested after another instruction,
// stays.
func TestCleanupFusesFlagBranches(t *testing.T) {
	out, n := cleanupText(t, "  cmp w2, w1\n  cset w5, hs\n  cbz w5, skip\n  add x0, x0, #1\nskip:\n  cmp w2, #1\n  cset w5, eq\n  cbnz w5, done\n  add x0, x0, #2\ndone:\n  ret")
	if n != 2 || !strings.Contains(out, "b.lo skip") || !strings.Contains(out, "b.eq done") || strings.Contains(out, "cset") {
		t.Fatalf("cset+cbz is b.!cond and cset+cbnz is b.cond (%d removed):\n%s", n, out)
	}
	out, n = cleanupText(t, "  cmp w2, w1\n  cset w5, hs\n  cbz w5, skip\n  add w0, w5, #1\nskip:\n  ret")
	if n != 0 || !strings.Contains(out, "cset w5, hs") {
		t.Fatalf("a Bool read after the branch keeps its cset (%d removed):\n%s", n, out)
	}
	out, n = cleanupText(t, "  cmp w2, w1\n  cset w5, hs\n  add w0, w0, #1\n  cbz w5, skip\nskip:\n  ret")
	if n != 0 {
		t.Fatalf("an instruction between the cset and the branch refuses the fusion (%d removed):\n%s", n, out)
	}
}

// Rule 3 through a run of labels, rule 7 (a masked bit compared and
// branched on is a test-bit branch), and rule 8 (a zero moved only to be
// stored is the zero register stored), each with its refusal.
func TestCleanupLabelRunsBitTestsAndZeroStores(t *testing.T) {
	out, n := cleanupText(t, "  cmp w2, w1\n  b.lo else_4\n  mov w4, wzr\n  b endif_5\nelse_4:\nendif_5:\n  mov w0, w4\n  ret")
	if n != 1 || strings.Contains(out, "b endif_5") {
		t.Fatalf("a branch to a label reached through a run of labels falls through (%d removed):\n%s", n, out)
	}
	out, n = cleanupText(t, "  and x9, x7, #1\n  cmp x9, #0\n  b.ne else_8\n  mov w4, wzr\nelse_8:\n  mov w0, w4\n  ret")
	if n != 2 || !strings.Contains(out, "tbnz w7, #0, else_8") || strings.Contains(out, "cmp x9") {
		t.Fatalf("a masked bit compared and branched on is tbnz (%d removed):\n%s", n, out)
	}
	out, n = cleanupText(t, "  and x9, x7, #4\n  cmp x9, #0\n  b.eq skip\n  mov w4, wzr\nskip:\n  mov w0, w4\n  ret")
	if n != 2 || !strings.Contains(out, "tbz w7, #2, skip") {
		t.Fatalf("b.eq on the masked bit is tbz (%d removed):\n%s", n, out)
	}
	out, n = cleanupText(t, "  and x9, x7, #1\n  cmp x9, #0\n  b.ne else_8\n  mov x0, x9\n  ret\nelse_8:\n  mov w0, w4\n  ret")
	if n != 0 {
		t.Fatalf("a masked value read after the branch keeps its compare (%d removed):\n%s", n, out)
	}
	out, n = cleanupText(t, "  and x9, x7, #1\n  cmp x9, #0\n  b.ne else_8\n  mov w4, wzr\n  ret\nelse_8:\n  b.eq done\n  mov w0, w4\ndone:\n  ret")
	if strings.Contains(out, "tbnz") {
		t.Fatalf("a target block that reads the flags refuses the fusion:\n%s", out)
	}
	out, n = cleanupText(t, "  mov x9, xzr\n  str x9, [x14]\n  ret")
	if n != 0 {
		t.Fatalf("the early cleanup leaves zero stores to the post-schedule pass (%d removed):\n%s", n, out)
	}
	out, n = postScheduleCleanupText(t, "  mov x9, xzr\n  str x9, [x14]\n  ret")
	if n != 1 || !strings.Contains(out, "str xzr, [x14]") {
		t.Fatalf("a zero moved only to be stored is the zero register stored (%d removed):\n%s", n, out)
	}
	out, n = postScheduleCleanupText(t, "  mov x9, xzr\n  add x14, x14, #8\n  str x9, [x14]\n  ret")
	if n != 1 || !strings.Contains(out, "str xzr, [x14]") || !strings.Contains(out, "add x14, x14, #8") {
		t.Fatalf("an independent scheduled instruction between the move and the store is kept (%d removed):\n%s", n, out)
	}
	out, n = postScheduleCleanupText(t, "  mov x9, xzr\n  str x9, [x14]\n  add x0, x9, #1\n  ret")
	if strings.Contains(out, "str xzr") {
		t.Fatalf("a zero read after the store keeps its register:\n%s", out)
	}
}

// Rule 9: a Bool materialized only to be selected on selects on the
// cset's condition; a read of the Bool after the select, or a flag-setting
// instruction between, keeps the shape.
func TestCleanupFusesFlagSelects(t *testing.T) {
	out, n := cleanupText(t, "  cmp x0, #0\n  cset w3, eq\n  movz w9, #3\n  cmp w3, #0\n  csel w0, w9, w2, ne\n  ret")
	if n != 2 || !strings.Contains(out, "csel w0, w9, w2, eq") || strings.Contains(out, "cset") {
		t.Fatalf("the select reads the compare's flags (%d removed):\n%s", n, out)
	}
	out, n = cleanupText(t, "  cmp x0, #0\n  cset w3, lo\n  cmp w3, #0\n  csel w0, w9, w2, eq\n  ret")
	if n != 2 || !strings.Contains(out, "csel w0, w9, w2, hs") {
		t.Fatalf("eq after the compare is the inverted condition (%d removed):\n%s", n, out)
	}
	out, n = cleanupText(t, "  cmp x0, #0\n  cset w3, eq\n  cmp w3, #0\n  csel w0, w9, w2, ne\n  add w0, w0, w3\n  ret")
	if strings.Contains(out, "csel w0, w9, w2, eq") {
		t.Fatalf("a Bool read after the select keeps its cset:\n%s", out)
	}
	out, n = cleanupText(t, "  cmp x0, #0\n  cset w3, eq\n  add w9, w9, #1\n  cmp w3, #0\n  csel w0, w9, w2, ne\n  ret")
	if strings.Contains(out, "csel w0, w9, w2, eq") {
		t.Fatalf("an arithmetic instruction between refuses the fusion:\n%s", out)
	}
}
