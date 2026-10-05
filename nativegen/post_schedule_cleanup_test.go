package nativegen

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/opt"
)

func TestPostScheduleCleanupForwardsFinalCopy(t *testing.T) {
	fn := &asm.Function{Arch: asm.ArchArm64, Items: []asm.Item{
		ins("strb", wr(0), asm.Memory{Base: xr(15)}),
		ins("mov", wr(2), wr(0)),
		ins("cmp", wr(2), asm.Immediate{Value: 0}),
		ins("cset", wr(2), asm.Condition{Code: "eq"}),
		ins("ret"),
	}}
	if n := postScheduleCleanup(fn); n != 1 {
		t.Fatalf("removed %d instructions, want one:\n%s", n, Describe(fn))
	}
	text := Describe(fn)
	if strings.Contains(text, "mov w2, w0") || !strings.Contains(text, "cmp w0, #0") {
		t.Fatalf("final copy was not forwarded into its compare:\n%s", text)
	}
	if n := postScheduleCleanup(fn); n != 0 {
		t.Fatalf("pass is not idempotent: removed %d again", n)
	}
}

func TestPostScheduleCleanupRemovesAliasLabelBranch(t *testing.T) {
	unit, errs := asm.ParseUnit("post.oakasm", "f: () -> u32 = {\n  clobber w9\n  b target\nalias:\ntarget:\n  mov w0, w9\n  ret\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	fn := unit.Functions[0]
	if removed := postScheduleAliasLabelCleanup(fn); removed != 1 || strings.Contains(Describe(fn), "b target") {
		t.Fatalf("alias-label branch cleanup removed %d:\n%s", removed, Describe(fn))
	}

	unit, errs = asm.ParseUnit("post.oakasm", "f: () -> u32 = {\n  clobber w9\n  b target\nmiddle:\n  b target\ntarget:\n  mov w0, w9\n  ret\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	fn = unit.Functions[0]
	if removed := postScheduleAliasLabelCleanup(fn); removed != 2 || strings.Contains(Describe(fn), "b target") {
		t.Fatalf("alias-label cleanup must close a newly adjacent branch (%d removed):\n%s", removed, Describe(fn))
	}

	unit, errs = asm.ParseUnit("post.oakasm", "f: () -> u32 = {\n  clobber w9\n  b target\nalias:\n  align 8\ntarget:\n  mov w0, w9\n  ret\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	fn = unit.Functions[0]
	if removed := postScheduleAliasLabelCleanup(fn); removed != 0 || !strings.Contains(Describe(fn), "b target") {
		t.Fatalf("alignment must end the alias-label run (%d removed):\n%s", removed, Describe(fn))
	}
}

func TestPostScheduleCleanupCandidateRequiresParent(t *testing.T) {
	transform, found := Registry().Lookup(TransformPostScheduleCleanup)
	if !found {
		t.Fatal("missing post-schedule cleanup candidate")
	}
	if gated, ok := transform.(opt.Gated); !ok || !gated.NeedsVerdict() {
		t.Fatal("post-schedule cleanup must require a semantic verdict")
	}
	plain := opt.Identity(PlainLane(Lane{Arch: asm.ArchArm64}))
	if transform.Apply(plain) != nil {
		t.Fatal("post-schedule cleanup must wait for ordinary cleanup")
	}
	parentLane := plain.Config.(Lane)
	parentLane.Cleanup = true
	parentLane.UnrollFills = true
	if transform.Apply(opt.Identity(parentLane)) != nil {
		t.Fatal("post-schedule cleanup must preserve the fill validation fallback")
	}
	parentLane.UnrollFills = false
	next := transform.Apply(opt.Identity(parentLane))
	if next == nil || !next.Config.(Lane).PostScheduleCleanup ||
		PlainLane(Lane{PostScheduleCleanup: true}).PostScheduleCleanup {
		t.Fatal("post-schedule cleanup toggle or identity fallback")
	}
}

func TestPostScheduleCleanupFollowsOrdinaryCleanup(t *testing.T) {
	cleanup, post := -1, -1
	for i, transform := range Transforms() {
		switch transform.Name() {
		case TransformCleanup:
			cleanup = i
		case TransformPostScheduleCleanup:
			post = i
		}
	}
	if cleanup < 0 || post < 0 || cleanup >= post {
		t.Fatalf("transform order cleanup=%d post-schedule=%d", cleanup, post)
	}
}
