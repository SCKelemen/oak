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

func TestPostScheduleCleanupCandidateRequiresParents(t *testing.T) {
	transform, found := Registry().Lookup(TransformPostScheduleCleanup)
	if !found {
		t.Fatal("missing post-schedule cleanup candidate")
	}
	if gated, ok := transform.(opt.Gated); !ok || !gated.NeedsVerdict() {
		t.Fatal("post-schedule cleanup must require a semantic verdict")
	}
	plain := opt.Identity(PlainLane(Lane{Arch: asm.ArchArm64}))
	if transform.Apply(plain) != nil {
		t.Fatal("post-schedule cleanup must wait for its parents")
	}
	parentLane := plain.Config.(Lane)
	parentLane.Schedule = true
	if transform.Apply(opt.Identity(parentLane)) != nil {
		t.Fatal("post-schedule cleanup applied without normalized forwarding")
	}
	parentLane.Schedule = false
	parentLane.ElideGlobalLoadMasks = true
	if transform.Apply(opt.Identity(parentLane)) != nil {
		t.Fatal("post-schedule cleanup applied without scheduling")
	}
	parentLane.Schedule = true
	next := transform.Apply(opt.Identity(parentLane))
	if next == nil || !next.Config.(Lane).PostScheduleCleanup ||
		PlainLane(Lane{PostScheduleCleanup: true}).PostScheduleCleanup {
		t.Fatal("post-schedule cleanup toggle or identity fallback")
	}
}
