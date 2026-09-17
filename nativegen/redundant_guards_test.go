package nativegen

import (
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/opt"
)

const redundantGuardAssembly = `
  cmp w19, w20
  b.hs trap
  cbz w2, other
  add w3, w3, #1
  b join
other:
  sub w3, w3, #1
join:
  cmp w19, w20
  b.hs trap
  movz w4, #7
  cmp w3, #0
  cset w0, eq
  ret
trap:
  brk #1`

func redundantGuardItems(t *testing.T, body string) *asm.Function {
	t.Helper()
	unit, errs := asm.ParseUnit("guards.oakasm", "f: (a, b, c: u32): u32 = {\n  bind w19 = a\n  bind w20 = b\n  bind w2 = c\n  clobber w0, w3, w4\n"+body+"\n}\n")
	if len(errs) > 0 {
		t.Fatal(errs)
	}
	return unit.Functions[0]
}

func TestElideRedundantGuards(t *testing.T) {
	fn := redundantGuardItems(t, redundantGuardAssembly)
	before := Describe(fn)
	out, n := elideRedundantGuards(fn.Items)
	if Describe(fn) != before {
		t.Fatal("candidate mutated its parent's items")
	}
	fn.Items = out
	text := Describe(fn)
	if n != 1 || strings.Count(text, "cmp w19, w20") != 1 || strings.Count(text, "b.hs trap") != 1 ||
		!strings.Contains(text, "join:\n  movz w4, #7") {
		t.Fatalf("redundant guard result (%d):\n%s", n, text)
	}
	if twice, n := elideRedundantGuards(out); n != 0 || !reflect.DeepEqual(twice, out) {
		t.Fatal("pass must be idempotent")
	}
	three := strings.Replace(redundantGuardAssembly, "  movz w4, #7", "  cmp w19, w20\n  b.hs trap\n  movz w4, #7", 1)
	if _, n := elideRedundantGuards(redundantGuardItems(t, three).Items); n != 2 {
		t.Fatalf("three guards removed %d pairs, want two", n)
	}
	transform, found := Registry().Lookup(TransformRedundantGuards)
	if !found {
		t.Fatal("missing redundant-guard candidate")
	}
	if gated, ok := transform.(opt.Gated); !ok || !gated.NeedsVerdict() {
		t.Fatal("redundant guards must require a semantic verdict")
	}
	if !transform.Apply(opt.Identity(PlainLane(Lane{Arch: asm.ArchArm64}))).Config.(Lane).ElideRedundantGuards ||
		PlainLane(Lane{ElideRedundantGuards: true}).ElideRedundantGuards {
		t.Fatal("candidate toggle or identity fallback")
	}
}

func TestElideRedundantGuardsRefusals(t *testing.T) {
	for name, body := range map[string]string{
		"first does not dominate": strings.Replace(redundantGuardAssembly,
			"  cmp w19, w20", "  cbz w2, join\n  cmp w19, w20", 1),
		"left changes": strings.Replace(redundantGuardAssembly,
			"  add w3, w3, #1", "  add w19, w19, #1", 1),
		"right changes": strings.Replace(redundantGuardAssembly,
			"  sub w3, w3, #1", "  sub w20, w20, #1", 1),
		"call between": strings.Replace(redundantGuardAssembly,
			"  add w3, w3, #1", "  bl helper", 1),
		"flags consumed": strings.Replace(redundantGuardAssembly,
			"  movz w4, #7\n  cmp w3, #0", "  cset w4, lo\n  cmp w3, #0", 1),
		"different condition": strings.Replace(redundantGuardAssembly,
			"  b.hs trap\n  movz w4", "  b.ge trap\n  movz w4", 1),
		"different target": strings.Replace(redundantGuardAssembly,
			"  b.hs trap\n  movz w4", "  b.hs trap2\n  movz w4", 1) + "\ntrap2:\n  brk #1",
		"different left": strings.Replace(redundantGuardAssembly,
			"  cmp w19, w20\n  b.hs trap\n  movz", "  cmp w2, w20\n  b.hs trap\n  movz", 1),
		"nontrap target": strings.Replace(redundantGuardAssembly, "trap:\n  brk #1", "trap:\n  ret", 1),
	} {
		t.Run(name, func(t *testing.T) {
			fn := redundantGuardItems(t, body)
			before := Describe(fn)
			out, n := elideRedundantGuards(fn.Items)
			fn.Items = out
			if n != 0 || Describe(fn) != before {
				t.Fatalf("unsafe shape changed (%d):\n%s", n, Describe(fn))
			}
		})
	}
}
