package prove

import (
	"strings"
	"testing"
)

// Bounded quantifiers inside theorems (docs/spec/10-syntax.md section 3e,
// docs/spec/125-verification.md section 2): the exhaustive rung
// enumerates them through the interpreter, the bit-level rung eliminates
// the binder on the diagram, and a refuted claim names the theorem's
// parameters only.
func TestTheoremsWithQuantifiers(t *testing.T) {
	src := `
Color: type = Red | Green | Blue

some_blue: theorem (b: Bool) { b || exists (c: Color) { c == .Blue } }

all_commute: theorem (y: u8) { forall (x: u8) { x + y == y + x } }

has_half: theorem (y: u8) { exists (x: u8) { x + x == y } }

low_byte: theorem (y: u32) { exists (x: u8) { u32(x) == (y & u32(255)) } }

or_grows: theorem (y: u32) { forall (x: u8) { (y | u32(x)) >= y } }

not_below: theorem (y: u32) { forall (x: u8) { u32(x) < y } }

main: (): i32 = 0
`
	results, err := Theorems(check(t, src), 0)
	if err != nil {
		t.Fatal(err)
	}
	want := map[string]Status{
		"some_blue": Decided, "all_commute": Decided, "has_half": Refuted,
		"low_byte": Decided, "or_grows": Decided, "not_below": Refuted,
	}
	if len(results) != len(want) {
		t.Fatalf("got %d results, want %d: %+v", len(results), len(want), results)
	}
	for _, r := range results {
		if r.Status != want[r.Name] {
			t.Errorf("%s: status %s (%s), want %s", r.Name, r.Status, r.Detail, want[r.Name])
		}
		switch r.Name {
		case "all_commute":
			if r.Detail != "all 256 cases" {
				t.Errorf("all_commute: detail %q", r.Detail)
			}
		case "low_byte", "or_grows":
			if !strings.Contains(r.Detail, "bit level") {
				t.Errorf("%s: detail %q", r.Name, r.Detail)
			}
		case "not_below":
			if strings.Contains(r.Detail, "@q") {
				t.Errorf("not_below: the counterexample names a binder: %q", r.Detail)
			}
		}
	}
}
