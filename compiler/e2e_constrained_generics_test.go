package compiler

import (
	"strings"
	"testing"
)

// Constrained generics monomorphize (docs/spec/20-types.md §11.2): the body
// is checked once against its contract (a field outside the constraint is
// a declaration-time error), every call site checks its argument against
// the constraint (OAK-T0104), and each satisfied call specializes the body
// for emission — one path for constrained and unconstrained templates.
func TestE2EConstrainedGenericsExecute(t *testing.T) {
	src := `
Position: type = { x: i32, y: i32 }
Tagged: type = { tag: u32 }

Point: type = struct {
  x: i32
  y: i32
}

Sprite: type = struct {
  tag: u32
  y: i32
  x: i32
  z: i32
}

fn [T: Position] sum_xy(p: T) -> i32 { p.x + p.y }
fn [T: Position & Tagged] tagged_sum(p: T) -> i32 { p.x + p.y + i32_bits_u32(p.tag) }

main: (): i32 {
  pt: Point = Point { x: 40, y: 2 }
  sp: Sprite = Sprite { tag: u32(1), y: 20, x: 21, z: 99 }
  assert(sum_xy(pt) == 42)
  assert(sum_xy(sp) == 41)
  assert(tagged_sum(sp) == 42)
  42
}
`
	output, err := New().WithSource("constrained.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, want := range []string{"oak_sum_xy_Point", "oak_sum_xy_Sprite", "oak_tagged_sum_Sprite"} {
		if !strings.Contains(output, want) {
			t.Fatalf("emitted C lacks specialization %q:\n%s", want, output)
		}
	}
	code, abnormal := buildAndRun(t, "constrained", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// The contract is the contract: a body reading outside its constraint is a
// declaration-time error even if every caller happens to satisfy it, and a
// call whose argument lacks a required field is rejected with the
// structured constraint diagnostic — neither ever reaches emission.
func TestConstrainedGenericsRejections(t *testing.T) {
	_, err := New().WithSource("outside.oak", `
Position: type = { x: i32, y: i32 }
Point3: type = struct { x: i32, y: i32, z: i32 }
fn [T: Position] read_z(p: T) -> i32 { p.z }
main: (): i32 {
  q: Point3 = Point3 { x: 1, y: 2, z: 3 }
  read_z(q)
}
`).EmitC().Get()
	if err == nil {
		t.Fatal("a body reading outside its constraint must be rejected at the declaration")
	}

	_, err = New().WithSource("unsat.oak", `
Position: type = { x: i32, y: i32 }
Flat: type = struct { x: i32 }
fn [T: Position] sum_xy(p: T) -> i32 { p.x + p.y }
main: (): i32 {
  f: Flat = Flat { x: 1 }
  sum_xy(f)
}
`).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "OAK-T0104") {
		t.Fatalf("unsatisfied constraint must fail with OAK-T0104, got %v", err)
	}
}
