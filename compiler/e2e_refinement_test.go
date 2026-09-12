package compiler

import (
	"strings"
	"testing"
)

// Refinement types (docs/spec/20-types.md section 12): a nominal base type
// with a predicate over `value`. A parameter of the refined type carries the
// predicate as an extent fact, so the table access below is proven; the
// construction is the base value through the guard; a refined value flows
// to its base freely.
func TestE2ERefinementTypes(t *testing.T) {
	src := `
Slot: type = u16 where value < u16(8)

TABLE: [8]u8 = [8]u8{ 7, 7, 7, 7, 7, 7, 7, 7 }

lookup: (i: Slot): u8 = TABLE[i]

widen: (i: Slot): u32 = u32(i) + u32(1)

main: (): i32 {
  first: Slot = Slot(u16(3))
  n: u16 = first
  computed: u16 = n * u16(2)
  last: Slot = Slot(computed)
  i32_bits_u32(u32(lookup(first)) + u32(lookup(last)) + widen(last) + u32(n))
}
`
	output, err := New().WithSource("refine.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if !strings.Contains(output, "typedef u16 oak_Slot;") || !strings.Contains(output, "oak_refine_oak_Slot(") {
		t.Fatalf("refinement not emitted:\n%s", output)
	}
	if strings.Contains(output, "oak_index( ") {
		t.Fatalf("the refined index should be proven:\n%s", output)
	}
	// 7 + 7 + 7 + 3 = 24
	code, abnormal := buildAndRun(t, "refine", src)
	if abnormal || code != 24 {
		t.Fatalf("exit = (%d, abnormal=%v), want 24", code, abnormal)
	}
}

// The guard traps on a value outside the predicate, and the checker refuses
// a base value where the refinement is expected.
func TestE2ERefinementGuardAndShape(t *testing.T) {
	trap := `
Slot: type = u16 where value < u16(8)
main: (): i32 {
  n: u16 = 300
  s: Slot = Slot(n)
  i32_bits_u32(u32(s))
}
`
	code, abnormal := buildAndRun(t, "refinetrap", trap)
	if !abnormal && code == 44 {
		t.Fatalf("the guard did not trap: exit = (%d, abnormal=%v)", code, abnormal)
	}
	for _, tc := range []struct{ name, src, want string }{
		{"base to refined", "Slot: type = u16 where value < u16(8)\nf: (i: Slot): u16 = i\nmain: (): i32 { n: u16 = 3\n i32_bits_u32(u32(f(n))) }\n", "Slot"},
		{"non-Bool predicate", "Slot: type = u16 where value + u16(1)\nmain: (): i32 = 0\n", "OAK-T0602"},
		{"non-integer base", "Odd: type = Bool where value\nmain: (): i32 = 0\n", "OAK-T0602"},
	} {
		_, err := New().WithSource("shape.oak", tc.src).Check().Get()
		if err == nil || !strings.Contains(err.Error(), tc.want) {
			t.Errorf("%s: err = %v, want %q", tc.name, err, tc.want)
		}
	}
}

// A construction whose argument the facts in scope prove below the bound
// emits no guard: a masked value, a literal, a loop counter under its
// bound; an unproven one keeps it.
func TestE2ERefinementDischarge(t *testing.T) {
	src := `
Slot: type = u16 where value < u16(8)
TABLE: [8]u8 = [8]u8{ 1, 2, 3, 4, 5, 6, 7, 8 }

sum: (x: u16, n: u16): u32 {
  total: u32 = 0
  i: u16 = 0
  while i < u16(8) {
    total = total + u32(TABLE[Slot(i)])
    i = i + u16(1)
  }
  total + u32(TABLE[Slot(x & u16(7))]) + u32(TABLE[Slot(u16(2))]) + u32(TABLE[Slot(n)])
}

main: (): i32 = i32_bits_u32(sum(u16(9), u16(1)) - u32(36))
`
	output, err := New().WithSource("discharge.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if got := strings.Count(output, "oak_refine_oak_Slot( ") - 1; got != 1 {
		t.Fatalf("expected one guarded construction (the unproven n) besides the definition, found %d:\n%s", got, output)
	}
	if strings.Contains(output, "oak_index( ") {
		t.Fatalf("every table access should be proven:\n%s", output)
	}
	// 36 + 2 + 3 + 2 - 36 = 7
	code, abnormal := buildAndRun(t, "discharge", src)
	if abnormal || code != 7 {
		t.Fatalf("exit = (%d, abnormal=%v), want 7", code, abnormal)
	}
}
