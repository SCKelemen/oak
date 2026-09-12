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

// A refined return type is a postcondition: the callee constructs, and the
// caller's index through the call is proven without a binding.
func TestE2ERefinementReturn(t *testing.T) {
	src := `
Slot: type = u16 where value < u16(8)
TABLE: [8]u8 = [8]u8{ 1, 2, 3, 4, 5, 6, 7, 8 }

low: (x: u16): Slot = Slot(x & u16(7))

main: (): i32 = i32_bits_u32(u32(TABLE[low(u16(13))]) + u32(TABLE[low(u16(2))]))
`
	output, err := New().WithSource("refret.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if strings.Contains(output, "oak_index( ") || strings.Count(output, "oak_refine_oak_Slot( ")-1 != 0 {
		t.Fatalf("expected proven accesses and a discharged construction:\n%s", output)
	}
	// TABLE[5] + TABLE[2] = 6 + 3
	code, abnormal := buildAndRun(t, "refret", src)
	if abnormal || code != 9 {
		t.Fatalf("exit = (%d, abnormal=%v), want 9", code, abnormal)
	}
	bad := "Slot: type = u16 where value < u16(8)\nlow: (x: u16): Slot = x & u16(7)\nmain: (): i32 = 0\n"
	if _, err := New().WithSource("refretbad.oak", bad).Check().Get(); err == nil {
		t.Fatalf("a base value must not be returned as the refinement without construction")
	}
}

// Generic refinements (docs/spec/20-types.md section 12.1): a refinement
// over integer constants is specialized per application before checking.
// `IrqId[4]` and `IrqId[8]` are distinct nominal types with their own
// guards; a parameter of either carries the substituted predicate as a
// fact, and a construction under a proving guard is discharged.
func TestE2ERefinementTemplates(t *testing.T) {
	src := `
IrqId[N: u32]: type = u16 where value < N

Table: type = struct { rows: [4]u8, wide: [8]u8 }

pick: (t: Table, i: IrqId[4]): u8 = t.rows[i]

pick_wide: (t: Table, i: IrqId[8]): u8 = t.wide[i]

sum_rows: (t: Table): u32 {
  total: u32 = 0
  k: u16 = 0
  while k < u16(4) {
    total = total + u32(t.rows[IrqId[4](k)])
    k = k + u16(1)
  }
  total
}

main: (): i32 {
  t: Table
  t.rows = [4]u8{ 1, 2, 3, 4 }
  t.wide = [8]u8{ 0, 0, 0, 0, 0, 0, 0, 30 }
  n: u16 = 7
  last: IrqId[8] = IrqId[8](n)
  i: IrqId[4] = IrqId[4](u16(2))
  base: u16 = i
  i32_bits_u32(sum_rows(t) + u32(pick(t, i)) + u32(pick_wide(t, last)) + u32(base) - u32(1))
}
`
	output, err := New().WithSource("refinetpl.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, want := range []string{"typedef u16 oak_IrqId_4;", "typedef u16 oak_IrqId_8;", "oak_refine_oak_IrqId_8( n )"} {
		if !strings.Contains(output, want) {
			t.Fatalf("missing %q:\n%s", want, output)
		}
	}
	// The literal construction and the loop-guarded one are discharged: the
	// only guard left is the one over the arbitrary n.
	if got := strings.Count(output, "oak_refine_oak_IrqId_"); got != 3 {
		t.Fatalf("expected two guard definitions and one guarded construction, found %d:\n%s", got, output)
	}
	if strings.Contains(output, "oak_index( ") {
		t.Fatalf("refined indices should be proven:\n%s", output)
	}
	// 10 + 3 + 30 + 2 - 1 = 44
	code, abnormal := buildAndRun(t, "refinetpl", src)
	if abnormal || code != 44 {
		t.Fatalf("exit = (%d, abnormal=%v), want 44", code, abnormal)
	}

	// Instantiations are distinct types; arguments are checked against the
	// parameter's kind; a type parameter is not a const parameter.
	for _, bad := range []struct{ name, src, want string }{
		{"mixed", "IrqId[N: u32]: type = u16 where value < N\nf: (i: IrqId[4]): u16 = i\nmain: (): i32 { x: IrqId[8] = IrqId[8](u16(1))\n i32(f(x)) }", "IrqId_4"},
		{"range", "IrqId[N: u8]: type = u16 where value < N\nmain: (): i32 { x: IrqId[300] = IrqId[300](u16(1))\n i32(x) }", "literal 300 does not fit in type u8"},
		{"arity", "IrqId[N: u32]: type = u16 where value < N\nmain: (): i32 { x: IrqId[1, 2] = IrqId[1, 2](u16(0))\n i32(x) }", "takes 1 constant argument(s), got 2"},
		{"kind", "Boxed[T]: type = u16 where value < u16(4)\nmain: (): i32 = 0", "integer constants (N: u32), not types"},
	} {
		_, err := New().WithSource(bad.name+".oak", bad.src).EmitC().Get()
		if err == nil || !strings.Contains(err.Error(), bad.want) {
			t.Fatalf("%s: expected an error mentioning %q, got %v", bad.name, bad.want, err)
		}
	}
}

// Discharge beyond a literal bound (docs/spec/20-types.md section 12,
// typechecker/discharge.go): a constant argument is evaluated, a lower
// bound comes from the facts, a power-of-two divisibility from the shape
// of the argument, a conjunction from its parts, and an argument already
// of the same refinement needs no second guard.
func TestE2ERefinementDischargeShapes(t *testing.T) {
	src := `
Page: type = u32 where value % u32(4096) == u32(0)
Slot: type = u16 where value >= u16(1) && value < u16(8)
Even: type = u8 where value % u8(2) == u8(0)
TABLE: [8]u8 = [8]u8{ 0, 1, 2, 3, 4, 5, 6, 7 }

frame: (p: u32): Page = Page(p << u32(12))
aligned: (a: u32): Page = Page(a & u32(4294963200))
raw: (n: u32): Page = Page(n)

sum_slots: (): u32 {
  total: u32 = 0
  k: u16 = 1
  while k >= u16(1) && k < u16(8) {
    total = total + u32(TABLE[Slot(k)])
    k = k + u16(1)
  }
  total + u32(TABLE[Slot(u16(7))])
}

twice: (x: u8): Even = Even(x * u8(2))
recheck: (e: Even): Even = Even(e)

main: (): i32 {
  a: Page = frame(u32(2))
  b: Page = aligned(u32(8191))
  c: Page = raw(u32(4096))
  i32_bits_u32(u32(a) / u32(4096) + u32(b) / u32(4096) + u32(c) / u32(4096) + sum_slots() + u32(twice(u8(3))) + u32(recheck(Even(u8(4)))))
}
`
	output, err := New().WithSource("shapes.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	// Each count includes the guard's definition: only raw's construction
	// keeps a guard.
	for name, want := range map[string]int{"Page": 2, "Slot": 1, "Even": 1} {
		if got := strings.Count(output, "oak_refine_oak_"+name+"( "); got != want {
			t.Fatalf("%s: expected %d guard occurrences, found %d:\n%s", name, want, got, output)
		}
	}
	if strings.Contains(output, "oak_index( ") {
		t.Fatalf("the slot indices should be proven through the conjunction's bound:\n%s", output)
	}
	// 2 + 1 + 1 + (28 + 7) + 6 + 4 = 49
	code, abnormal := buildAndRun(t, "shapes", src)
	if abnormal || code != 49 {
		t.Fatalf("exit = (%d, abnormal=%v), want 49", code, abnormal)
	}
}
