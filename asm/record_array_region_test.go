package asm

import (
	"fmt"
	"math"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func recordArrayTestLayout() Composite {
	return Composite{Size: 2072, Fields: []CompositeField{
		{Name: "pages", Offset: 0, Size: 2048, Elem: "u64", Length: 256},
		{Name: "tail", Offset: 2048, Size: 24, Elem: "u64", Length: 3},
	}}
}

func TestRecordArrayFieldSelection(t *testing.T) {
	for _, test := range []struct {
		name   string
		change func(*Composite, *region)
	}{
		{"unknown nominal record", func(_ *Composite, r *region) { r.record = "Decoy" }},
		{"interior array offset", func(_ *Composite, r *region) { r.recordOffset, r.size = 8, 2064 }},
		{"wrong record tail size", func(_ *Composite, r *region) { r.size = 2048 }},
		{"negative record offset", func(_ *Composite, r *region) { r.recordOffset = -8 }},
		{"length product overflow", func(c *Composite, _ *region) { c.Fields[0].Length = math.MaxInt64 }},
		{"length exceeds index width", func(c *Composite, _ *region) { c.Fields[0].Length = 1<<32 + 1 }},
		{"inconsistent size", func(c *Composite, _ *region) { c.Fields[0].Size = 2040 }},
		{"past record end", func(c *Composite, _ *region) { c.Fields[0].Size = math.MaxInt64 }},
		{"not u64", func(c *Composite, _ *region) { c.Fields[0].Elem = "u32" }},
		{"nested array", func(c *Composite, _ *region) { c.Fields[0].ElemType = "Nested" }},
		{"scalar ambiguity", func(c *Composite, _ *region) { c.Fields[0].Scalar = "u64" }},
		{"record ambiguity", func(c *Composite, _ *region) { c.Fields[0].Type = "Nested" }},
		{"variant layout", func(c *Composite, _ *region) { c.Variants = map[string]int64{"pages": 0} }},
		{"duplicate name", func(c *Composite, _ *region) { c.Fields[1].Name = "pages" }},
		{"duplicate start", func(c *Composite, _ *region) { c.Fields[1].Offset = 0 }},
		{"overlapping sibling", func(c *Composite, _ *region) { c.Fields[1].Offset = 2040 }},
		{"negative sibling", func(c *Composite, _ *region) { c.Fields[1].Offset = -8 }},
		{"sibling endpoint overflow", func(c *Composite, _ *region) { c.Fields[1].Offset = math.MaxInt64 }},
	} {
		t.Run(test.name, func(t *testing.T) {
			comp := recordArrayTestLayout()
			extent := region{size: comp.Size, writable: true, record: "Regime"}
			test.change(&comp, &extent)
			if got, ok := recordU64ArrayFieldOf(map[string]Composite{"Regime": comp}, extent); ok {
				t.Fatalf("invalid field selection returned %+v", got)
			}
			if got := narrowRecordArrayRegion(map[string]Composite{"Regime": comp}, extent); got != extent {
				t.Fatalf("unsupported selection changed original region: %+v != %+v", got, extent)
			}
		})
	}
	for _, writable := range []bool{false, true} {
		comp := recordArrayTestLayout()
		extent := region{size: comp.Size, writable: writable, record: "Regime"}
		field, ok := recordU64ArrayFieldOf(map[string]Composite{"Regime": comp}, extent)
		if !ok || field != (recordArrayField{"Regime", "pages", 2072, 0, 2048, 256}) {
			t.Fatalf("selected field = %+v, ok=%v", field, ok)
		}
		narrowed := narrowRecordArrayRegion(map[string]Composite{"Regime": comp}, extent)
		if narrowed.size != 2048 || narrowed.writable != writable || narrowed.record != "" {
			t.Fatalf("field narrowing changed writability or retained record-tail identity: %+v", narrowed)
		}
	}
}

func TestCheckerRecordArrayFieldBounds(t *testing.T) {
	decl := "clear: (s: [*]Regime, dom: u32, j: u32) -> ()"
	for _, test := range []struct {
		name        string
		fieldOffset int64
		bound       int
		materialize bool
		wantOK      bool
	}{
		{"last field element", 0, 256, false, true},
		{"sibling bytes are not array elements", 0, 257, false, false},
		{"materialized last field element", 0, 256, true, true},
		{"materialized sibling overrun", 0, 257, true, false},
		{"nonzero split field offset", 4112, 256, false, true},
		{"nonzero field sibling overrun", 4112, 257, false, false},
	} {
		t.Run(test.name, func(t *testing.T) {
			comp := recordArrayTestLayout()
			comp.Size += test.fieldOffset
			for i := range comp.Fields {
				comp.Fields[i].Offset += test.fieldOffset
			}
			offsetAdd := ""
			if test.fieldOffset != 0 {
				offsetAdd = "  add x10, x10, #1, lsl #12\n  add x10, x10, #16\n"
			}
			store := "  str xzr, [x11, w3, uxtw #3]\n"
			if test.materialize {
				store = "  add x12, x11, w3, uxtw #3\n  str xzr, [x12]\n"
			}
			body := fmt.Sprintf("  bind x0, w1 = s\n  bind w2 = dom\n  bind w3 = j\n  clobber w9, x10, x11, x12\n  cmp w2, w1\n  b.hs done\n  mov w9, #%d\n  umaddl x10, w2, w9, x0\n%s  mov x11, x10\n  cmp w3, #%d\n  b.hs done\n%sdone:\n  ret\n", comp.Size, offsetAdd, test.bound, store)
			unit, errs := ParseUnit("record_array.oakasm", decl+" = {\n"+body+"}\n")
			if len(errs) != 0 {
				t.Fatal(errs)
			}
			sig, err := parseSignature(decl)
			if err != nil {
				t.Fatal(err)
			}
			unit.Functions[0].Composites = map[string]Composite{"Regime": comp}
			findings := Check(unit.Functions[0], sig, nil)
			if (len(findings) == 0) != test.wantOK {
				t.Fatalf("checker findings = %v, wantOK=%v", findings, test.wantOK)
			}
		})
	}
}

func TestRecordArrayQuadDecisionsMatchLean(t *testing.T) {
	lean, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "RecordArrayRegion.lean"))
	if err != nil {
		t.Fatal(err)
	}
	field := recordArrayField{"Regime", "pages", 2072, 0, 2048, 256}
	maxField := recordArrayField{"Regime", "pages", 34359738368, 0, 34359738368, 4294967296}
	renderField := func(f recordArrayField) string {
		return fmt.Sprintf("⟨%q, %q, %s, %s, %s, %s⟩", f.recordName, f.fieldName,
			renderInt(f.recordSize), renderInt(f.offset), renderInt(f.size), renderInt(f.length))
	}
	var lines []string
	for _, test := range []struct {
		name   string
		place  recordPlace
		extent region
		field  recordArrayField
		want   bool
	}{
		{"writable baseline", recordPlace{"Regime", 0}, region{size: 2072, writable: true}, field, true},
		{"readonly baseline", recordPlace{"Regime", 0}, region{size: 2072, writable: false}, field, true},
		{"nonzero aligned offset", recordPlace{"Regime", 24}, region{size: 2048, writable: true}, recordArrayField{"Regime", "pages", 2072, 24, 2048, 256}, true},
		{"mismatched nominal name", recordPlace{"Regime", 0}, region{size: 2072, writable: true}, recordArrayField{"Decoy", "pages", 2072, 0, 2048, 256}, false},
		{"empty field name", recordPlace{"Regime", 0}, region{size: 2072, writable: true}, recordArrayField{"Regime", "", 2072, 0, 2048, 256}, false},
		{"unaligned coherent tail", recordPlace{"Regime", 1}, region{size: 2071, writable: true}, recordArrayField{"Regime", "pages", 2072, 1, 2048, 256}, false},
		{"zero length", recordPlace{"Regime", 0}, region{size: 2072, writable: true}, recordArrayField{"Regime", "pages", 2072, 0, 0, 0}, false},
		{"field over tail", recordPlace{"Regime", 24}, region{size: 2048, writable: true}, recordArrayField{"Regime", "pages", 2072, 24, 2056, 257}, false},
		{"maximum index length", recordPlace{"Regime", 0}, region{size: 34359738368, writable: true}, maxField, true},
		{"length exceeds index width", recordPlace{"Regime", 0}, region{size: 34359738376, writable: true}, recordArrayField{"Regime", "pages", 34359738376, 0, 34359738376, 4294967297}, false},
	} {
		got := recordArrayFieldValid(test.place, test.extent, test.field)
		if got != test.want {
			t.Errorf("%s: recordArrayFieldValid = %v, want %v", test.name, got, test.want)
		}
		lines = append(lines, fmt.Sprintf("example : validField ⟨%q, %s⟩ ⟨%s, %v⟩ %s = %v := by decide",
			test.place.name, renderInt(test.place.offset), renderInt(test.extent.size), test.extent.writable,
			renderField(test.field), test.want))
	}
	for _, test := range []struct {
		name   string
		field  recordArrayField
		bound  idxFact
		stride int64
		want   bool
	}{
		{"last admitted baseline bound", field, idxFact{boundReg: -1, bound: 253}, 8, true},
		{"first overflowing baseline bound", field, idxFact{boundReg: -1, bound: 254}, 8, false},
		{"full baseline length", field, idxFact{boundReg: -1, bound: 256}, 8, false},
		{"zero bound", field, idxFact{boundReg: -1, bound: 0}, 8, false},
		{"register bound", field, idxFact{boundReg: 1, bound: 253}, 8, false},
		{"slack bound", field, idxFact{boundReg: -1, bound: 253, slack: true}, 8, false},
		{"wrong stride", field, idxFact{boundReg: -1, bound: 253}, 4, false},
		{"maximum no-wrap bound", maxField, idxFact{boundReg: -1, bound: 4294967293}, 8, true},
		{"first wrapping bound", maxField, idxFact{boundReg: -1, bound: 4294967294}, 8, false},
	} {
		got := recordArrayQuadAdmits(test.field, test.bound, test.stride)
		if got != test.want {
			t.Errorf("%s: recordArrayQuadAdmits = %v, want %v", test.name, got, test.want)
		}
		lines = append(lines, fmt.Sprintf("example : quadAdmits %s %s %d = %v := by decide",
			renderField(test.field), renderIdx(test.bound), test.stride, test.want))
	}
	var missing []string
	for _, line := range lines {
		if !strings.Contains(string(lean), line) {
			missing = append(missing, line)
		}
	}
	if len(missing) != 0 {
		t.Fatalf("Go record-array decisions missing from Lean:\n%s", strings.Join(missing, "\n"))
	}
}
