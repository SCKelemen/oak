package asm

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// A record argument's large array field read at a symbolic index is a
// read of the memory its leaves are the elements of, on both sides
// (elementUnderIndexTerm, recordArrayMemory): proven by the same term,
// not by a diagram over a sixty-four-way fold.
func TestVerifyRecordArgumentArrayAsMemory(t *testing.T) {
	program := "Bits: type = struct { at: [64]u32, lo: [64]u32 }\n\npick: (a: Bits, i: u32): u32 = a.at[i]\n"
	p := parser.New(layout.New(scanner.New(program)))
	parsed := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	records := map[string]*ast.RecordLiteral{}
	for _, stmt := range parsed.Statements {
		if d, isADT := stmt.(*ast.ADTType); isADT {
			records[d.Name.Value] = d.Variants[0].Literal.(*ast.RecordLiteral)
		}
	}
	composites := map[string]Composite{"Bits": {Size: 512, Fields: []CompositeField{
		{Name: "at", Offset: 0, Size: 256, Elem: "u32", Length: 64},
		{Name: "lo", Offset: 256, Size: 256, Elem: "u32", Length: 64},
	}}}
	verify := func(t *testing.T, decl, asmBody, oakBody string) Verdict {
		t.Helper()
		unit, errs := ParseUnit("v.oakasm", decl+" = {\n"+asmBody+"\n}\n")
		if len(errs) != 0 {
			t.Fatal(errs)
		}
		sig, err := parseSignature(decl)
		if err != nil {
			t.Fatal(err)
		}
		fn := unit.Functions[0]
		fn.Composites = composites
		fn.Records = records
		if findings := Check(fn, sig, nil); len(findings) != 0 {
			t.Fatalf("checker: %v", findings)
		}
		spec, err := parseSignatureWithBody(decl + " = " + oakBody)
		if err != nil {
			t.Fatal(err)
		}
		return Verify(fn, sig, spec.Body)
	}
	asmBody := "  bind x0 = a\n  bind w1 = i\n  cmp w1, #64\n  b.hs trap\n  ldr w0, [x0, w1, uxtw #2]\n  ret\ntrap:\n  brk #1"
	v := verify(t, "pick: (a: Bits, i: u32) -> u32", asmBody, "a.at[i]")
	if v.Kind != VerdictProven || !strings.Contains(v.Message, "a.at[i]") {
		t.Fatalf("the read of a large array field must be one memory read on both sides (a linear form over it), got %s: %s", v.Kind, v.Message)
	}
	if v := verify(t, "pick: (a: Bits, i: u32) -> u32", asmBody, "a.lo[i]"); v.Kind != VerdictMismatch {
		t.Fatalf("reading the other field's memory must be refuted, got %s: %s", v.Kind, v.Message)
	}
	// Two reads at indices one linear form apart decide in the form.
	sum := "  bind x0 = a\n  bind w1 = i\n  clobber w2, w3, w4\n  cmp w1, #64\n  b.hs trap\n  add w2, w1, #1\n  cmp w2, #64\n  b.hs trap\n  ldr w3, [x0, w1, uxtw #2]\n  ldr w4, [x0, w2, uxtw #2]\n  add w0, w3, w4\n  ret\ntrap:\n  brk #1"
	if v := verify(t, "pick: (a: Bits, i: u32) -> u32", sum, "a.at[i] + a.at[i + u32(1)]"); v.Kind != VerdictProven {
		t.Fatalf("two reads of the memory must be proven, got %s: %s", v.Kind, v.Message)
	}
	// A constant index is the leaf parameter itself, as before.
	if v := verify(t, "pick: (a: Bits) -> u32", "  bind x0 = a\n  ldr w0, [x0, #12]\n  ret", "a.at[u32(3)]"); v.Kind != VerdictProven {
		t.Fatalf("a constant element must be proven, got %s: %s", v.Kind, v.Message)
	}
}
