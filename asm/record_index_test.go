package asm

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// A load through a record argument at a register index (`ldr w0, [x0,
// w1, uxtw #2]` under `cmp w1, #4; b.hs trap`) reads the element of the
// array field the address starts, selected from the field's leaves by
// the index — the fold the Oak side builds for `a.at[i]` — so the body
// is proven; a body reading a different field's elements is refuted.
func TestVerifyIndexedLoadThroughRecordArgument(t *testing.T) {
	program := "Bits4: type = struct { at: [4]u32, lo: [4]u32 }\n\npick: (a: Bits4, i: u32): u32 = a.at[i]\n"
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
	composites := map[string]Composite{"Bits4": {Size: 32, Fields: []CompositeField{
		{Name: "at", Offset: 0, Size: 16, Elem: "u32", Length: 4},
		{Name: "lo", Offset: 16, Size: 16, Elem: "u32", Length: 4},
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
	asmBody := "  bind x0 = a\n  bind w1 = i\n  cmp w1, #4\n  b.hs trap\n  ldr w0, [x0, w1, uxtw #2]\n  ret\ntrap:\n  brk #1"
	if v := verify(t, "pick: (a: Bits4, i: u32) -> u32", asmBody, "a.at[i]"); v.Kind != VerdictProven {
		t.Fatalf("an indexed load through a record argument under its guard must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verify(t, "pick: (a: Bits4, i: u32) -> u32", asmBody, "a.lo[i]"); v.Kind != VerdictMismatch {
		t.Fatalf("reading the other field's elements must be refuted, got %s: %s", v.Kind, v.Message)
	}
}
