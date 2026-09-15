package asm

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// A callee returning a record beyond two chunks writes it into the frame
// area whose address the caller passes in x8 (docs/spec/94-assembler.md
// §9). Its summary stores the callee's leaves into that area at their
// offsets and widths, so the caller's later loads read the callee's value;
// a load from the wrong offset is refuted.
func TestVerifyMemoryReturnedCallee(t *testing.T) {
	program := "Wide: type = struct { a: u64, b: u64, c: u32 }\n\nmk_wide: (x: u64) -> Wide = Wide { a: x, b: x + u64(1), c: u32(3) }\n"
	p := parser.New(layout.New(scanner.New(program)))
	parsed := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	records := map[string]*ast.RecordLiteral{}
	var callee *ast.FunctionStatement
	for _, stmt := range parsed.Statements {
		switch d := stmt.(type) {
		case *ast.ADTType:
			records[d.Name.Value] = d.Variants[0].Literal.(*ast.RecordLiteral)
		case *ast.FunctionStatement:
			callee = d
		}
	}
	composites := map[string]Composite{"Wide": {Size: 24, Fields: []CompositeField{
		{Name: "a", Offset: 0, Size: 8, Scalar: "u64"},
		{Name: "b", Offset: 8, Size: 8, Scalar: "u64"},
		{Name: "c", Offset: 16, Size: 4, Scalar: "u32"},
	}}}
	pair := func(t *testing.T, decl, asmBody, oakBody string) Verdict {
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
		fn.Callees = map[string]*ast.FunctionStatement{"mk_wide": callee}
		fn.Composites = composites
		fn.Records = records
		if findings := Check(fn, sig, map[string]bool{"mk_wide": true}); len(findings) != 0 {
			t.Fatalf("checker: %v", findings)
		}
		spec, err := parseSignatureWithBody(decl + " = " + oakBody)
		if err != nil {
			t.Fatal(err)
		}
		return Verify(fn, sig, spec.Body)
	}
	call := "  bind x0 = x\n  clobber x8, x9, x29, x30\n  frame 48\n  sub sp, sp, #48\n  stp x29, x30, [sp]\n  add x8, sp, #16\n  bl mk_wide\n"
	ret := "  ldp x29, x30, [sp]\n  add sp, sp, #48\n  ret"
	good := pair(t, "wide_ab: (x: u64) -> u64", call+"  ldr x9, [sp, #16]\n  ldr x0, [sp, #24]\n  add x0, x0, x9\n"+ret, "{\n  w: Wide = mk_wide(x)\n  w.a + w.b\n}")
	if good.Kind != VerdictProven {
		t.Fatalf("a caller reading a memory-returned record must be proven, got %s: %s", good.Kind, good.Message)
	}
	narrow := pair(t, "wide_ac: (x: u64) -> u64", call+"  ldr x9, [sp, #16]\n  ldr w0, [sp, #32]\n  add x0, x0, x9\n"+ret, "{\n  w: Wide = mk_wide(x)\n  w.a + u64(w.c)\n}")
	if narrow.Kind != VerdictProven {
		t.Fatalf("a narrow leaf read from the area must be proven, got %s: %s", narrow.Kind, narrow.Message)
	}
	// The caller reads b where the Oak body reads a: refuted.
	wrong := pair(t, "wide_a: (x: u64) -> u64", call+"  ldr x0, [sp, #24]\n"+ret, "{\n  w: Wide = mk_wide(x)\n  w.a\n}")
	if wrong.Kind != VerdictMismatch {
		t.Fatalf("a load from the wrong leaf must be refuted, got %s: %s", wrong.Kind, wrong.Message)
	}
}
