package asm

import (
	"strings"
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

	// The result area survives across iterations even though the call,
	// rather than a str instruction, writes it. Keep the initial value for
	// zero iterations and carry every result field for subsequent calls.
	// Make the narrow field change too; constant aggregate leaves have a
	// separate coupling limitation, independent of the missing stores.
	var err error
	callee, err = parseSignatureWithBody("mk_wide: (x: u64) -> Wide = Wide { a: x, b: x + u64(1), c: u32_trunc_u64(x) }")
	if err != nil {
		t.Fatal(err)
	}
	loop := `  bind w0 = n
  clobber x8, x19, x20, x29, x30
  frame 80
  sub sp, sp, #80
  stp x29, x30, [sp]
  stp x19, x20, [sp, #16]
  mov w20, w0
  mov x0, #0
  add x8, sp, #32
  bl mk_wide
  mov w19, #0
loop:
  cmp w19, w20
  b.hs done
  ldr x0, [sp, #32]
  add x0, x0, #1
  add x8, sp, #32
  bl mk_wide
  add w19, w19, #1
  b loop
done:
  ldr x0, [sp, #32]
  ldp x19, x20, [sp, #16]
  ldp x29, x30, [sp]
  add sp, sp, #80
  ret`
	oakLoop := `{
  w: Wide = mk_wide(u64(0))
  i: u32 = 0
  while i < n {
    w = mk_wide(w.a + u64(1))
    i = i + u32(1)
  }
  w.a
}`
	guarded := strings.Replace(loop, "  ldr x0, [sp, #32]\n  add x0", "  cmp w19, #4\n  b.hs skip\n  ldr x0, [sp, #32]\n  add x0", 1)
	guarded = strings.Replace(guarded, "  add w19, w19, #1", "skip:\n  add w19, w19, #1", 1)
	guardedOak := strings.Replace(oakLoop, "w = mk_wide(w.a + u64(1))", "i < u32(4) ? { w = mk_wide(w.a + u64(1)) }", 1)
	parked := strings.Replace(loop, "clobber x8,", "clobber x8, x21,", 1)
	parked = strings.Replace(parked, "  mov w20, w0", "  str x21, [sp, #64]\n  add x21, sp, #32\n  mov w20, w0", 1)
	parked = strings.ReplaceAll(parked, "add x8, sp, #32", "mov x8, x21")
	parked = strings.Replace(parked, "  ldp x19, x20", "  ldr x21, [sp, #64]\n  ldp x19, x20", 1)
	forwarded := strings.Replace(parked, "add x21, sp, #32", "mov x21, x8", 1)
	forwarded = strings.ReplaceAll(forwarded, "ldr x0, [sp, #32]", "ldr x0, [x21]")
	for _, tc := range []struct {
		name, result, asm, oak string
		want                   VerdictKind
	}{
		{"loop carries call result", "u64", loop, oakLoop, VerdictProven},
		{"conditional call", "u64", guarded, guardedOak, VerdictProven},
		{"invariant parked area", "u64", parked, oakLoop, VerdictProven},
		{"forwarded result area", "Wide", forwarded, strings.Replace(oakLoop, "\n  w.a\n", "\n  w\n", 1), VerdictProven},
		{"overlapping spill widths", "u64", strings.Replace(loop, "  add x0, x0, #1", "  str xzr, [sp, #48]\n  add x0, x0, #1", 1), oakLoop, VerdictProven},
		{"wrong returned leaf", "u64", strings.Replace(loop, "done:\n  ldr x0, [sp, #32]", "done:\n  ldr x0, [sp, #40]", 1), oakLoop, VerdictMismatch},
		{"different return area", "u64", strings.Replace(loop, "  add x0, x0, #1\n  add x8, sp, #32", "  add x0, x0, #1\n  add x8, sp, #48", 1), oakLoop, VerdictMismatch},
	} {
		t.Run(tc.name, func(t *testing.T) {
			v := pair(t, "repeat: (n: u32) -> "+tc.result, tc.asm, tc.oak)
			if v.Kind != tc.want {
				t.Fatalf("want %s, got %s: %s", tc.want, v.Kind, v.Message)
			}
		})
	}
	t.Run("call address across a join stays outside", func(t *testing.T) {
		body := strings.Replace(loop, "  add x0, x0, #1\n  add x8, sp, #32", "  add x0, x0, #1\n  add x8, sp, #32\ncall_join:", 1)
		v := pair(t, "repeat: (n: u32) -> u64", body, oakLoop)
		if v.Kind != VerdictTrusted || !strings.Contains(v.Message, "invariant frame address") {
			t.Fatalf("want an unresolved call-area address, got %s: %s", v.Kind, v.Message)
		}
	})
	t.Run("loop cannot retain stale call result", func(t *testing.T) {
		// The conditional is deliberately beyond the small witness runs.
		// Those runs cannot justify treating the result area as invariant.
		body := strings.Replace(loop, "  ldr x0, [sp, #32]\n  add x0", "  mov w0, #30000\n  cmp w19, w0\n  b.ne skip\n  ldr x0, [sp, #32]\n  add x0", 1)
		body = strings.Replace(body, "  add w19, w19, #1", "skip:\n  add w19, w19, #1", 1)
		oak := strings.Replace(oakLoop, "    w = mk_wide(w.a + u64(1))", "    i == u32(30000) ? { _ = mk_wide(w.a + u64(1)) }", 1)
		v := pair(t, "repeat: (n: u32) -> u64", body, oak)
		if v.Kind == VerdictProven {
			t.Fatalf("the call changes w.a at iteration 30000: %s", v.Message)
		}
	})
}
