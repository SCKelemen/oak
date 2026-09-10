package typechecker

import (
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// Region parameters erase before checking (docs/spec/50-borrowing.md
// section 8c): View[T, R] is []T, Span[T, R] is [*]T, a region argument to a
// region record is dropped, and the side table keeps the structure.
func TestRegionParametersEraseAndRecord(t *testing.T) {
	src := `
Cursor[R]: type = struct { data: View[u8, R], pos: u32 }
frame[R]: (buf: View[u8, R], at: u32): View[u8, R] = subslice(buf, at, 2)
tail[R]: (buf: Span[u8, R], from: u32): Span[u8, R] = subslice(buf, from, 1)
open[R]: (buf: View[u8, R]): Cursor[R] = Cursor { data: buf, pos: 0 }
advance[R]: (c: Cursor[R], n: u32): Cursor[R] {
  next: Cursor[R] = Cursor { data: c.data, pos: c.pos + n }
  next
}
`
	p := parser.New(scanner.New(src))
	program := p.ParseProgram()
	if len(p.Errors()) != 0 {
		t.Fatalf("parse errors: %v", p.Errors())
	}
	tc := New(object.NewEnvironment())
	tc.CheckProgram(program)
	if errs := tc.Errors(); len(errs) != 0 {
		t.Fatalf("type errors after erasure: %v", errs)
	}
	env := tc.Env()
	rec, ok := env.RegionRecord("Cursor")
	if !ok || len(rec.Regions) != 1 || rec.Regions[0] != "R" || rec.Fields["data"] != "R" || rec.Positions[0] != 0 {
		t.Fatalf("Cursor region record = %+v, %v", rec, ok)
	}
	for name, want := range map[string]RegionSignature{
		"frame":   {Regions: []string{"R"}, Params: []string{"R", ""}, Return: "R"},
		"tail":    {Regions: []string{"R"}, Params: []string{"R", ""}, Return: "R"},
		"open":    {Regions: []string{"R"}, Params: []string{"R"}, Return: "R"},
		"advance": {Regions: []string{"R"}, Params: []string{"R", ""}, Return: "R"},
	} {
		sig, ok := env.RegionSignature(name)
		if !ok {
			t.Fatalf("%s: no region signature", name)
		}
		if sig.Return != want.Return || len(sig.Params) != len(want.Params) || len(sig.Regions) != len(want.Regions) {
			t.Fatalf("%s: signature = %+v, want %+v", name, sig, want)
		}
		for i := range want.Params {
			if sig.Params[i] != want.Params[i] {
				t.Fatalf("%s: param %d region = %q, want %q", name, i, sig.Params[i], want.Params[i])
			}
		}
	}
	// The erased declarations are ordinary: the record has no type
	// parameters left and the functions are not templates.
	if tc.IsFunctionTemplate("frame") || tc.IsFunctionTemplate("open") {
		t.Fatal("region-only parameters must not leave a template behind")
	}
	scheme, ok := env.Get("frame")
	if !ok {
		t.Fatal("frame not declared")
	}
	fn, isFn := scheme.Type.(*FunctionType)
	if !isFn {
		t.Fatalf("frame type = %T", scheme.Type)
	}
	if arr, isArr := fn.ReturnType.(*ArrayType); !isArr || !arr.IsSlice {
		t.Fatalf("frame returns %v, want []u8", fn.ReturnType)
	}
	if arr, isArr := fn.Parameters[0].(*ArrayType); !isArr || !arr.IsSlice {
		t.Fatalf("frame parameter 0 is %v, want []u8", fn.Parameters[0])
	}
}

// A type parameter used anywhere outside a region position stays a type
// parameter, so ordinary generics are untouched.
func TestNonRegionTypeParametersSurvive(t *testing.T) {
	src := "first[T]: (v: []T): T = v[0]\nmain: (): i32 { 0 }"
	p := parser.New(scanner.New(src))
	program := p.ParseProgram()
	tc := New(object.NewEnvironment())
	tc.CheckProgram(program)
	if _, ok := tc.Env().RegionSignature("first"); ok {
		t.Fatal("first has no region parameters")
	}
	if !tc.IsFunctionTemplate("first") {
		t.Fatal("first must remain a template")
	}
}
