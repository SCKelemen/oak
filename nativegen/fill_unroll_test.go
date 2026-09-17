package nativegen

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/typechecker"
)

func checkedFillFunction(t *testing.T, source, name string) (*ast.FunctionStatement, map[string]*ast.FunctionStatement, map[string]*ast.RecordLiteral, *typechecker.TypeChecker) {
	t.Helper()
	p := parser.New(scanner.New(source))
	program := p.ParseProgram()
	if errors := p.Errors(); len(errors) != 0 {
		t.Fatalf("parse: %v", errors)
	}
	tc := typechecker.New(object.NewEnvironment())
	tc.CheckProgram(program)
	if errors := tc.Errors(); len(errors) != 0 {
		t.Fatalf("check: %v", errors)
	}
	functions := map[string]*ast.FunctionStatement{}
	records := map[string]*ast.RecordLiteral{}
	for _, statement := range program.Statements {
		switch declaration := statement.(type) {
		case *ast.FunctionStatement:
			fn := declaration
			functions[fn.Name.Value] = fn
		case *ast.ADTType:
			if len(declaration.Variants) == 1 {
				if record, ok := declaration.Variants[0].Literal.(*ast.RecordLiteral); ok {
					records[declaration.Name.Value] = record
				}
			}
		}
	}
	fn := functions[name]
	if fn == nil {
		t.Fatalf("function %q not found", name)
	}
	return fn, functions, records, tc
}

func TestUnrollFillsRecognizesCheckedU64ZeroFill(t *testing.T) {
	fn, _, _, tc := checkedFillFunction(t, `
entries: u32 = u32(8)
fill: (pages: [*]u64): () {
  j: u32 = u32(0)
  while j < entries {
    pages[j] = u64(0)
    j = j + u32(1)
  }
}
`, "fill")
	got, changed := unrollFills(fn, fn.Body, tc, map[string]asm.Constant{"entries": {Type: "u32", Value: 8}})
	if !changed {
		t.Fatalf("checked u64 zero fill was not recognized:\n%s", fn.Body.String())
	}
	if got.String() == fn.Body.String() {
		t.Fatal("recognized fill did not change the body")
	}
	if strings.Contains(got.String(), "entries >=") || !strings.Contains(got.String(), "j <= u32(4)") {
		t.Fatalf("checked constant bound was not folded safely:\n%s", got.String())
	}
}

func TestUnrollFillsSkipsShortConstantAndGuardsDynamicBound(t *testing.T) {
	short, _, _, shortTC := checkedFillFunction(t, `
entries: u32 = u32(3)
fill: (pages: [*]u64): () {
  j: u32 = u32(0)
  while j < entries {
    pages[j] = u64(0)
    j = j + u32(1)
  }
}
`, "fill")
	if _, changed := unrollFills(short, short.Body, shortTC, map[string]asm.Constant{"entries": {Type: "u32", Value: 3}}); changed {
		t.Fatal("a fill shorter than one block was rewritten")
	}
	if CanUnrollFills(short, shortTC, map[string]asm.Constant{"entries": {Type: "u32", Value: 3}}) {
		t.Fatal("a fill shorter than one block entered candidate search")
	}
	dynamic, _, _, dynamicTC := checkedFillFunction(t, `
fill: (pages: [*]u64, bound: u32): () {
  j: u32 = u32(0)
  while j < bound {
    pages[j] = u64(0)
    j = j + u32(1)
  }
}
`, "fill")
	got, changed := unrollFills(dynamic, dynamic.Body, dynamicTC, nil)
	if !changed || !strings.Contains(got.String(), "bound >= u32(4)") {
		t.Fatalf("dynamic bound lost its underflow guard:\n%s", got.String())
	}
	if !CanUnrollFills(dynamic, dynamicTC, nil) {
		t.Fatal("a dynamic checked fill was gated out of candidate search")
	}
}

func TestUnrollFillsDoesNotMutateNestedCheckedBody(t *testing.T) {
	fn, _, _, tc := checkedFillFunction(t, `
fill: (pages: [*]u64, bound: u32): () {
  outer: u32 = u32(0)
  while outer < u32(1) {
    j: u32 = u32(0)
    while j < bound {
      pages[j] = u64(0)
      j = j + u32(1)
    }
    outer = outer + u32(1)
  }
}
`, "fill")
	original := fn.Body.String()
	got, changed := unrollFills(fn, fn.Body, tc, nil)
	if !changed || got.String() == original {
		t.Fatalf("nested fill was not rewritten:\n%s", got.String())
	}
	if fn.Body.String() != original {
		t.Fatalf("fill rewrite mutated the checked source body:\nbefore: %s\nafter:  %s", original, fn.Body.String())
	}
}

func TestUnrollFillStageCacheIncludesConstantValues(t *testing.T) {
	fn, functions, _, tc := checkedFillFunction(t, `
entries: u32 = u32(8)
fill: (pages: [*]u64): () {
  j: u32 = u32(0)
  while j < entries {
    pages[j] = u64(0)
    j = j + u32(1)
  }
}
`, "fill")
	stages := func(bound uint64) []rewriteStage {
		return rewriteStages(
			fn, functions,
			map[string]asm.Constant{"entries": {Type: "u32", Value: bound}},
			tc,
			false, false, true, false, false, false, false, false, false, false,
		)
	}
	if got := len(stages(8)); got != 2 {
		t.Fatalf("eight-element fill produced %d stages, want blocked and source", got)
	}
	if got := len(stages(3)); got != 1 {
		t.Fatalf("short fill reused the cached blocked stage: %d stages", got)
	}
}

func TestUnrollFillsDoesNotFoldShadowedGlobalConstant(t *testing.T) {
	fn, _, _, tc := checkedFillFunction(t, `
fill: (pages: [*]u64, entries: u32): () {
  j: u32 = u32(0)
  while j < entries {
    pages[j] = u64(0)
    j = j + u32(1)
  }
}
`, "fill")
	got, changed := unrollFills(fn, fn.Body, tc, map[string]asm.Constant{"entries": {Type: "u32", Value: 8}})
	if !changed || !strings.Contains(got.String(), "entries >= u32(4)") {
		t.Fatalf("shadowed global constant was folded into a parameter bound:\n%s", got.String())
	}
}

func TestUnrollFillsAfterPureIndexHelperExpansion(t *testing.T) {
	fn, _, _, tc := checkedFillFunction(t, `
entries: u32 = u32(8)
fill: (pages: [*]u64, table: u16): () {
  j: u32 = u32(0)
  while j < entries {
    address: u32 = u32(table) * entries + j
    pages[address] = u64(0)
    j = j + u32(1)
  }
}
`, "fill")
	got, changed := unrollFills(fn, fn.Body, tc, map[string]asm.Constant{"entries": {Type: "u32", Value: 8}})
	if !changed {
		t.Fatalf("checked fill through expanded pure index helper was not recognized:\n%s", fn.Body.String())
	}
	if got.String() == fn.Body.String() {
		t.Fatal("recognized fill did not change the body")
	}
}

func TestUnrollFillsSharesOneSlackGuard(t *testing.T) {
	fn, functions, _, tc := checkedFillFunction(t, `
entries: u32 = u32(8)
fill: (pages: [*]u64): () {
  j: u32 = u32(0)
  while j < entries {
    pages[j] = u64(0)
    j = j + u32(1)
  }
}
`, "fill")
	constants := map[string]asm.Constant{"entries": {Type: "u32", Value: 8}}
	got, err := CompileFor(Lane{Arch: asm.ArchArm64, UnrollFills: true, NoReductions: true}, fn, functions, nil, nil, constants, tc)
	if err != nil {
		t.Fatalf("compile blocked fill: %v", err)
	}
	body := Describe(got)
	if strings.Count(body, "str x") != 5 {
		t.Fatalf("blocked fill should contain four main stores and its scalar tail:\n%s", body)
	}
	if strings.Count(body, "b.lo trap") != 1 || strings.Count(body, "b.hi trap") != 1 {
		t.Fatalf("blocked stores did not share exactly one four-lane slack guard:\n%s", body)
	}
	if findings := asm.Check(got, fn, map[string]bool{"fill": true}); len(findings) != 0 {
		t.Fatalf("the seam checker did not derive all four store bounds: %v\n%s", findings, body)
	}
}

func TestUnrollFillsSharesGuardForComputedAddress(t *testing.T) {
	fn, functions, _, tc := checkedFillFunction(t, `
entries: u32 = u32(8)
fill: (pages: [*]u64, table: u16): () {
  j: u32 = u32(0)
  while j < entries {
    address: u32 = u32(table) * entries + j
    pages[address] = u64(0)
    j = j + u32(1)
  }
}
`, "fill")
	constants := map[string]asm.Constant{"entries": {Type: "u32", Value: 8}}
	got, err := CompileFor(Lane{Arch: asm.ArchArm64, UnrollFills: true, NoReductions: true}, fn, functions, nil, nil, constants, tc)
	if err != nil {
		t.Fatalf("compile computed-address fill: %v", err)
	}
	body := Describe(got)
	for _, store := range []string{"str xzr, [x", "#8]", "#16]", "#24]"} {
		if !strings.Contains(body, store) {
			t.Fatalf("computed-address fill lacks %q:\n%s", store, body)
		}
	}
	if strings.Count(body, "b.lo trap") != 1 || strings.Count(body, "b.hi trap") != 1 {
		t.Fatalf("computed-address stores did not share one slack guard:\n%s", body)
	}
	if findings := asm.Check(got, fn, map[string]bool{"fill": true}); len(findings) != 0 {
		t.Fatalf("the seam checker did not derive the computed-address region: %v\n%s", findings, body)
	}
}

func TestUnrollFillsKeepsRecordFieldStoresIndividuallyGuarded(t *testing.T) {
	fn, functions, records, tc := checkedFillFunction(t, `
entries: u32 = u32(8)
Regime: type = struct { pages: [32]u64 }
fill: (s: [*]Regime, dom: u32, table: u16): () {
  j: u32 = u32(0)
  while j < entries {
    address: u32 = u32(table) * entries + j
    s[dom].pages[address] = u64(0)
    j = j + u32(1)
  }
}
`, "fill")
	constants := map[string]asm.Constant{"entries": {Type: "u32", Value: 8}}
	got, err := CompileFor(Lane{Arch: asm.ArchArm64, UnrollFills: true, NoReductions: true}, fn, functions, records, nil, constants, tc)
	if err != nil {
		t.Fatalf("compile record-field fill: %v", err)
	}
	body := Describe(got)
	if strings.Count(body, "str xzr") != 5 {
		t.Fatalf("record-field fill should contain four main stores and its scalar tail:\n%s", body)
	}
	if strings.Count(body, "b.hs trap") < 4 {
		t.Fatalf("record-field stores must retain their individually checked bounds:\n%s", body)
	}
	if strings.Contains(body, "stp xzr") || strings.Contains(body, "stp wzr") {
		t.Fatalf("record-field fill acquired pair-store authority:\n%s", body)
	}
	if findings := asm.Check(got, fn, map[string]bool{"fill": true}); len(findings) != 0 {
		t.Fatalf("the seam checker rejected guarded record-field stores: %v\n%s", findings, body)
	}
}

func TestUnrollFillsRejectsUnsafeShapes(t *testing.T) {
	tests := []struct {
		name   string
		source string
	}{
		{
			name: "nonzero value",
			source: `fill: (pages: [*]u64, bound: u32): () {
  j: u32 = u32(0)
  while j < bound {
    pages[j] = u64(1)
    j = j + u32(1)
  }
}`,
		},
		{
			name: "wrong element width",
			source: `fill: (pages: [*]u32, bound: u32): () {
  j: u32 = u32(0)
  while j < bound {
    pages[j] = u32(0)
    j = j + u32(1)
  }
}`,
		},
		{
			name: "non-unit induction",
			source: `fill: (pages: [*]u64, bound: u32): () {
  j: u32 = u32(0)
  while j < bound {
    pages[j] = u64(0)
    j = j + u32(2)
  }
}`,
		},
		{
			name: "nonlinear address",
			source: `fill: (pages: [*]u64, bound: u32): () {
  j: u32 = u32(0)
  while j < bound {
    address: u32 = j * u32(2)
    pages[address] = u64(0)
    j = j + u32(1)
  }
}`,
		},
		{
			name: "call in address",
			source: `index: (j: u32): u32 { j }
fill: (pages: [*]u64, bound: u32): () {
  j: u32 = u32(0)
  while j < bound {
    address: u32 = index(j)
    pages[address] = u64(0)
    j = j + u32(1)
  }
}`,
		},
		{
			name: "extra statement",
			source: `fill: (pages: [*]u64, bound: u32): () {
  j: u32 = u32(0)
  while j < bound {
    scratch: u32 = j
    pages[j] = u64(0)
    scratch = scratch + u32(1)
    j = j + u32(1)
  }
}`,
		},
		{
			name: "non-u32 induction",
			source: `fill: (pages: [*]u64, bound: u16): () {
  j: u16 = u16(0)
  while j < bound {
    address: u32 = u32(j) + u32(0)
    pages[address] = u64(0)
    j = j + u16(1)
  }
}`,
		},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			fn, _, _, tc := checkedFillFunction(t, test.source, "fill")
			if got, changed := unrollFills(fn, fn.Body, tc, nil); changed {
				t.Fatalf("unsafe fill shape was rewritten:\n%s", got.String())
			}
		})
	}
}

func TestUnrollFillsRV64RetainsCheckedScalarStores(t *testing.T) {
	fn, functions, _, tc := checkedFillFunction(t, `
entries: u32 = u32(8)
fill: (pages: [*]u64): () {
  j: u32 = u32(0)
  while j < entries {
    pages[j] = u64(0)
    j = j + u32(1)
  }
}
`, "fill")
	constants := map[string]asm.Constant{"entries": {Type: "u32", Value: 8}}
	got, err := CompileFor(Lane{Arch: asm.ArchRV64, UnrollFills: true, NoReductions: true}, fn, functions, nil, nil, constants, tc)
	if err != nil {
		t.Fatalf("compile RV64 blocked fill: %v", err)
	}
	if sites := UnrolledFills(got); sites != 1 {
		t.Fatalf("RV64 blocked-fill sites = %d, want 1", sites)
	}
	if findings := asm.Check(got, fn, map[string]bool{"fill": true}); len(findings) != 0 {
		t.Fatalf("the seam checker rejected RV64 scalar stores: %v\n%s", findings, Describe(got))
	}
}
