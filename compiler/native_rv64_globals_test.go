package compiler

import (
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/nativegen"
)

func TestNativeRV64RetainsTransitiveVerificationGlobals(t *testing.T) {
	model, err := New().WithSource("rv64_callee_globals.oak", `
side: u32 = u32(0)
unrelated: u32 = u32(0)
leaf: (value: u32): u32 {
  side = value
  value
}
middle: (value: u32): u32 = leaf(value)
caller: (value: u32): u32 = middle(value)
main: (): i32 = 0
`).Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	functions := make(map[string]*ast.FunctionStatement)
	for _, statement := range model.Tree.Root.Statements {
		if function, ok := statement.(*ast.FunctionStatement); ok {
			functions[function.Name.Value] = function
		}
	}
	globals := map[string]asm.Global{
		"side": {Type: "u32", Bits: 32}, "unrelated": {Type: "u32", Bits: 32},
	}
	caller := functions["caller"]
	if caller == nil {
		t.Fatal("missing caller")
	}
	// Exercise direct lowering, without OptIR or candidate search supplying
	// the missing declaration later. This also supplies OptIR's ABI template.
	lowered, err := nativegen.CompileFor(nativegen.Lane{Arch: asm.ArchRV64, Globals: globals}, caller, functions, nil, nil, nil, model.TypeChecker)
	if err != nil {
		t.Fatal(err)
	}
	if len(lowered.Globals) != 1 || lowered.Globals["side"] != globals["side"] {
		t.Fatalf("RV64 source footprint = %+v, want only side", lowered.Globals)
	}
	lowered.Callees = functions
	if verdict := asm.Verify(lowered, caller, caller.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("transitive global verification = %s (%s)", verdict.Kind, verdict.Message)
	}
	_, relocations, err := asm.EncodeFunction(lowered)
	if err != nil {
		t.Fatal(err)
	}
	for _, relocation := range relocations {
		if relocation.Symbol == "side" || relocation.Symbol == "unrelated" {
			t.Fatalf("verification declaration introduced a caller memory access: %+v", relocation)
		}
	}
}
