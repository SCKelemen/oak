package optir

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// Oak.OptIRMemoryAuthorityProjection proves the structural list/authority
// model. These bounded pins require representative decisions made by the Go
// CFG projector to appear as kernel-checked Lean examples; they are not a
// universal implementation refinement.
func TestActiveCheckedMemoryAuthorityProjectionMatchesLeanPins(t *testing.T) {
	contents, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "OptIRMemoryAuthorityProjection.lean"))
	if err != nil {
		t.Fatal(err)
	}
	lean := strings.Join(strings.Fields(string(contents)), " ")

	direct := activeMemoryAccessRecord(t, Source{Context: "projection.oak", Line: 2, Column: 3}, "global:x", MemoryRead, "u32", false)
	call := activeMemoryCallRecord(t, Source{Context: "projection.oak", Line: 3, Column: 3}, "leaf", "summary:leaf", nil)
	authority, err := NewCheckedMemoryAuthorityWithCalls([]CheckedMemoryAccessRecord{direct}, []CheckedMemoryCallRecord{call})
	if err != nil {
		t.Fatal(err)
	}
	valid := CFG{Name: "root", Entry: 0, Results: []Type{"u32"}, Blocks: []Block{{
		ID: 0, Operations: []Operation{
			{Code: OpLoadRegion, Results: []Value{{ID: 1, Type: "u32"}}, Effects: []Effect{EffectReadMemory}, Source: direct.Source, MemoryAccessID: direct.ID},
			{Code: OpCall, Results: []Value{{ID: 2, Type: "u32"}}, Operands: []ValueID{1}, Effects: []Effect{EffectCall}, Attributes: []Attribute{{Name: AttributeCallee, Value: "leaf"}}, Source: call.Source, MemoryCallID: call.ID},
		}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{2}},
	}}}
	empty := CFG{Name: "root", Entry: 0, Blocks: []Block{{ID: 0, Terminator: Terminator{Kind: TerminatorReturn}}}}

	tests := []struct {
		name      string
		cfg       CFG
		authority CheckedMemoryAuthority
		coverage  checkedMemoryAuthorityCoverage
		want      bool
		leanPin   string
	}{
		{name: "exact active authority", cfg: valid, authority: authority, coverage: checkedMemoryAuthorityExact, want: true,
			leanPin: `example : check .exact authority [directOperation, callOperation] expected = true := by decide`},
		{name: "upper-bound unused authority", cfg: empty, authority: authority, coverage: checkedMemoryAuthorityUpperBound, want: true,
			leanPin: `example : check .upperBound authority [] ⟨[], []⟩ = true := by decide`},
		{name: "exact unused authority", cfg: empty, authority: authority, coverage: checkedMemoryAuthorityExact,
			leanPin: `example : check .exact authority [] ⟨[], []⟩ = false := by decide`},
		{name: "both IDs", cfg: mutateProjectionCFG(valid, func(operation *Operation) { operation.MemoryCallID = call.ID }), authority: authority, coverage: checkedMemoryAuthorityUpperBound,
			leanPin: `example : check .upperBound authority [⟨"source:1", .direct readShape, some "access:1", some "call:1"⟩] ⟨[], []⟩ = false := by decide`},
		{name: "unknown ID", cfg: mutateProjectionCFG(valid, func(operation *Operation) { operation.MemoryAccessID = "unknown" }), authority: authority, coverage: checkedMemoryAuthorityUpperBound,
			leanPin: `example : check .upperBound authority [⟨"source:1", .direct readShape, some "unknown", none⟩] ⟨[], []⟩ = false := by decide`},
		{name: "duplicate ID", cfg: duplicateProjectionAccess(valid), authority: authority, coverage: checkedMemoryAuthorityUpperBound,
			leanPin: `example : check .upperBound authority [directOperation, directOperation] ⟨[readAccess, readAccess], []⟩ = false := by decide`},
		{name: "untagged direct opcode", cfg: mutateProjectionCFG(valid, func(operation *Operation) { operation.MemoryAccessID = ""; operation.Effects = nil }), authority: authority, coverage: checkedMemoryAuthorityUpperBound,
			leanPin: `example : check .upperBound authority [⟨"source:1", .direct readShape, none, none⟩] ⟨[], []⟩ = false := by decide`},
		{name: "opaque effect", cfg: activeMemoryOperationCFG(Operation{Code: "extension.unknown"}), authority: authority, coverage: checkedMemoryAuthorityUpperBound,
			leanPin: `example : check .upperBound authority [⟨"source:1", .opaqueEffect, none, none⟩] ⟨[], []⟩ = false := by decide`},
		{name: "moved source", cfg: mutateProjectionCFG(valid, func(operation *Operation) { operation.Source.Column++ }), authority: authority, coverage: checkedMemoryAuthorityUpperBound,
			leanPin: `example : check .upperBound authority [⟨"moved", .direct readShape, some "access:1", none⟩] ⟨[], []⟩ = false := by decide`},
		{name: "changed shape", cfg: mutateProjectionCFG(valid, func(operation *Operation) { operation.Results[0].Type = "u64" }), authority: authority, coverage: checkedMemoryAuthorityUpperBound,
			leanPin: `example : check .upperBound authority [⟨"source:1", .direct { readShape with valueType := "u64" }, some "access:1", none⟩] ⟨[], []⟩ = false := by decide`},
		{name: "changed callee", cfg: mutateProjectionCallCFG(valid, func(operation *Operation) { operation.Attributes[0].Value = "other" }), authority: authority, coverage: checkedMemoryAuthorityUpperBound,
			leanPin: `example : check .upperBound authority [⟨"source:2", .call "other", none, some "call:1"⟩] ⟨[], []⟩ = false := by decide`},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			projection, err := projectActiveCheckedMemoryAuthority(test.cfg, test.authority, test.coverage)
			if got := err == nil; got != test.want {
				t.Fatalf("Go projection accepted = %v, want %v: %v", got, test.want, err)
			}
			if test.want && test.name == "exact active authority" &&
				(len(projection.direct) != 1 || len(projection.calls) != 1 || len(projection.calls[0].Accesses) != 0) {
				t.Fatalf("exact projection = %+v", projection)
			}
			if !strings.Contains(lean, strings.Join(strings.Fields(test.leanPin), " ")) {
				t.Fatalf("Lean projection model is missing decision pin:\n%s", test.leanPin)
			}
		})
	}
}

func mutateProjectionCFG(cfg CFG, mutate func(*Operation)) CFG {
	result := cloneCFG(cfg)
	mutate(&result.Blocks[0].Operations[0])
	return result
}

func mutateProjectionCallCFG(cfg CFG, mutate func(*Operation)) CFG {
	result := cloneCFG(cfg)
	mutate(&result.Blocks[0].Operations[1])
	return result
}

func duplicateProjectionAccess(cfg CFG) CFG {
	result := cloneCFG(cfg)
	duplicate := result.Blocks[0].Operations[0]
	duplicate.Results = []Value{{ID: 3, Type: "u32"}}
	result.Blocks[0].Operations = append(result.Blocks[0].Operations, duplicate)
	return result
}
