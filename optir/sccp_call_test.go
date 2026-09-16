package optir

import (
	"strings"
	"testing"
)

func sccpCallCFG(operation Operation) CFG {
	return CFG{
		Name:    "call_schema",
		Entry:   0,
		Results: []Type{"u32"},
		Blocks: []Block{{
			ID:         0,
			Parameters: []Value{sccpValue(1, "u32")},
			Operations: []Operation{operation},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}},
		}},
	}
}

func validSCCPCall() Operation {
	return Operation{
		Code:       OpCall,
		Results:    []Value{sccpValue(2, "u32")},
		Operands:   []ValueID{1},
		Effects:    []Effect{EffectCall},
		Attributes: []Attribute{{Name: AttributeCallee, Value: "opaque"}},
	}
}

func TestSCCPCallRequiresClosedSchema(t *testing.T) {
	tests := []struct {
		name      string
		mutate    func(*Operation)
		wantError string
	}{
		{name: "no result", mutate: func(call *Operation) { call.Results = nil }, wantError: "0 results"},
		{name: "multiple results", mutate: func(call *Operation) { call.Results = append(call.Results, sccpValue(3, "u32")) }, wantError: "2 results"},
		{name: "no effect", mutate: func(call *Operation) { call.Effects = nil }, wantError: "exactly one call effect"},
		{name: "wrong effect", mutate: func(call *Operation) { call.Effects = []Effect{EffectReadMemory} }, wantError: "exactly one call effect"},
		{name: "duplicate effect", mutate: func(call *Operation) { call.Effects = []Effect{EffectCall, EffectCall} }, wantError: "exactly one call effect"},
		{name: "extra effect", mutate: func(call *Operation) { call.Effects = append(call.Effects, EffectWriteMemory) }, wantError: "exactly one call effect"},
		{name: "no attribute", mutate: func(call *Operation) { call.Attributes = nil }, wantError: "exactly one callee attribute"},
		{name: "wrong attribute", mutate: func(call *Operation) { call.Attributes = []Attribute{{Name: "extension", Value: "opaque"}} }, wantError: "no callee attribute"},
		{name: "duplicate callee", mutate: func(call *Operation) { call.Attributes = append(call.Attributes, call.Attributes[0]) }, wantError: "exactly one callee attribute"},
		{name: "extra attribute", mutate: func(call *Operation) {
			call.Attributes = append(call.Attributes, Attribute{Name: "extension", Value: "value"})
		}, wantError: "exactly one callee attribute"},
		{name: "empty callee", mutate: func(call *Operation) { call.Attributes[0].Value = "" }, wantError: "no callee attribute"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			call := validSCCPCall()
			test.mutate(&call)
			_, err := AnalyzeSCCP(sccpCallCFG(call))
			if err == nil || !strings.Contains(err.Error(), test.wantError) {
				t.Fatalf("malformed call error = %v, want substring %q", err, test.wantError)
			}
		})
	}
}

func TestSCCPKeepsWellFormedCallUnknownAndEffectful(t *testing.T) {
	call := validSCCPCall()
	cfg := sccpCallCFG(call)
	result, err := AnalyzeSCCP(cfg)
	if err != nil {
		t.Fatal(err)
	}
	value, ok := result.Value(call.Results[0].ID)
	if !ok || value.State != LatticeOverdefined {
		t.Fatalf("call result = %+v, want overdefined", value)
	}

	dead, report, err := EliminateDeadCode(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if report.EliminatedOperations != 0 || len(dead.Blocks[0].Operations) != 1 {
		t.Fatalf("effectful call was eliminated: report=%+v operations=%#v", report, dead.Blocks[0].Operations)
	}
	kept := dead.Blocks[0].Operations[0]
	if len(kept.Effects) != 1 || kept.Effects[0] != EffectCall {
		t.Fatalf("call effects = %v, want [%s]", kept.Effects, EffectCall)
	}
}
