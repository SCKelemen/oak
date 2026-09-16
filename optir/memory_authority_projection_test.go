package optir

import (
	"strings"
	"testing"
)

func TestActiveCheckedMemoryAuthorityProjectionChecksAndCopiesClaims(t *testing.T) {
	cfg, authority, direct, call := activeMemoryAuthorityFixture(t)
	projection, err := projectActiveCheckedMemoryAuthority(cfg, authority, checkedMemoryAuthorityExact)
	if err != nil {
		t.Fatal(err)
	}
	if len(projection.direct) != 1 || projection.direct[0] != direct {
		t.Fatalf("direct projection = %+v", projection.direct)
	}
	if len(projection.calls) != 1 || projection.calls[0].ID != call.ID || len(projection.calls[0].Accesses) != 1 {
		t.Fatalf("call projection = %+v", projection.calls)
	}
	projection.calls[0].Accesses[0].Region = "forged"
	if got := authority.callRecords[call.ID].Accesses[0].Region; got != "global:child" {
		t.Fatalf("projected call accesses alias authority: %q", got)
	}
}

func TestActiveCheckedMemoryAuthorityProjectionDistinguishesUpperBoundAndExactCoverage(t *testing.T) {
	cfg, _, direct, call := activeMemoryAuthorityFixture(t)
	extraDirect := activeMemoryAccessRecord(t, Source{Context: "projection.oak", Line: 7, Column: 2}, "global:removed", MemoryRead, "u64", false)
	extraCall := activeMemoryCallRecord(t, Source{Context: "projection.oak", Line: 8, Column: 2}, "removed", "summary:removed", nil)

	tests := []struct {
		name       string
		records    []CheckedMemoryAccessRecord
		calls      []CheckedMemoryCallRecord
		coverage   checkedMemoryAuthorityCoverage
		wantDirect int
		wantCalls  int
		wantError  string
	}{
		{name: "exact active authority", records: []CheckedMemoryAccessRecord{direct}, calls: []CheckedMemoryCallRecord{call}, coverage: checkedMemoryAuthorityExact, wantDirect: 1, wantCalls: 1},
		{name: "root upper bound", records: []CheckedMemoryAccessRecord{direct, extraDirect}, calls: []CheckedMemoryCallRecord{call, extraCall}, coverage: checkedMemoryAuthorityUpperBound, wantDirect: 1, wantCalls: 1},
		{name: "exact omitted access", records: []CheckedMemoryAccessRecord{direct, extraDirect}, calls: []CheckedMemoryCallRecord{call}, coverage: checkedMemoryAuthorityExact, wantError: "access ID"},
		{name: "exact omitted call", records: []CheckedMemoryAccessRecord{direct}, calls: []CheckedMemoryCallRecord{call, extraCall}, coverage: checkedMemoryAuthorityExact, wantError: "call ID"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			authority, err := NewCheckedMemoryAuthorityWithCalls(test.records, test.calls)
			if err != nil {
				t.Fatal(err)
			}
			projection, err := projectActiveCheckedMemoryAuthority(cfg, authority, test.coverage)
			if test.wantError != "" {
				if err == nil || !strings.Contains(err.Error(), test.wantError) {
					t.Fatalf("error = %v, want %q", err, test.wantError)
				}
				return
			}
			if err != nil {
				t.Fatal(err)
			}
			if len(projection.direct) != test.wantDirect || len(projection.calls) != test.wantCalls {
				t.Fatalf("projection = %+v", projection)
			}
		})
	}
}

func TestActiveCheckedMemoryAuthorityProjectionRejectsInvalidIdentityUse(t *testing.T) {
	valid, authority, _, _ := activeMemoryAuthorityFixture(t)
	tests := []struct {
		name   string
		mutate func(*CFG)
		want   string
	}{
		{name: "unknown access", mutate: func(cfg *CFG) { cfg.Blocks[0].Operations[0].MemoryAccessID = "unknown" }, want: "stale or unknown access ID"},
		{name: "unknown call", mutate: func(cfg *CFG) { cfg.Blocks[0].Operations[1].MemoryCallID = "unknown" }, want: "stale or unknown call ID"},
		{name: "both IDs", mutate: func(cfg *CFG) { cfg.Blocks[0].Operations[0].MemoryCallID = cfg.Blocks[0].Operations[1].MemoryCallID }, want: "both memory access and call IDs"},
		{name: "duplicate access", mutate: func(cfg *CFG) {
			operation := cfg.Blocks[0].Operations[0]
			operation.Results = []Value{{ID: 3, Type: "u32"}}
			cfg.Blocks[0].Operations = append(cfg.Blocks[0].Operations, operation)
		}, want: "attached more than once"},
		{name: "duplicate call", mutate: func(cfg *CFG) {
			operation := cfg.Blocks[0].Operations[1]
			operation.Results = []Value{{ID: 3, Type: "u32"}}
			cfg.Blocks[0].Operations = append(cfg.Blocks[0].Operations, operation)
		}, want: "attached more than once"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			cfg := cloneCFG(valid)
			test.mutate(&cfg)
			if _, err := projectActiveCheckedMemoryAuthority(cfg, authority, checkedMemoryAuthorityUpperBound); err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("error = %v, want %q", err, test.want)
			}
		})
	}
}

func TestActiveCheckedMemoryAuthorityProjectionRejectsEveryUntaggedOpaqueOperation(t *testing.T) {
	authority, err := NewCheckedMemoryAuthority(nil)
	if err != nil {
		t.Fatal(err)
	}
	tests := []struct {
		name      string
		operation Operation
		want      string
	}{
		{name: "read", operation: Operation{Code: OpLoadRegion, Effects: []Effect{EffectReadMemory}}, want: "no checked memory access ID"},
		{name: "read without effects", operation: Operation{Code: OpLoadRegion}, want: "no checked memory access ID"},
		{name: "read with trap only", operation: Operation{Code: OpLoadRegion, Effects: []Effect{EffectTrap}}, want: "no checked memory access ID"},
		{name: "write", operation: Operation{Code: OpStoreRegion, Effects: []Effect{EffectWriteMemory}}, want: "no checked memory access ID"},
		{name: "write without effects", operation: Operation{Code: OpStoreRegion}, want: "no checked memory access ID"},
		{name: "write with trap only", operation: Operation{Code: OpStoreRegion, Effects: []Effect{EffectTrap}}, want: "no checked memory access ID"},
		{name: "call", operation: Operation{Code: OpCall, Effects: []Effect{EffectCall}, Attributes: []Attribute{{Name: AttributeCallee, Value: "child"}}}, want: "unknown-clobber"},
		{name: "allocate", operation: Operation{Code: OpIntAdd, Effects: []Effect{EffectAllocate}}, want: "unknown-clobber"},
		{name: "synchronize", operation: Operation{Code: OpIntAdd, Effects: []Effect{EffectSynchronize}}, want: "unknown-clobber"},
		{name: "unknown extension", operation: Operation{Code: "extension.unknown"}, want: "unknown-clobber"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			cfg := activeMemoryOperationCFG(test.operation)
			if _, err := projectActiveCheckedMemoryAuthority(cfg, authority, checkedMemoryAuthorityExact); err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("error = %v, want %q", err, test.want)
			}
		})
	}

	for _, operation := range []Operation{
		{Code: OpConstUnit},
		{Code: OpConstUnit, Effects: []Effect{EffectTrap}},
	} {
		if _, err := projectActiveCheckedMemoryAuthority(activeMemoryOperationCFG(operation), authority, checkedMemoryAuthorityExact); err != nil {
			t.Fatalf("closed no-memory operation %+v: %v", operation, err)
		}
	}
}

func TestActiveCheckedMemoryAuthorityProjectionRejectsMismatchedDirectClaims(t *testing.T) {
	valid, authority, _, _ := activeMemoryAuthorityFixture(t)
	tests := []struct {
		name   string
		mutate func(*Operation)
		want   string
	}{
		{name: "source", mutate: func(operation *Operation) { operation.Source.Column++ }, want: "source scope"},
		{name: "operation shape", mutate: func(operation *Operation) { operation.Code = OpStoreRegion }, want: "load does not match"},
		{name: "result type", mutate: func(operation *Operation) { operation.Results[0].Type = "u64" }, want: "load does not match"},
		{name: "attribute", mutate: func(operation *Operation) { operation.Attributes = []Attribute{{Name: "region", Value: "forged"}} }, want: "has attributes"},
		{name: "effect", mutate: func(operation *Operation) { operation.Effects = nil }, want: "load does not match"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			cfg := cloneCFG(valid)
			test.mutate(&cfg.Blocks[0].Operations[0])
			if _, err := projectActiveCheckedMemoryAuthority(cfg, authority, checkedMemoryAuthorityUpperBound); err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("error = %v, want %q", err, test.want)
			}
		})
	}
}

func TestActiveCheckedMemoryAuthorityProjectionRejectsMismatchedCallClaims(t *testing.T) {
	valid, authority, _, _ := activeMemoryAuthorityFixture(t)
	tests := []struct {
		name   string
		mutate func(*Operation)
		want   string
	}{
		{name: "source", mutate: func(operation *Operation) { operation.Source.Column++ }, want: "source scope"},
		{name: "callee", mutate: func(operation *Operation) { operation.Attributes[0].Value = "other" }, want: "checked callee"},
		{name: "missing callee", mutate: func(operation *Operation) { operation.Attributes = nil }, want: "checked callee"},
		{name: "effect", mutate: func(operation *Operation) { operation.Effects = []Effect{EffectReadMemory} }, want: "canonical call effect"},
		{name: "operation shape", mutate: func(operation *Operation) { operation.Code = OpIntAdd }, want: "canonical call effect"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			cfg := cloneCFG(valid)
			test.mutate(&cfg.Blocks[0].Operations[1])
			if _, err := projectActiveCheckedMemoryAuthority(cfg, authority, checkedMemoryAuthorityUpperBound); err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("error = %v, want %q", err, test.want)
			}
		})
	}
}

func TestActiveCheckedMemoryAuthorityProjectionRejectsInvalidInputs(t *testing.T) {
	cfg, authority, _, _ := activeMemoryAuthorityFixture(t)
	if _, err := projectActiveCheckedMemoryAuthority(cfg, authority, 0); err == nil || !strings.Contains(err.Error(), "invalid checked memory authority coverage") {
		t.Fatalf("invalid coverage error = %v", err)
	}
	malformed := cloneCFG(cfg)
	malformed.Name = ""
	if _, err := projectActiveCheckedMemoryAuthority(malformed, authority, checkedMemoryAuthorityExact); err == nil || !strings.Contains(err.Error(), "function name is empty") {
		t.Fatalf("malformed CFG error = %v", err)
	}
	if _, err := projectActiveCheckedMemoryAuthority(cfg, CheckedMemoryAuthority{}, checkedMemoryAuthorityExact); err == nil || !strings.Contains(err.Error(), "missing or corrupted") {
		t.Fatalf("malformed authority error = %v", err)
	}
}

func activeMemoryAuthorityFixture(t *testing.T) (CFG, CheckedMemoryAuthority, CheckedMemoryAccessRecord, CheckedMemoryCallRecord) {
	t.Helper()
	direct := activeMemoryAccessRecord(t, Source{Context: "projection.oak", Line: 2, Column: 3}, "global:direct", MemoryRead, "u32", false)
	call := activeMemoryCallRecord(t, Source{Context: "projection.oak", Line: 3, Column: 3}, "child", "summary:child", []CheckedMemoryCallAccess{{
		Region: "global:child", Kind: MemoryWrite, ValueType: "u64",
	}})
	authority, err := NewCheckedMemoryAuthorityWithCalls([]CheckedMemoryAccessRecord{direct}, []CheckedMemoryCallRecord{call})
	if err != nil {
		t.Fatal(err)
	}
	cfg := CFG{Name: "root", Entry: 0, Results: []Type{"u32"}, Blocks: []Block{{
		ID: 0, Operations: []Operation{
			{Code: OpLoadRegion, Results: []Value{{ID: 1, Type: "u32"}}, Effects: []Effect{EffectReadMemory}, Source: direct.Source, MemoryAccessID: direct.ID},
			{Code: OpCall, Results: []Value{{ID: 2, Type: "u32"}}, Operands: []ValueID{1}, Effects: []Effect{EffectCall}, Attributes: []Attribute{{Name: AttributeCallee, Value: "child"}}, Source: call.Source, MemoryCallID: call.ID},
		}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{2}},
	}}}
	return cfg, authority, direct, call
}

func activeMemoryOperationCFG(operation Operation) CFG {
	return CFG{Name: "operation", Entry: 0, Blocks: []Block{{
		ID: 0, Operations: []Operation{operation}, Terminator: Terminator{Kind: TerminatorReturn},
	}}}
}

func activeMemoryAccessRecord(t *testing.T, source Source, region RegionID, kind MemoryAccessKind, typ Type, whole bool) CheckedMemoryAccessRecord {
	t.Helper()
	record, err := NewCheckedMemoryAccessRecord(source, region, kind, typ, whole, false)
	if err != nil {
		t.Fatal(err)
	}
	return record
}

func activeMemoryCallRecord(t *testing.T, source Source, callee, fingerprint string, accesses []CheckedMemoryCallAccess) CheckedMemoryCallRecord {
	t.Helper()
	record, err := NewCheckedMemoryCallRecordWithAccesses(source, callee, fingerprint, accesses)
	if err != nil {
		t.Fatal(err)
	}
	return record
}
