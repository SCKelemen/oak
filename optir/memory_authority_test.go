package optir

import (
	"reflect"
	"strings"
	"testing"
)

func TestCheckedMemoryAuthorityProjectsExactGlobalAccesses(t *testing.T) {
	read := checkedMemoryRecord(t, Source{Context: "memory.oak", Line: 3, Column: 10}, "global:counter", MemoryRead, "u32", false)
	write := checkedMemoryRecord(t, Source{Context: "memory.oak", Line: 4, Column: 3}, "global:counter", MemoryWrite, "u32", true)
	authority, err := NewCheckedMemoryAuthority([]CheckedMemoryAccessRecord{write, read})
	if err != nil {
		t.Fatal(err)
	}
	cfg := CFG{Name: "memory", Entry: 0, Results: []Type{"u32"}, Blocks: []Block{{
		ID: 0, Parameters: []Value{{ID: 1, Type: "u32"}}, Operations: []Operation{
			{Code: OpLoadRegion, Results: []Value{{ID: 2, Type: "u32"}}, Effects: []Effect{EffectReadMemory}, Source: read.Source, MemoryAccessID: read.ID},
			{Code: OpStoreRegion, Operands: []ValueID{1}, Effects: []Effect{EffectWriteMemory}, Source: write.Source, MemoryAccessID: write.ID},
		}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{2}},
	}}}
	projection, err := ProjectCheckedMemory(cfg, authority)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyCheckedMemoryProjection(cfg, authority, projection); err != nil {
		t.Fatal(err)
	}
	if projection.Fingerprint() == "" {
		t.Fatal("checked memory projection has no transport fingerprint")
	}
	if !reflect.DeepEqual(projection.Metadata.Regions, []RegionID{"global:counter"}) ||
		!reflect.DeepEqual(projection.Observability.LiveOut, []RegionID{"global:counter"}) || len(projection.Metadata.Operations) != 2 {
		t.Fatalf("checked memory projection = %+v", projection)
	}
	if projection.Metadata.Operations[0].Accesses[0].Kind != MemoryRead ||
		projection.Metadata.Operations[1].Accesses[0] != (MemoryAccessSpec{Region: "global:counter", Kind: MemoryWrite, WholeRegion: true}) {
		t.Fatalf("projected accesses = %+v", projection.Metadata.Operations)
	}

	records := authority.Records()
	records[0].Region = "forged"
	if authority.Records()[0].Region == "forged" {
		t.Fatal("authority inspection aliases internal records")
	}
	other, err := NewCheckedMemoryAuthority([]CheckedMemoryAccessRecord{read})
	if err != nil || authority.Fingerprint() == "" || authority.Fingerprint() == other.Fingerprint() {
		t.Fatalf("authority fingerprints = %q and %q, err=%v", authority.Fingerprint(), other.Fingerprint(), err)
	}
}

func TestCheckedMemoryAuthorityProjectsExactNoModRefCall(t *testing.T) {
	read := checkedMemoryRecord(t, Source{Context: "calls.oak", Line: 3, Column: 3}, "global:counter", MemoryRead, "u32", false)
	call, err := NewCheckedMemoryCallRecord(Source{Context: "calls.oak", Line: 4, Column: 8}, "identity", "summary:identity:v1")
	if err != nil {
		t.Fatal(err)
	}
	authority, err := NewCheckedMemoryAuthorityWithCalls([]CheckedMemoryAccessRecord{read}, []CheckedMemoryCallRecord{call})
	if err != nil {
		t.Fatal(err)
	}
	cfg := CFG{Name: "caller", Entry: 0, Results: []Type{"u32"}, Blocks: []Block{{
		ID: 0, Operations: []Operation{
			{Code: OpLoadRegion, Results: []Value{{ID: 1, Type: "u32"}}, Effects: []Effect{EffectReadMemory}, Source: read.Source, MemoryAccessID: read.ID},
			{Code: OpCall, Results: []Value{{ID: 2, Type: "u32"}}, Operands: []ValueID{1}, Effects: []Effect{EffectCall}, Attributes: []Attribute{{Name: AttributeCallee, Value: "identity"}}, Source: call.Source, MemoryCallID: call.ID},
		}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{2}},
	}}}
	projection, err := ProjectCheckedMemory(cfg, authority)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyCheckedMemoryProjection(cfg, authority, projection); err != nil {
		t.Fatal(err)
	}
	if len(projection.Metadata.Operations) != 2 || projection.Metadata.Operations[1].CallEffect != MemoryCallNoModRef || len(projection.Metadata.Operations[1].Accesses) != 0 {
		t.Fatalf("checked call projection = %+v", projection.Metadata)
	}
	mutated := projection
	mutated.Metadata.Operations = append([]MemoryOperationMetadata(nil), projection.Metadata.Operations...)
	mutated.Metadata.Operations[1].CallEffect = ""
	if err := VerifyCheckedMemoryProjection(cfg, authority, mutated); err == nil || !strings.Contains(err.Error(), "mutated") {
		t.Fatalf("mutated call projection error = %v", err)
	}
	memory, err := AnalyzeRegionMemorySSA(cfg, projection.Metadata)
	if err != nil {
		t.Fatal(err)
	}
	if len(memory.Accesses) != 1 || memory.Accesses[0].Kind != MemoryRead {
		t.Fatalf("no-ModRef call created memory accesses: %+v", memory.Accesses)
	}

	calls := authority.CallRecords()
	calls[0].Callee = "forged"
	if authority.CallRecords()[0].Callee != "identity" {
		t.Fatal("call-record inspection aliases authority")
	}
	changed, err := NewCheckedMemoryCallRecord(call.Source, call.Callee, "summary:identity:v2")
	if err != nil {
		t.Fatal(err)
	}
	other, err := NewCheckedMemoryAuthorityWithCalls([]CheckedMemoryAccessRecord{read}, []CheckedMemoryCallRecord{changed})
	if err != nil || authority.Fingerprint() == other.Fingerprint() {
		t.Fatalf("summary change retained authority fingerprint, err=%v", err)
	}
}

func TestCheckedMemoryAuthorityProjectsCanonicalRefCall(t *testing.T) {
	source := Source{Context: "calls.oak", Line: 7, Column: 5}
	input := []CheckedMemoryCallAccess{
		{Region: "global:right", Kind: MemoryRead, ValueType: "u64"},
		{Region: "global:left", Kind: MemoryRead, ValueType: "u32"},
	}
	call, err := NewCheckedMemoryCallRecordWithAccesses(source, "sum", "summary:sum:v1", input)
	if err != nil {
		t.Fatal(err)
	}
	input[0].Region = "forged"
	if got := call.Accesses[0].Region; got != "global:left" {
		t.Fatalf("canonical call access starts with %q", got)
	}
	canonicalAgain, err := NewCheckedMemoryCallRecordWithAccesses(source, "sum", "summary:sum:v1", []CheckedMemoryCallAccess{
		{Region: "global:left", Kind: MemoryRead, ValueType: "u32"},
		{Region: "global:right", Kind: MemoryRead, ValueType: "u64"},
	})
	if err != nil || canonicalAgain.ID != call.ID {
		t.Fatalf("canonical call IDs = %q and %q, err=%v", call.ID, canonicalAgain.ID, err)
	}
	authority, err := NewCheckedMemoryAuthorityWithCalls(nil, []CheckedMemoryCallRecord{call})
	if err != nil {
		t.Fatal(err)
	}
	if !authority.HasMemoryEffects() {
		t.Fatal("Ref-only authority reports no memory effects")
	}
	cfg := CFG{Name: "caller", Entry: 0, Results: []Type{"u64"}, Blocks: []Block{{
		ID: 0, Operations: []Operation{{
			Code: OpCall, Results: []Value{{ID: 1, Type: "u64"}}, Effects: []Effect{EffectCall},
			Attributes: []Attribute{{Name: AttributeCallee, Value: "sum"}}, Source: source, MemoryCallID: call.ID,
		}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}},
	}}}
	projection, err := ProjectCheckedMemory(cfg, authority)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyCheckedMemoryProjection(cfg, authority, projection); err != nil {
		t.Fatal(err)
	}
	wantAccesses := []MemoryAccessSpec{
		{Region: "global:left", Kind: MemoryRead},
		{Region: "global:right", Kind: MemoryRead},
	}
	if got := projection.Metadata; !reflect.DeepEqual(got.Regions, []RegionID{"global:left", "global:right"}) ||
		len(got.Operations) != 1 || got.Operations[0].CallEffect != MemoryCallRef || !reflect.DeepEqual(got.Operations[0].Accesses, wantAccesses) {
		t.Fatalf("Ref projection = %+v", got)
	}
	ssa, err := AnalyzeRegionMemorySSA(cfg, projection.Metadata)
	if err != nil {
		t.Fatal(err)
	}
	if len(ssa.Accesses) != 2 || ssa.Accesses[0].Kind != MemoryRead || ssa.Accesses[1].Kind != MemoryRead ||
		ssa.Accesses[0].Output != 0 || ssa.Accesses[1].Output != 0 {
		t.Fatalf("Ref call memory SSA = %+v", ssa.Accesses)
	}

	inspection := authority.CallRecords()
	inspection[0].Accesses[0].Region = "forged"
	if authority.CallRecords()[0].Accesses[0].Region != "global:left" {
		t.Fatal("call access inspection aliases authority")
	}
	changed, err := NewCheckedMemoryCallRecordWithAccesses(source, "sum", "summary:sum:v1", []CheckedMemoryCallAccess{{
		Region: "global:left", Kind: MemoryRead, ValueType: "u64",
	}})
	if err != nil {
		t.Fatal(err)
	}
	other, err := NewCheckedMemoryAuthorityWithCalls(nil, []CheckedMemoryCallRecord{changed})
	if err != nil || authority.Fingerprint() == other.Fingerprint() {
		t.Fatalf("call access change retained authority fingerprint, err=%v", err)
	}
}

func TestCheckedMemoryCallRefAuthorityRejectsUnsafeOrInconsistentAccesses(t *testing.T) {
	source := Source{Context: "calls.oak", Line: 3, Column: 4}
	tests := []struct {
		name   string
		access []CheckedMemoryCallAccess
		want   string
	}{
		{name: "write", access: []CheckedMemoryCallAccess{{Region: "global:x", Kind: MemoryWrite, ValueType: "u32", WholeRegion: true}}, want: "unsupported access"},
		{name: "unknown kind", access: []CheckedMemoryCallAccess{{Region: "global:x", Kind: "forged", ValueType: "u32"}}, want: "unsupported access"},
		{name: "whole read", access: []CheckedMemoryCallAccess{{Region: "global:x", Kind: MemoryRead, ValueType: "u32", WholeRegion: true}}, want: "unsupported access"},
		{name: "volatile", access: []CheckedMemoryCallAccess{{Region: "global:x", Kind: MemoryRead, ValueType: "u32", Volatile: true}}, want: "unsupported access"},
		{name: "empty region", access: []CheckedMemoryCallAccess{{Kind: MemoryRead, ValueType: "u32"}}, want: "malformed access"},
		{name: "unsupported type", access: []CheckedMemoryCallAccess{{Region: "global:x", Kind: MemoryRead, ValueType: "f32"}}, want: "malformed access"},
		{name: "duplicate", access: []CheckedMemoryCallAccess{{Region: "global:x", Kind: MemoryRead, ValueType: "u32"}, {Region: "global:x", Kind: MemoryRead, ValueType: "u32"}}, want: "unique canonical"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if _, err := NewCheckedMemoryCallRecordWithAccesses(source, "read", "summary:read:v1", test.access); err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("error = %v, want %q", err, test.want)
			}
		})
	}

	call, err := NewCheckedMemoryCallRecordWithAccesses(source, "read", "summary:read:v1", []CheckedMemoryCallAccess{{
		Region: "global:x", Kind: MemoryRead, ValueType: "u32",
	}})
	if err != nil {
		t.Fatal(err)
	}
	forged := call
	forged.Accesses = append([]CheckedMemoryCallAccess(nil), call.Accesses...)
	forged.Accesses[0].ValueType = "u64"
	if _, err := NewCheckedMemoryAuthorityWithCalls(nil, []CheckedMemoryCallRecord{forged}); err == nil || !strings.Contains(err.Error(), "stale or forged") {
		t.Fatalf("forged call access error = %v", err)
	}
	direct := checkedMemoryRecord(t, Source{Context: "calls.oak", Line: 2, Column: 2}, "global:x", MemoryRead, "u64", false)
	if _, err := NewCheckedMemoryAuthorityWithCalls([]CheckedMemoryAccessRecord{direct}, []CheckedMemoryCallRecord{call}); err == nil || !strings.Contains(err.Error(), "both u64 and u32") {
		t.Fatalf("inconsistent call/direct type error = %v", err)
	}
	pure, err := NewCheckedMemoryCallRecord(source, "pure", "summary:pure:v1")
	if err != nil {
		t.Fatal(err)
	}
	pureAuthority, err := NewCheckedMemoryAuthorityWithCalls(nil, []CheckedMemoryCallRecord{pure})
	if err != nil || pureAuthority.HasMemoryEffects() {
		t.Fatalf("NoModRef-only authority memory effects = %v, err=%v", pureAuthority.HasMemoryEffects(), err)
	}
}

func TestCheckedMemoryCallAuthorityDerivesCanonicalModAndModRef(t *testing.T) {
	source := Source{Context: "calls.oak", Line: 9, Column: 2}
	tests := []struct {
		name     string
		accesses []CheckedMemoryCallAccess
		want     MemoryCallEffect
	}{
		{name: "mod", accesses: []CheckedMemoryCallAccess{{Region: "global:x", Kind: MemoryWrite, ValueType: "u32"}}, want: MemoryCallMod},
		{name: "single-region mod-ref", accesses: []CheckedMemoryCallAccess{{Region: "global:x", Kind: MemoryReadWrite, ValueType: "u32"}}, want: MemoryCallModRef},
		{name: "disjoint mod-ref", accesses: []CheckedMemoryCallAccess{
			{Region: "global:written", Kind: MemoryWrite, ValueType: "u64"},
			{Region: "global:read", Kind: MemoryRead, ValueType: "u32"},
		}, want: MemoryCallModRef},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			record, err := NewCheckedMemoryCallRecordWithAccesses(source, "effect", "summary:effect:v1", test.accesses)
			if err != nil {
				t.Fatal(err)
			}
			for _, access := range record.Accesses {
				if access.WholeRegion || access.Volatile {
					t.Fatalf("call MAY effect gained overwrite/volatile authority: %+v", access)
				}
			}
			authority, err := NewCheckedMemoryAuthorityWithCalls(nil, []CheckedMemoryCallRecord{record})
			if err != nil {
				t.Fatal(err)
			}
			cfg := CFG{Name: "caller", Entry: 0, Results: []Type{"u32"}, Blocks: []Block{{
				ID: 0, Operations: []Operation{{
					Code: OpCall, Results: []Value{{ID: 1, Type: "u32"}}, Effects: []Effect{EffectCall},
					Attributes: []Attribute{{Name: AttributeCallee, Value: "effect"}}, Source: source, MemoryCallID: record.ID,
				}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}},
			}}}
			projection, err := ProjectCheckedMemory(cfg, authority)
			if err != nil {
				t.Fatal(err)
			}
			if got := projection.Metadata.Operations; len(got) != 1 || got[0].CallEffect != test.want {
				t.Fatalf("projected effect = %+v, want %s", got, test.want)
			}
		})
	}

	if _, err := NewCheckedMemoryCallRecordWithAccesses(source, "effect", "summary:effect:v1", []CheckedMemoryCallAccess{
		{Region: "global:x", Kind: MemoryRead, ValueType: "u32"},
		{Region: "global:x", Kind: MemoryWrite, ValueType: "u32"},
	}); err == nil || !strings.Contains(err.Error(), "unique canonical") {
		t.Fatalf("unmerged same-region effects error = %v", err)
	}
}

func TestCheckedMemoryCallAuthorityRejectsMissingForgedAndMismatchedCalls(t *testing.T) {
	call, err := NewCheckedMemoryCallRecord(Source{Context: "calls.oak", Line: 2, Column: 5}, "identity", "summary:identity:v1")
	if err != nil {
		t.Fatal(err)
	}
	authority, err := NewCheckedMemoryAuthorityWithCalls(nil, []CheckedMemoryCallRecord{call})
	if err != nil {
		t.Fatal(err)
	}
	valid := CFG{Name: "caller", Entry: 0, Results: []Type{"u32"}, Blocks: []Block{{
		ID: 0, Operations: []Operation{{
			Code: OpCall, Results: []Value{{ID: 1, Type: "u32"}}, Effects: []Effect{EffectCall},
			Attributes: []Attribute{{Name: AttributeCallee, Value: "identity"}}, Source: call.Source, MemoryCallID: call.ID,
		}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}},
	}}}
	tests := []struct {
		name   string
		mutate func(*CFG)
		want   string
	}{
		{name: "stale", mutate: func(cfg *CFG) { cfg.Blocks[0].Operations[0].MemoryCallID = "stale" }, want: "stale or unknown"},
		{name: "missing", mutate: func(cfg *CFG) { cfg.Blocks[0].Operations[0].MemoryCallID = "" }, want: "unknown-clobber"},
		{name: "source", mutate: func(cfg *CFG) { cfg.Blocks[0].Operations[0].Source.Column++ }, want: "source scope"},
		{name: "callee", mutate: func(cfg *CFG) { cfg.Blocks[0].Operations[0].Attributes[0].Value = "other" }, want: "checked callee"},
		{name: "effect", mutate: func(cfg *CFG) { cfg.Blocks[0].Operations[0].Effects = []Effect{EffectReadMemory} }, want: "canonical call effect"},
		{name: "access ID", mutate: func(cfg *CFG) { cfg.Blocks[0].Operations[0].MemoryAccessID = "other" }, want: "both memory access and call IDs"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			candidate := cloneCFG(valid)
			test.mutate(&candidate)
			if _, err := ProjectCheckedMemory(candidate, authority); err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("ProjectCheckedMemory error = %v, want %q", err, test.want)
			}
		})
	}

	forged := call
	forged.SummaryFingerprint = "summary:forged"
	if _, err := NewCheckedMemoryAuthorityWithCalls(nil, []CheckedMemoryCallRecord{forged}); err == nil || !strings.Contains(err.Error(), "stale or forged") {
		t.Fatalf("forged call record error = %v", err)
	}
	if _, err := NewCheckedMemoryAuthorityWithCalls(nil, []CheckedMemoryCallRecord{call, call}); err == nil || !strings.Contains(err.Error(), "repeats") {
		t.Fatalf("duplicate call record error = %v", err)
	}
}

func TestProjectWithCheckedMemoryCarriesStructuredNoModRefCall(t *testing.T) {
	callRecord, err := NewCheckedMemoryCallRecord(Source{Context: "calls.oak", Line: 2, Column: 3}, "pure", "summary:pure:v1")
	if err != nil {
		t.Fatal(err)
	}
	authority, err := NewCheckedMemoryAuthorityWithCalls(nil, []CheckedMemoryCallRecord{callRecord})
	if err != nil {
		t.Fatal(err)
	}
	call := &Operation{
		Code: OpCall, Results: []Value{{ID: 1, Type: "u32"}}, Effects: []Effect{EffectCall},
		Attributes: []Attribute{{Name: AttributeCallee, Value: "pure"}}, Source: callRecord.Source, MemoryCallID: callRecord.ID,
	}
	function := Function{Name: "caller", Results: []Type{"u32"}, Body: Region{Nodes: []Node{{Operation: call}}, Yield: []ValueID{1}}}
	cfg, projection, err := ProjectWithCheckedMemory(function, authority)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyCheckedMemoryProjection(cfg, authority, projection); err != nil {
		t.Fatal(err)
	}
	if got := projection.Metadata.Operations; len(got) != 1 || got[0].CallEffect != MemoryCallNoModRef || len(got[0].Accesses) != 0 {
		t.Fatalf("structured no-ModRef projection = %+v", got)
	}
}

func TestProjectWithCheckedMemoryCarriesStructuredRefCall(t *testing.T) {
	source := Source{Context: "calls.oak", Line: 5, Column: 7}
	callRecord, err := NewCheckedMemoryCallRecordWithAccesses(source, "read", "summary:read:v1", []CheckedMemoryCallAccess{{
		Region: "global:state", Kind: MemoryRead, ValueType: "u32",
	}})
	if err != nil {
		t.Fatal(err)
	}
	authority, err := NewCheckedMemoryAuthorityWithCalls(nil, []CheckedMemoryCallRecord{callRecord})
	if err != nil {
		t.Fatal(err)
	}
	call := &Operation{
		Code: OpCall, Results: []Value{{ID: 1, Type: "u32"}}, Effects: []Effect{EffectCall},
		Attributes: []Attribute{{Name: AttributeCallee, Value: "read"}}, Source: source, MemoryCallID: callRecord.ID,
	}
	function := Function{Name: "caller", Results: []Type{"u32"}, Body: Region{Nodes: []Node{{Operation: call}}, Yield: []ValueID{1}}}
	cfg, projection, err := ProjectWithCheckedMemory(function, authority)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyCheckedMemoryProjection(cfg, authority, projection); err != nil {
		t.Fatal(err)
	}
	want := []MemoryAccessSpec{{Region: "global:state", Kind: MemoryRead}}
	if got := projection.Metadata.Operations; len(got) != 1 || got[0].CallEffect != MemoryCallRef || !reflect.DeepEqual(got[0].Accesses, want) {
		t.Fatalf("structured Ref projection = %+v", got)
	}
}

func TestProjectWithCheckedMemoryComposesStructuredIdentityAndAuthority(t *testing.T) {
	read := checkedMemoryRecord(t, Source{Context: "memory.oak", Line: 3, Column: 10}, "global:counter", MemoryRead, "u32", false)
	write := checkedMemoryRecord(t, Source{Context: "memory.oak", Line: 4, Column: 3}, "global:counter", MemoryWrite, "u32", true)
	authority, err := NewCheckedMemoryAuthority([]CheckedMemoryAccessRecord{read, write})
	if err != nil {
		t.Fatal(err)
	}
	load := &Operation{
		Code: OpLoadRegion, Results: []Value{{ID: 2, Type: "u32"}}, Effects: []Effect{EffectReadMemory},
		Source: read.Source, MemoryAccessID: read.ID,
	}
	store := &Operation{
		Code: OpStoreRegion, Operands: []ValueID{1}, Effects: []Effect{EffectWriteMemory},
		Source: write.Source, MemoryAccessID: write.ID,
	}
	function := Function{
		Name: "memory", Parameters: []Value{{ID: 1, Type: "u32"}}, Results: []Type{"u32"},
		Body: Region{Nodes: []Node{{Operation: load}, {Operation: store}}, Yield: []ValueID{2}},
	}
	cfg, projection, err := ProjectWithCheckedMemory(function, authority)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyCheckedMemoryProjection(cfg, authority, projection); err != nil {
		t.Fatal(err)
	}
	if got := projection.Metadata.Operations; len(got) != 2 || got[0].Site != (OperationSite{Block: 0, Index: 0}) || got[1].Site != (OperationSite{Block: 0, Index: 1}) {
		t.Fatalf("composed checked memory sites = %+v", got)
	}

	load.MemoryAccessID = "stale"
	if _, _, err := ProjectWithCheckedMemory(function, authority); err == nil || !strings.Contains(err.Error(), "stale or unknown") {
		t.Fatalf("stale structured access error = %v", err)
	}
}

func TestCheckedMemoryAuthorityRejectsForgedStaleAndAmbiguousOperations(t *testing.T) {
	read := checkedMemoryRecord(t, Source{Context: "memory.oak", Line: 2, Column: 8}, "global:counter", MemoryRead, "u32", false)
	authority, err := NewCheckedMemoryAuthority([]CheckedMemoryAccessRecord{read})
	if err != nil {
		t.Fatal(err)
	}
	valid := CFG{Name: "read", Entry: 0, Results: []Type{"u32"}, Blocks: []Block{{
		ID: 0, Operations: []Operation{{
			Code: OpLoadRegion, Results: []Value{{ID: 1, Type: "u32"}}, Effects: []Effect{EffectReadMemory},
			Source: read.Source, MemoryAccessID: read.ID,
		}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}},
	}}}
	tests := []struct {
		name   string
		mutate func(*CFG)
		want   string
	}{
		{name: "stale", mutate: func(cfg *CFG) { cfg.Blocks[0].Operations[0].MemoryAccessID = "stale" }, want: "stale or unknown"},
		{name: "missing", mutate: func(cfg *CFG) { cfg.Blocks[0].Operations[0].MemoryAccessID = "" }, want: "no checked access ID"},
		{name: "source", mutate: func(cfg *CFG) { cfg.Blocks[0].Operations[0].Source.Column++ }, want: "source scope"},
		{name: "kind", mutate: func(cfg *CFG) { cfg.Blocks[0].Operations[0].Code = OpStoreRegion }, want: "load does not match"},
		{name: "attribute", mutate: func(cfg *CFG) {
			cfg.Blocks[0].Operations[0].Attributes = []Attribute{{Name: "region", Value: "forged"}}
		}, want: "has attributes"},
		{name: "without effect", mutate: func(cfg *CFG) { cfg.Blocks[0].Operations[0].Effects = nil }, want: "without a memory effect"},
		{name: "ambiguous", mutate: func(cfg *CFG) {
			cfg.Blocks[0].Operations = append(cfg.Blocks[0].Operations, Operation{
				Code: OpLoadRegion, Results: []Value{{ID: 2, Type: "u32"}}, Effects: []Effect{EffectReadMemory},
				Source: read.Source, MemoryAccessID: read.ID,
			})
		}, want: "attached more than once"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			candidate := cloneCFG(valid)
			test.mutate(&candidate)
			if _, err := ProjectCheckedMemory(candidate, authority); err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("ProjectCheckedMemory error = %v, want %q", err, test.want)
			}
		})
	}

	forged := read
	forged.Region = "global:other"
	if _, err := NewCheckedMemoryAuthority([]CheckedMemoryAccessRecord{forged}); err == nil || !strings.Contains(err.Error(), "stale or forged") {
		t.Fatalf("forged record error = %v", err)
	}
	if _, err := NewCheckedMemoryAuthority([]CheckedMemoryAccessRecord{read, read}); err == nil || !strings.Contains(err.Error(), "repeats") {
		t.Fatalf("duplicate record error = %v", err)
	}
	if _, err := ProjectCheckedMemory(valid, CheckedMemoryAuthority{}); err == nil {
		t.Fatal("zero authority admitted checked memory")
	}
}

func TestCheckedMemoryAuthorityRejectsUntaggedClosedMemoryOpcodesWithoutEffects(t *testing.T) {
	authority, err := NewCheckedMemoryAuthority(nil)
	if err != nil {
		t.Fatal(err)
	}
	for _, test := range []struct {
		name    string
		effects []Effect
		cfg     CFG
	}{
		{name: "load without effects", cfg: CFG{Name: "load", Entry: 0, Results: []Type{"u32"}, Blocks: []Block{{
			ID: 0, Operations: []Operation{{Code: OpLoadRegion, Results: []Value{{ID: 1, Type: "u32"}}}},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}},
		}}}},
		{name: "load with trap only", effects: []Effect{EffectTrap}, cfg: CFG{Name: "load", Entry: 0, Results: []Type{"u32"}, Blocks: []Block{{
			ID: 0, Operations: []Operation{{Code: OpLoadRegion, Results: []Value{{ID: 1, Type: "u32"}}}},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}},
		}}}},
		{name: "store without effects", cfg: CFG{Name: "store", Entry: 0, Blocks: []Block{{
			ID: 0, Parameters: []Value{{ID: 1, Type: "u32"}}, Operations: []Operation{{Code: OpStoreRegion, Operands: []ValueID{1}}},
			Terminator: Terminator{Kind: TerminatorReturn},
		}}}},
		{name: "store with trap only", effects: []Effect{EffectTrap}, cfg: CFG{Name: "store", Entry: 0, Blocks: []Block{{
			ID: 0, Parameters: []Value{{ID: 1, Type: "u32"}}, Operations: []Operation{{Code: OpStoreRegion, Operands: []ValueID{1}}},
			Terminator: Terminator{Kind: TerminatorReturn},
		}}}},
	} {
		t.Run(test.name, func(t *testing.T) {
			test.cfg.Blocks[0].Operations[0].Effects = test.effects
			if _, err := ProjectCheckedMemory(test.cfg, authority); err == nil || !strings.Contains(err.Error(), "no checked access ID") {
				t.Fatalf("ProjectCheckedMemory error = %v", err)
			}
		})
	}
}

func TestCheckedMemoryProjectionRejectsMutationAndStaleCFG(t *testing.T) {
	read := checkedMemoryRecord(t, Source{Line: 2, Column: 3}, "global:g", MemoryRead, TypeBool, false)
	authority, err := NewCheckedMemoryAuthority([]CheckedMemoryAccessRecord{read})
	if err != nil {
		t.Fatal(err)
	}
	cfg := CFG{Name: "read_bool", Entry: 0, Results: []Type{TypeBool}, Blocks: []Block{{
		ID: 0, Operations: []Operation{{Code: OpLoadRegion, Results: []Value{{ID: 1, Type: TypeBool}}, Effects: []Effect{EffectReadMemory}, Source: read.Source, MemoryAccessID: read.ID}},
		Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}},
	}}}
	projection, err := ProjectCheckedMemory(cfg, authority)
	if err != nil {
		t.Fatal(err)
	}
	mutated := projection
	mutated.Observability.LiveOut = []RegionID{"forged"}
	if err := VerifyCheckedMemoryProjection(cfg, authority, mutated); err == nil || !strings.Contains(err.Error(), "mutated") {
		t.Fatalf("mutated projection error = %v", err)
	}
	stale := cloneCFG(cfg)
	stale.Name += ".changed"
	if err := VerifyCheckedMemoryProjection(stale, authority, projection); err == nil || !strings.Contains(err.Error(), "different CFG") {
		t.Fatalf("stale projection error = %v", err)
	}
}

func checkedMemoryRecord(t *testing.T, source Source, region RegionID, kind MemoryAccessKind, typ Type, whole bool) CheckedMemoryAccessRecord {
	t.Helper()
	record, err := NewCheckedMemoryAccessRecord(source, region, kind, typ, whole, false)
	if err != nil {
		t.Fatal(err)
	}
	return record
}
