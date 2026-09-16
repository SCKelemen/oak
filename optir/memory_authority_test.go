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
