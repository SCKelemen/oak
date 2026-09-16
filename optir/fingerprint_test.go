package optir

import (
	"strings"
	"testing"
)

func TestFingerprintCFGIsCanonicalAndSensitiveToExactInput(t *testing.T) {
	cfg := licmTestCFG()
	first, err := FingerprintCFG(cfg)
	if err != nil {
		t.Fatal(err)
	}
	second, err := FingerprintCFG(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if first == "" || first != second {
		t.Fatalf("CFG fingerprint is not deterministic: %q, %q", first, second)
	}

	empty := cfg
	empty.Facts = []Fact{}
	empty.Blocks = append([]Block(nil), cfg.Blocks...)
	empty.Blocks[0].Operations = append([]Operation(nil), cfg.Blocks[0].Operations...)
	empty.Blocks[0].Operations[0].Effects = []Effect{}
	emptyFingerprint, err := FingerprintCFG(empty)
	if err != nil {
		t.Fatal(err)
	}
	if emptyFingerprint != first {
		t.Fatalf("nil and empty slices have different fingerprints: %q, %q", first, emptyFingerprint)
	}

	changed := cfg
	changed.Blocks = append([]Block(nil), cfg.Blocks...)
	changed.Blocks[2].Operations = append([]Operation(nil), cfg.Blocks[2].Operations...)
	changed.Blocks[2].Operations[1].Source.Column++
	changedFingerprint, err := FingerprintCFG(changed)
	if err != nil {
		t.Fatal(err)
	}
	if changedFingerprint == first {
		t.Fatal("source identity change did not invalidate the CFG fingerprint")
	}
}

func TestFingerprintCFGRejectsMalformedInput(t *testing.T) {
	cfg := licmTestCFG()
	cfg.Blocks[0].Terminator.True.Target = 99
	if fingerprint, err := FingerprintCFG(cfg); err == nil || fingerprint != "" {
		t.Fatalf("malformed CFG fingerprint = %q, err = %v", fingerprint, err)
	}
}

func TestFingerprintCFGIncludesMemoryCallAuthorityID(t *testing.T) {
	cfg := CFG{Name: "call", Entry: 0, Results: []Type{"u32"}, Blocks: []Block{{
		ID: 0, Operations: []Operation{{
			Code: OpCall, Results: []Value{{ID: 1, Type: "u32"}}, Effects: []Effect{EffectCall},
			Attributes: []Attribute{{Name: AttributeCallee, Value: "pure"}}, MemoryCallID: "summary-a",
		}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}},
	}}}
	first, err := FingerprintCFG(cfg)
	if err != nil {
		t.Fatal(err)
	}
	cfg.Blocks[0].Operations[0].MemoryCallID = "summary-b"
	second, err := FingerprintCFG(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if first == second {
		t.Fatal("memory call authority ID change retained CFG fingerprint")
	}
}

func TestFingerprintRegionMemoryInputIsCanonical(t *testing.T) {
	cfg, metadata, observability := regionMemoryFingerprintInput()
	first, err := FingerprintRegionMemoryInput(cfg, metadata, observability)
	if err != nil {
		t.Fatal(err)
	}
	second, err := FingerprintRegionMemoryInput(cfg, metadata, observability)
	if err != nil {
		t.Fatal(err)
	}
	if first == "" || first != second {
		t.Fatalf("region-memory input fingerprint is not deterministic: %q, %q", first, second)
	}

	reordered := RegionMemoryMetadata{
		Regions: []RegionID{"left", "right"},
		Operations: []MemoryOperationMetadata{
			{
				Site: OperationSite{Block: 1, Index: 0},
				Accesses: []MemoryAccessSpec{
					{Region: "left", Kind: MemoryRead},
					{Region: "right", Kind: MemoryWrite, WholeRegion: true},
				},
			},
			{
				Site: OperationSite{Block: 1, Index: 1},
				Accesses: []MemoryAccessSpec{
					{Region: "right", Kind: MemoryRead},
					{Region: "left", Kind: MemoryWrite, WholeRegion: true},
				},
			},
		},
	}
	canonical, err := FingerprintRegionMemoryInput(cfg, reordered, RegionMemoryObservability{LiveOut: []RegionID{"left", "right"}})
	if err != nil {
		t.Fatal(err)
	}
	if canonical != first {
		t.Fatalf("equivalent declaration order changed fingerprint: %q, %q", first, canonical)
	}

	pure := CFG{
		Name: "empty-memory", Entry: 1, Results: []Type{"u32"},
		Blocks: []Block{{ID: 1, Parameters: []Value{{ID: 1, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}}}},
	}
	nilFingerprint, err := FingerprintRegionMemoryInput(pure, RegionMemoryMetadata{}, RegionMemoryObservability{})
	if err != nil {
		t.Fatal(err)
	}
	emptyFingerprint, err := FingerprintRegionMemoryInput(
		pure,
		RegionMemoryMetadata{Regions: []RegionID{}, Operations: []MemoryOperationMetadata{}},
		RegionMemoryObservability{LiveOut: []RegionID{}},
	)
	if err != nil {
		t.Fatal(err)
	}
	if nilFingerprint != emptyFingerprint {
		t.Fatalf("nil and empty memory inputs have different fingerprints: %q, %q", nilFingerprint, emptyFingerprint)
	}
}

func TestFingerprintRegionMemoryInputCoversEveryInput(t *testing.T) {
	cfg, metadata, observability := regionMemoryFingerprintInput()
	baseline := mustRegionMemoryInputFingerprint(t, cfg, metadata, observability)

	changedCFG := cfg
	changedCFG.Blocks = append([]Block(nil), cfg.Blocks...)
	changedCFG.Blocks[0].Operations = append([]Operation(nil), cfg.Blocks[0].Operations...)
	changedCFG.Blocks[0].Operations[0].Source.Column++

	wholeRegion := cloneRegionMemoryMetadata(metadata)
	wholeRegion.Operations[0].Accesses[0].WholeRegion = false
	volatile := cloneRegionMemoryMetadata(metadata)
	volatile.Operations[0].Accesses[0].Volatile = true
	kinds := cloneRegionMemoryMetadata(metadata)
	kinds.Operations[0].Accesses[0].Kind, kinds.Operations[0].Accesses[1].Kind = kinds.Operations[0].Accesses[1].Kind, kinds.Operations[0].Accesses[0].Kind
	kinds.Operations[0].Accesses[0].WholeRegion, kinds.Operations[0].Accesses[1].WholeRegion = kinds.Operations[0].Accesses[1].WholeRegion, kinds.Operations[0].Accesses[0].WholeRegion
	sites := cloneRegionMemoryMetadata(metadata)
	sites.Operations[0].Site, sites.Operations[1].Site = sites.Operations[1].Site, sites.Operations[0].Site

	tests := []struct {
		name          string
		cfg           CFG
		metadata      RegionMemoryMetadata
		observability RegionMemoryObservability
	}{
		{name: "CFG", cfg: changedCFG, metadata: metadata, observability: observability},
		{name: "whole-region", cfg: cfg, metadata: wholeRegion, observability: observability},
		{name: "volatile", cfg: cfg, metadata: volatile, observability: observability},
		{name: "access-kind", cfg: cfg, metadata: kinds, observability: observability},
		{name: "operation-site", cfg: cfg, metadata: sites, observability: observability},
		{name: "observability", cfg: cfg, metadata: metadata, observability: RegionMemoryObservability{LiveOut: []RegionID{"left"}}},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			changed := mustRegionMemoryInputFingerprint(t, test.cfg, test.metadata, test.observability)
			if changed == baseline {
				t.Fatalf("%s change did not invalidate fingerprint %q", test.name, baseline)
			}
		})
	}
}

func TestFingerprintRegionMemoryInputRejectsMalformedInput(t *testing.T) {
	cfg, metadata, observability := regionMemoryFingerprintInput()
	malformedCFG := cfg
	malformedCFG.Entry = 99
	malformedMetadata := cloneRegionMemoryMetadata(metadata)
	malformedMetadata.Operations[0].Accesses[0].Region = "missing"

	tests := []struct {
		name          string
		cfg           CFG
		metadata      RegionMemoryMetadata
		observability RegionMemoryObservability
		want          string
	}{
		{name: "CFG", cfg: malformedCFG, metadata: metadata, observability: observability, want: "entry block"},
		{name: "metadata", cfg: cfg, metadata: malformedMetadata, observability: observability, want: "undeclared region"},
		{name: "observability", cfg: cfg, metadata: metadata, observability: RegionMemoryObservability{LiveOut: []RegionID{"missing"}}, want: "undeclared region"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			fingerprint, err := FingerprintRegionMemoryInput(test.cfg, test.metadata, test.observability)
			if err == nil || fingerprint != "" || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("malformed %s fingerprint = %q, err = %v", test.name, fingerprint, err)
			}
		})
	}
}

func regionMemoryFingerprintInput() (CFG, RegionMemoryMetadata, RegionMemoryObservability) {
	cfg := CFG{
		Name: "memory-fingerprint", Entry: 1, Results: []Type{"u32"},
		Blocks: []Block{{
			ID: 1, Parameters: []Value{{ID: 1, Type: "u32"}},
			Operations: []Operation{
				{Code: "memory.update", Effects: []Effect{EffectReadMemory, EffectWriteMemory}, Source: Source{Context: "first", Line: 1, Column: 1}},
				{Code: "memory.update", Effects: []Effect{EffectReadMemory, EffectWriteMemory}, Source: Source{Context: "second", Line: 2, Column: 1}},
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}},
		}},
	}
	metadata := RegionMemoryMetadata{
		Regions: []RegionID{"right", "left"},
		Operations: []MemoryOperationMetadata{
			{
				Site: OperationSite{Block: 1, Index: 1},
				Accesses: []MemoryAccessSpec{
					{Region: "left", Kind: MemoryWrite, WholeRegion: true},
					{Region: "right", Kind: MemoryRead},
				},
			},
			{
				Site: OperationSite{Block: 1, Index: 0},
				Accesses: []MemoryAccessSpec{
					{Region: "right", Kind: MemoryWrite, WholeRegion: true},
					{Region: "left", Kind: MemoryRead},
				},
			},
		},
	}
	return cfg, metadata, RegionMemoryObservability{LiveOut: []RegionID{"right", "left"}}
}

func cloneRegionMemoryMetadata(metadata RegionMemoryMetadata) RegionMemoryMetadata {
	clone := RegionMemoryMetadata{Regions: append([]RegionID(nil), metadata.Regions...)}
	clone.Operations = make([]MemoryOperationMetadata, len(metadata.Operations))
	for index, operation := range metadata.Operations {
		clone.Operations[index] = MemoryOperationMetadata{
			Site:     operation.Site,
			Accesses: append([]MemoryAccessSpec(nil), operation.Accesses...),
		}
	}
	return clone
}

func mustRegionMemoryInputFingerprint(t *testing.T, cfg CFG, metadata RegionMemoryMetadata, observability RegionMemoryObservability) string {
	t.Helper()
	fingerprint, err := FingerprintRegionMemoryInput(cfg, metadata, observability)
	if err != nil {
		t.Fatal(err)
	}
	return fingerprint
}
