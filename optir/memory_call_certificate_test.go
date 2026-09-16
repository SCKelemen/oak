package optir

import (
	"reflect"
	"strings"
	"testing"
)

func TestDeriveCheckedMemoryCallSummaryJoinsCanonicalMayEffects(t *testing.T) {
	node := checkedMemoryCertificateDirectNode(t, "effects", []CheckedMemoryCallAccess{
		{Region: "global:z", Kind: MemoryRead, ValueType: "u64"},
		{Region: "global:x", Kind: MemoryRead, ValueType: "u32"},
		{Region: "global:x", Kind: MemoryWrite, ValueType: "u32"},
	})
	summary, err := DeriveCheckedMemoryCallSummary(node.CFG, node.Authority)
	if err != nil {
		t.Fatal(err)
	}
	want := []CheckedMemoryCallAccess{
		{Region: "global:x", Kind: MemoryReadWrite, ValueType: "u32"},
		{Region: "global:z", Kind: MemoryRead, ValueType: "u64"},
	}
	if summary.Fingerprint() == "" || !reflect.DeepEqual(summary.Accesses(), want) {
		t.Fatalf("summary = %q %+v, want %+v", summary.Fingerprint(), summary.Accesses(), want)
	}
	accesses := summary.Accesses()
	accesses[0].Region = "forged"
	if !reflect.DeepEqual(summary.Accesses(), want) {
		t.Fatal("summary access inspection aliases private state")
	}

	unused := checkedMemoryCertificateDirectNode(t, "unused", []CheckedMemoryCallAccess{
		{Region: "global:x", Kind: MemoryRead, ValueType: "u32"},
	})
	unused.CFG.Blocks[0].Operations = nil
	if _, err := DeriveCheckedMemoryCallSummary(unused.CFG, unused.Authority); err == nil || !strings.Contains(err.Error(), "exact active authority") {
		t.Fatalf("unused authority error = %v", err)
	}
}

func TestCheckedMemoryCallCertificateAuthenticatesTransitiveSummaries(t *testing.T) {
	leaf := checkedMemoryCertificateDirectNode(t, "leaf", []CheckedMemoryCallAccess{
		{Region: "global:state", Kind: MemoryRead, ValueType: "u32"},
		{Region: "global:state", Kind: MemoryWrite, ValueType: "u32"},
	})
	leafSummary := mustCheckedMemoryCallSummary(t, leaf)
	middle := checkedMemoryCertificateCallerNode(t, "middle", "leaf", leafSummary, 8)
	middleSummary := mustCheckedMemoryCallSummary(t, middle)
	root := checkedMemoryCertificateCallerNode(t, "root", "middle", middleSummary, 4)

	// The optimized root may retain checked authority for an operation that a
	// verified rewrite removed. Non-root callees remain exact.
	unused := checkedMemoryRecord(t, Source{Context: "root.oak", Line: 20, Column: 3}, "global:unused", MemoryRead, "u32", false)
	rootCalls := root.Authority.CallRecords()
	unusedCall, err := NewCheckedMemoryCallRecord(Source{Context: "root.oak", Line: 21, Column: 3}, "removed", "removed-summary")
	if err != nil {
		t.Fatal(err)
	}
	rootAuthority, err := NewCheckedMemoryAuthorityWithCalls([]CheckedMemoryAccessRecord{unused}, append(rootCalls, unusedCall))
	if err != nil {
		t.Fatal(err)
	}
	root.Authority = rootAuthority

	certificate, err := NewCheckedMemoryCallCertificate("root", []CheckedMemoryCallCertificateNode{middle, root, leaf})
	if err != nil {
		t.Fatal(err)
	}
	if certificate.Fingerprint() == "" {
		t.Fatal("certificate has no fingerprint")
	}
	if err := VerifyCheckedMemoryCallCertificate("root", root.CFG, root.Authority, certificate); err != nil {
		t.Fatal(err)
	}

	reordered, err := NewCheckedMemoryCallCertificate("root", []CheckedMemoryCallCertificateNode{leaf, root, middle})
	if err != nil || reordered.Fingerprint() != certificate.Fingerprint() {
		t.Fatalf("canonical certificate fingerprints = %q and %q, err=%v", certificate.Fingerprint(), reordered.Fingerprint(), err)
	}
	projection, err := ProjectCheckedMemory(root.CFG, root.Authority)
	if err != nil {
		t.Fatal(err)
	}
	first, err := FingerprintCertifiedRegionMemoryInput(root.CFG, projection.Metadata, projection.Observability, "root", root.Authority, certificate)
	if err != nil {
		t.Fatal(err)
	}
	second, err := FingerprintCertifiedRegionMemoryInput(root.CFG, projection.Metadata, projection.Observability, "root", root.Authority, reordered)
	if err != nil || first == "" || first != second {
		t.Fatalf("certified input fingerprints = %q and %q, err=%v", first, second, err)
	}
	forgedMetadata := projection.Metadata
	forgedMetadata.Operations = append([]MemoryOperationMetadata(nil), projection.Metadata.Operations...)
	forgedMetadata.Operations[0].Accesses = []MemoryAccessSpec{{Region: "global:state", Kind: MemoryWrite}}
	forgedMetadata.Operations[0].CallEffect = MemoryCallMod
	if _, err := FingerprintCertifiedRegionMemoryInput(root.CFG, forgedMetadata, projection.Observability, "root", root.Authority, certificate); err == nil || !strings.Contains(err.Error(), "does not match") {
		t.Fatalf("forged certified metadata error = %v", err)
	}
	changedRoot := root
	changedRoot.CFG = cloneCFG(root.CFG)
	changedRoot.CFG.Blocks[0].Operations = append(changedRoot.CFG.Blocks[0].Operations, Operation{
		Code: OpConstInt, Results: []Value{{ID: 99, Type: "u32"}}, Attributes: []Attribute{{Name: AttributeValue, Value: "1"}},
	})
	changedCertificate, err := NewCheckedMemoryCallCertificate("root", []CheckedMemoryCallCertificateNode{middle, changedRoot, leaf})
	if err != nil {
		t.Fatal(err)
	}
	changedProjection, err := ProjectCheckedMemory(changedRoot.CFG, changedRoot.Authority)
	if err != nil {
		t.Fatal(err)
	}
	changedFingerprint, err := FingerprintCertifiedRegionMemoryInput(
		changedRoot.CFG, changedProjection.Metadata, changedProjection.Observability,
		"root", changedRoot.Authority, changedCertificate,
	)
	if err != nil || changedFingerprint == first {
		t.Fatalf("changed certified input fingerprint = %q, original %q, err=%v", changedFingerprint, first, err)
	}
}

func TestCheckedMemoryCallCertificateRejectsForgedAndOpenGraphs(t *testing.T) {
	leaf := checkedMemoryCertificateDirectNode(t, "leaf", []CheckedMemoryCallAccess{{
		Region: "global:state", Kind: MemoryRead, ValueType: "u32",
	}})
	leafSummary := mustCheckedMemoryCallSummary(t, leaf)
	validRoot := checkedMemoryCertificateCallerNode(t, "root", "leaf", leafSummary, 3)
	extra := checkedMemoryCertificateDirectNode(t, "extra", nil)

	tests := []struct {
		name  string
		root  string
		nodes []CheckedMemoryCallCertificateNode
		want  string
	}{
		{name: "missing root", root: "missing", nodes: []CheckedMemoryCallCertificateNode{validRoot, leaf}, want: "missing root"},
		{name: "missing child", root: "root", nodes: []CheckedMemoryCallCertificateNode{validRoot}, want: "missing callee"},
		{name: "duplicate", root: "root", nodes: []CheckedMemoryCallCertificateNode{validRoot, validRoot, leaf}, want: "repeats node"},
		{name: "unreachable", root: "root", nodes: []CheckedMemoryCallCertificateNode{validRoot, leaf, extra}, want: "unreachable extra"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if _, err := NewCheckedMemoryCallCertificate(test.root, test.nodes); err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("NewCheckedMemoryCallCertificate error = %v, want %q", err, test.want)
			}
		})
	}

	forgedSummary := CheckedMemoryCallSummary{fingerprint: leafSummary.Fingerprint()}
	forgedRoot := checkedMemoryCertificateCallerNode(t, "root", "leaf", forgedSummary, 3)
	if _, err := NewCheckedMemoryCallCertificate("root", []CheckedMemoryCallCertificateNode{forgedRoot, leaf}); err == nil || !strings.Contains(err.Error(), "forged summary") {
		t.Fatalf("underapproximated summary error = %v", err)
	}

	bogusSummary := CheckedMemoryCallSummary{fingerprint: "bogus", accesses: leafSummary.Accesses()}
	bogusRoot := checkedMemoryCertificateCallerNode(t, "root", "leaf", bogusSummary, 3)
	if _, err := NewCheckedMemoryCallCertificate("root", []CheckedMemoryCallCertificateNode{bogusRoot, leaf}); err == nil || !strings.Contains(err.Error(), "forged summary") {
		t.Fatalf("forged fingerprint error = %v", err)
	}

	cycleSummary := CheckedMemoryCallSummary{fingerprint: "cycle"}
	cycle := checkedMemoryCertificateCallerNode(t, "cycle", "cycle", cycleSummary, 2)
	if _, err := NewCheckedMemoryCallCertificate("cycle", []CheckedMemoryCallCertificateNode{cycle}); err == nil || !strings.Contains(err.Error(), "cycle") {
		t.Fatalf("cyclic graph error = %v", err)
	}

	inexactLeaf := leaf
	unused := checkedMemoryRecord(t, Source{Context: "leaf.oak", Line: 50, Column: 2}, "global:other", MemoryRead, "u32", false)
	inexactLeaf.Authority, _ = NewCheckedMemoryAuthority([]CheckedMemoryAccessRecord{leaf.Authority.Records()[0], unused})
	if _, err := NewCheckedMemoryCallCertificate("root", []CheckedMemoryCallCertificateNode{validRoot, inexactLeaf}); err == nil || !strings.Contains(err.Error(), "exact active authority") {
		t.Fatalf("inexact child error = %v", err)
	}
}

func TestCheckedMemoryCallCertificateDefensiveCopiesAndRechecksIntegrity(t *testing.T) {
	leaf := checkedMemoryCertificateDirectNode(t, "leaf", []CheckedMemoryCallAccess{{
		Region: "global:state", Kind: MemoryRead, ValueType: "u32",
	}})
	root := checkedMemoryCertificateCallerNode(t, "root", "leaf", mustCheckedMemoryCallSummary(t, leaf), 3)
	originalRoot := cloneCFG(root.CFG)
	originalAuthority := root.Authority
	certificate, err := NewCheckedMemoryCallCertificate("root", []CheckedMemoryCallCertificateNode{root, leaf})
	if err != nil {
		t.Fatal(err)
	}

	root.CFG.Blocks[0].Operations[0].Attributes[0].Value = "forged"
	leaf.CFG.Blocks[0].Operations[0].MemoryAccessID = "forged"
	if err := VerifyCheckedMemoryCallCertificate("root", originalRoot, originalAuthority, certificate); err != nil {
		t.Fatalf("input mutation changed certificate: %v", err)
	}
	if err := VerifyCheckedMemoryCallCertificate("wrong", originalRoot, originalAuthority, certificate); err == nil || !strings.Contains(err.Error(), "different root") {
		t.Fatalf("wrong root error = %v", err)
	}
	changedRoot := cloneCFG(originalRoot)
	changedRoot.Blocks[0].Operations = append(changedRoot.Blocks[0].Operations, Operation{Code: OpConstInt, Results: []Value{{ID: 99, Type: "u32"}}, Attributes: []Attribute{{Name: AttributeValue, Value: "1"}}})
	if err := VerifyCheckedMemoryCallCertificate("root", changedRoot, originalAuthority, certificate); err == nil || !strings.Contains(err.Error(), "different root inputs") {
		t.Fatalf("changed root CFG error = %v", err)
	}

	corrupted := certificate
	corruptedNode := corrupted.nodes["leaf"]
	corruptedNode.cfg.Blocks[0].Operations[0].MemoryAccessID = "forged"
	corrupted.nodes["leaf"] = corruptedNode
	if err := VerifyCheckedMemoryCallCertificate("root", originalRoot, originalAuthority, corrupted); err == nil {
		t.Fatal("mutated private certificate was accepted")
	}
	projection, err := ProjectCheckedMemory(originalRoot, originalAuthority)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := FingerprintCertifiedRegionMemoryInput(originalRoot, projection.Metadata, projection.Observability, "root", originalAuthority, corrupted); err == nil {
		t.Fatal("certified input accepted a mutated certificate")
	}
}

func checkedMemoryCertificateDirectNode(t *testing.T, name string, effects []CheckedMemoryCallAccess) CheckedMemoryCallCertificateNode {
	t.Helper()
	records := make([]CheckedMemoryAccessRecord, 0, len(effects))
	block := Block{ID: 0, Terminator: Terminator{Kind: TerminatorReturn}}
	nextValue := ValueID(1)
	for index, effect := range effects {
		source := Source{Context: name + ".oak", Line: index + 1, Column: 2}
		record := checkedMemoryRecord(t, source, effect.Region, effect.Kind, effect.ValueType, effect.Kind == MemoryWrite)
		records = append(records, record)
		switch effect.Kind {
		case MemoryRead:
			block.Operations = append(block.Operations, Operation{
				Code: OpLoadRegion, Results: []Value{{ID: nextValue, Type: effect.ValueType}},
				Effects: []Effect{EffectReadMemory}, Source: source, MemoryAccessID: record.ID,
			})
			nextValue++
		case MemoryWrite:
			block.Parameters = append(block.Parameters, Value{ID: nextValue, Type: effect.ValueType})
			block.Operations = append(block.Operations, Operation{
				Code: OpStoreRegion, Operands: []ValueID{nextValue},
				Effects: []Effect{EffectWriteMemory}, Source: source, MemoryAccessID: record.ID,
			})
			nextValue++
		default:
			t.Fatalf("direct test node has unsupported effect %s", effect.Kind)
		}
	}
	authority, err := NewCheckedMemoryAuthority(records)
	if err != nil {
		t.Fatal(err)
	}
	return CheckedMemoryCallCertificateNode{
		Name: name, CFG: CFG{Name: name, Entry: 0, Blocks: []Block{block}}, Authority: authority,
	}
}

func checkedMemoryCertificateCallerNode(t *testing.T, name, callee string, summary CheckedMemoryCallSummary, line int) CheckedMemoryCallCertificateNode {
	t.Helper()
	source := Source{Context: name + ".oak", Line: line, Column: 4}
	call, err := NewCheckedMemoryCallRecordWithAccesses(source, callee, summary.Fingerprint(), summary.Accesses())
	if err != nil {
		t.Fatal(err)
	}
	authority, err := NewCheckedMemoryAuthorityWithCalls(nil, []CheckedMemoryCallRecord{call})
	if err != nil {
		t.Fatal(err)
	}
	return CheckedMemoryCallCertificateNode{
		Name: name,
		CFG: CFG{Name: name, Entry: 0, Blocks: []Block{{
			ID: 0, Operations: []Operation{{
				Code: OpCall, Results: []Value{{ID: 1, Type: "u32"}}, Effects: []Effect{EffectCall}, Attributes: []Attribute{{Name: AttributeCallee, Value: callee}},
				Source: source, MemoryCallID: call.ID,
			}}, Terminator: Terminator{Kind: TerminatorReturn},
		}}},
		Authority: authority,
	}
}

func mustCheckedMemoryCallSummary(t *testing.T, node CheckedMemoryCallCertificateNode) CheckedMemoryCallSummary {
	t.Helper()
	summary, err := DeriveCheckedMemoryCallSummary(node.CFG, node.Authority)
	if err != nil {
		t.Fatal(err)
	}
	return summary
}
