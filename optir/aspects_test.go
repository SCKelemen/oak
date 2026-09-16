package optir

import (
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/opt"
)

func aspectTestKey(name, version string) opt.ArtifactKey {
	return opt.ArtifactKey{Kind: opt.ArtifactIR, Name: name, Version: version}
}

func TestAnalysisRequirementsAreClosedCanonicalAndDefensive(t *testing.T) {
	input := []AnalysisAspect{AspectTypes, AspectCFGTopology}
	requirements, err := NewAnalysisRequirements("test", input...)
	if err != nil {
		t.Fatal(err)
	}
	input[0] = AspectLayout
	want := []AnalysisAspect{AspectCFGTopology, AspectTypes}
	if requirements.Name() != "test" || !reflect.DeepEqual(requirements.Aspects(), want) {
		t.Fatalf("requirements = %s %v", requirements.Name(), requirements.Aspects())
	}
	copy := requirements.Aspects()
	copy[0] = AspectLayout
	if !reflect.DeepEqual(requirements.Aspects(), want) {
		t.Fatalf("requirements inspection mutated declaration: %v", requirements.Aspects())
	}

	invalid := []struct {
		name    string
		aspects []AnalysisAspect
	}{
		{name: "", aspects: []AnalysisAspect{AspectTypes}},
		{name: "empty"},
		{name: "duplicate", aspects: []AnalysisAspect{AspectTypes, AspectTypes}},
		{name: "unknown", aspects: []AnalysisAspect{"Other"}},
	}
	for _, test := range invalid {
		if _, err := NewAnalysisRequirements(test.name, test.aspects...); err == nil {
			t.Fatalf("invalid requirements %q %v were admitted", test.name, test.aspects)
		}
	}
}

func TestCFGPreservationChecksAspectsIndependently(t *testing.T) {
	before := licmTestCFG()
	after := before
	after.Blocks = append([]Block(nil), before.Blocks...)
	after.Blocks[2].Operations = append([]Operation(nil), before.Blocks[2].Operations...)
	after.Blocks[2].Operations[0].Attributes = append([]Attribute(nil), before.Blocks[2].Operations[0].Attributes...)
	after.Blocks[2].Operations[0].Attributes[0].Value = "3"

	certificate, err := CheckCFGPreservation(
		aspectTestKey("before", "v0"), before,
		aspectTestKey("after", "v1"), after,
		AspectLayout, AspectProofFacts, AspectTypes, AspectMemoryEffects,
		AspectOperationSemantics, AspectSSAIdentity, AspectCFGTopology,
	)
	if err != nil {
		t.Fatal(err)
	}
	checks := certificate.Checks()
	if len(checks) != len(orderedAnalysisAspects) {
		t.Fatalf("checks = %+v", checks)
	}
	for index, aspect := range orderedAnalysisAspects {
		if checks[index].Aspect != aspect {
			t.Fatalf("check order = %+v", checks)
		}
		wantPreserved := aspect != AspectOperationSemantics
		if checks[index].Preserved != wantPreserved {
			t.Fatalf("%s preserved = %v, want %v", aspect, checks[index].Preserved, wantPreserved)
		}
	}
	if !certificate.Preserves(LoopStructureAnalysisRequirements()) {
		t.Fatal("operation-only change did not preserve loop structure requirements")
	}
	if certificate.Preserves(SCCPAnalysisRequirements()) || certificate.Preserves(LICMRequirements()) {
		t.Fatal("operation-only change incorrectly preserved value-dependent requirements")
	}
	inspection := certificate.Checks()
	inspection[0].Preserved = false
	if !certificate.Preserves(LoopStructureAnalysisRequirements()) {
		t.Fatal("certificate inspection slice mutated the certificate")
	}
}

func TestCFGPreservationBindsExactArtifactsAndRejectsMutatedEvidence(t *testing.T) {
	before := licmTestCFG()
	after := before
	after.Blocks = append([]Block(nil), before.Blocks...)
	after.Blocks[2].Operations = append([]Operation(nil), before.Blocks[2].Operations...)
	after.Blocks[2].Operations[1].Source.Column++
	beforeKey := aspectTestKey("cfg.v0", "before")
	afterKey := aspectTestKey("cfg.v1", "after")
	certificate, err := CheckCFGPreservation(beforeKey, before, afterKey, after, orderedAnalysisAspects...)
	if err != nil {
		t.Fatal(err)
	}
	if certificate.Before() != beforeKey || certificate.After() != afterKey || certificate.BeforeFingerprint() == certificate.AfterFingerprint() || certificate.CheckerRevision() == "" {
		t.Fatalf("certificate provenance = before %s/%s after %s/%s checker %q", certificate.Before(), certificate.BeforeFingerprint(), certificate.After(), certificate.AfterFingerprint(), certificate.CheckerRevision())
	}
	for _, check := range certificate.Checks() {
		if !check.Preserved {
			t.Fatalf("source-only change affected %s", check.Aspect)
		}
	}

	mutated := certificate
	mutated.checks = append([]PreservationCheck(nil), certificate.checks...)
	mutated.checks[0].Preserved = false
	if mutated.Preserves(LoopStructureAnalysisRequirements()) {
		t.Fatal("mutated certificate admitted reuse")
	}
	if _, err := CheckCFGPreservation(opt.ArtifactKey{Kind: opt.ArtifactCandidate, Name: "not-ir", Version: "v"}, before, afterKey, after, AspectCFGTopology); err == nil || !strings.Contains(err.Error(), "not an exact IR identity") {
		t.Fatalf("non-IR identity was admitted: %v", err)
	}
	if _, err := CheckCFGPreservation(beforeKey, before, afterKey, after, AspectCFGTopology, AspectCFGTopology); err == nil || !strings.Contains(err.Error(), "repeated") {
		t.Fatalf("duplicate aspect was admitted: %v", err)
	}
}

func TestMemoryEffectAspectTreatsUnknownOperationsAsObservable(t *testing.T) {
	before := licmTestCFG()
	before.Blocks[2].Operations[1].Code = "extension.before"
	after := before
	after.Blocks = append([]Block(nil), before.Blocks...)
	after.Blocks[2].Operations = append([]Operation(nil), before.Blocks[2].Operations...)
	after.Blocks[2].Operations[1].Code = "extension.after"
	certificate, err := CheckCFGPreservation(
		aspectTestKey("cfg.v0", "unknown-before"), before,
		aspectTestKey("cfg.v1", "unknown-after"), after,
		AspectMemoryEffects,
	)
	if err != nil {
		t.Fatal(err)
	}
	checks := certificate.Checks()
	if len(checks) != 1 || checks[0].Preserved {
		t.Fatalf("unknown operation change preserved conservative effect trace: %+v", checks)
	}
}

func TestCallAuthorityIdentityIsAnOperationAndMemoryEffectAspect(t *testing.T) {
	before := CFG{Name: "call-authority", Entry: 0, Results: []Type{"u32"}, Blocks: []Block{{
		ID: 0, Operations: []Operation{{
			Code: OpCall, Results: []Value{{ID: 1, Type: "u32"}}, Effects: []Effect{EffectCall},
			Attributes: []Attribute{{Name: AttributeCallee, Value: "pure"}}, MemoryCallID: "summary-a",
		}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}},
	}}}
	after := cloneCFG(before)
	after.Blocks[0].Operations[0].MemoryCallID = "summary-b"
	certificate, err := CheckCFGPreservation(
		aspectTestKey("cfg.v0", "call-a"), before,
		aspectTestKey("cfg.v1", "call-b"), after,
		AspectOperationSemantics, AspectMemoryEffects,
	)
	if err != nil {
		t.Fatal(err)
	}
	for _, check := range certificate.Checks() {
		if check.Preserved {
			t.Fatalf("%s ignored changed call authority ID: %+v", check.Aspect, certificate.Checks())
		}
	}
}

func TestGVNDCECertificatePreservesTopologyAndEffectTraceOnlyWhenChecked(t *testing.T) {
	before := CFG{
		Name:    "cleanup_preservation",
		Entry:   0,
		Results: []Type{"u32"},
		Blocks: []Block{{
			ID: 0,
			Operations: []Operation{
				integerConstant(1, "u32", "7"),
				integerConstant(2, "u32", "7"),
				cseTestAdd(3, 1, 1),
				cseTestAdd(4, 2, 2),
				{Code: OpCall, Results: []Value{cseTestValue(5, "u32")}, Operands: []ValueID{3}, Effects: []Effect{EffectCall}, Attributes: []Attribute{{Name: AttributeCallee, Value: "observe"}}},
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4}},
		}},
	}
	after, _, err := SimplifyGVNDCE(before)
	if err != nil {
		t.Fatal(err)
	}
	certificate, err := CheckCFGPreservation(aspectTestKey("cfg.v0", "a"), before, aspectTestKey("cfg.v1", "b"), after, orderedAnalysisAspects...)
	if err != nil {
		t.Fatal(err)
	}
	preserved := map[AnalysisAspect]bool{}
	for _, check := range certificate.Checks() {
		preserved[check.Aspect] = check.Preserved
	}
	if !preserved[AspectCFGTopology] || !preserved[AspectMemoryEffects] || !preserved[AspectLayout] {
		t.Fatalf("cleanup preservation = %+v", certificate.Checks())
	}
	if preserved[AspectSSAIdentity] || preserved[AspectOperationSemantics] || preserved[AspectTypes] {
		t.Fatalf("cleanup overstated preservation = %+v", certificate.Checks())
	}
}
