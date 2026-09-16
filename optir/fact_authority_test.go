package optir

import (
	"reflect"
	"strings"
	"testing"
)

func TestCheckedFactAuthoritySurvivesProjectionSCCPAndGVNRemapping(t *testing.T) {
	record := CheckedFactRecord{
		ID: "proof-add", Name: "checked.type", ValueType: "u32", Provenance: "checked",
		Witness: "u32", Scope: "facts.oak:3:12", Dependencies: []string{"operand-types"},
	}
	authority, err := NewCheckedFactAuthority([]CheckedFactRecord{record})
	if err != nil {
		t.Fatal(err)
	}
	fact := Fact{
		ID: record.ID, Name: record.Name, Values: []ValueID{4}, Provenance: record.Provenance,
		Witness: record.Witness, Scope: record.Scope, Dependencies: append([]string(nil), record.Dependencies...),
	}
	function := Function{
		Name: "fact_gvn", Parameters: []Value{{ID: 1, Type: "u32"}}, Results: []Type{"u32"},
		Body: Region{Nodes: []Node{
			{Operation: &Operation{Code: OpConstInt, Results: []Value{{ID: 2, Type: "u32"}}, Attributes: []Attribute{{Name: AttributeValue, Value: "1"}}}},
			{Operation: &Operation{Code: OpIntAdd, Results: []Value{{ID: 3, Type: "u32"}}, Operands: []ValueID{1, 2}}},
			{Operation: &Operation{Code: OpIntAdd, Results: []Value{{ID: 4, Type: "u32"}}, Operands: []ValueID{1, 2}, Facts: []Fact{fact}}},
			{Operation: &Operation{Code: OpIntAdd, Results: []Value{{ID: 5, Type: "u32"}}, Operands: []ValueID{3, 4}}},
		}, Yield: []ValueID{5}},
	}
	if err := VerifyFunctionCheckedFacts(function, authority); err != nil {
		t.Fatalf("structured checked fact refused: %v", err)
	}
	cfg, err := Project(function)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyCFGCheckedFacts(cfg, authority); err != nil {
		t.Fatalf("projected checked fact refused: %v", err)
	}
	sccp, err := AnalyzeSCCP(cfg)
	if err != nil {
		t.Fatal(err)
	}
	sccpCFG, _, err := SimplifyWithSCCP(cfg, sccp)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyCFGCheckedFacts(sccpCFG, authority); err != nil {
		t.Fatalf("SCCP checked fact refused: %v", err)
	}
	cleaned, report, err := SimplifyGVNDCE(sccpCFG)
	if err != nil {
		t.Fatal(err)
	}
	if report.GVN.EliminatedOperations != 1 || !reflect.DeepEqual(report.GVN.Replacements, []ValueReplacement{{From: 4, To: 3}}) {
		t.Fatalf("GVN report = %+v", report.GVN)
	}
	if err := VerifyCFGCheckedFacts(cleaned, authority); err != nil {
		t.Fatalf("GVN-remapped checked fact refused: %v", err)
	}
	remapped, ok := findCheckedFact(cleaned, record.ID)
	if !ok || !reflect.DeepEqual(remapped.Values, []ValueID{3}) || remapped.Scope != record.Scope ||
		!reflect.DeepEqual(remapped.Dependencies, record.Dependencies) {
		t.Fatalf("checked fact did not survive GVN remapping: %+v, ok=%v", remapped, ok)
	}
}

func TestCheckedFactAuthorityRejectsStaleForgedAndAmbiguousFacts(t *testing.T) {
	record := CheckedFactRecord{
		ID: "proof", Name: "checked.type", ValueType: "u32", Provenance: "checked",
		Witness: "u32", Scope: "facts.oak:2:10", Dependencies: []string{"checked operands"},
	}
	authority, err := NewCheckedFactAuthority([]CheckedFactRecord{record})
	if err != nil {
		t.Fatal(err)
	}
	validFact := Fact{
		ID: record.ID, Name: record.Name, Values: []ValueID{2}, Provenance: record.Provenance,
		Witness: record.Witness, Scope: record.Scope, Dependencies: append([]string(nil), record.Dependencies...),
	}
	valid := CFG{
		Name: "fact_refusal", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{{ID: 0, Parameters: []Value{{ID: 1, Type: "u32"}}, Operations: []Operation{
			{Code: OpConstInt, Results: []Value{{ID: 2, Type: "u32"}}, Attributes: []Attribute{{Name: AttributeValue, Value: "1"}}, Facts: []Fact{validFact}},
		}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{2}}}},
	}
	if err := VerifyCFGCheckedFacts(valid, authority); err != nil {
		t.Fatal(err)
	}

	tests := []struct {
		name   string
		mutate func(*CFG)
		want   string
	}{
		{name: "stale id", mutate: func(cfg *CFG) { cfg.Blocks[0].Operations[0].Facts[0].ID = "old-proof" }, want: "stale or unknown"},
		{name: "forged scope", mutate: func(cfg *CFG) { cfg.Blocks[0].Operations[0].Facts[0].Scope = "other:1:1" }, want: "does not match authority"},
		{name: "forged dependency", mutate: func(cfg *CFG) { cfg.Blocks[0].Operations[0].Facts[0].Dependencies[0] = "invented" }, want: "does not match authority"},
		{name: "wrong owner", mutate: func(cfg *CFG) { cfg.Blocks[0].Operations[0].Facts[0].Values[0] = 1 }, want: "not attached to its defining"},
		{name: "missing id", mutate: func(cfg *CFG) { cfg.Blocks[0].Operations[0].Facts[0].ID = "" }, want: "no authority ID"},
		{name: "ambiguous id", mutate: func(cfg *CFG) {
			cfg.Blocks[0].Operations = append(cfg.Blocks[0].Operations, Operation{
				Code: OpCopy, Results: []Value{{ID: 3, Type: "u32"}}, Operands: []ValueID{2},
				Facts: []Fact{{ID: record.ID, Name: record.Name, Values: []ValueID{3}, Provenance: record.Provenance, Witness: record.Witness, Scope: record.Scope, Dependencies: append([]string(nil), record.Dependencies...)}},
			})
			cfg.Blocks[0].Terminator.Values[0] = 3
		}, want: "attached more than once"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			candidate := cloneCFG(valid)
			test.mutate(&candidate)
			if err := VerifyCFGCheckedFacts(candidate, authority); err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("VerifyCFGCheckedFacts error = %v, want %q", err, test.want)
			}
		})
	}

	wrongType, err := NewCheckedFactAuthority([]CheckedFactRecord{{
		ID: record.ID, Name: record.Name, ValueType: "u64", Provenance: record.Provenance,
		Witness: record.Witness, Scope: record.Scope, Dependencies: record.Dependencies,
	}})
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyCFGCheckedFacts(valid, wrongType); err == nil || !strings.Contains(err.Error(), "authority requires u64") {
		t.Fatalf("wrong-type authority error = %v", err)
	}
	if err := VerifyCFGCheckedFacts(valid, CheckedFactAuthority{}); err == nil {
		t.Fatal("zero authority admitted a checked fact")
	}
	if _, err := NewCheckedFactAuthority([]CheckedFactRecord{record, record}); err == nil {
		t.Fatal("duplicate authority IDs were accepted")
	}
}

func TestCheckedFactAuthorityAndCFGFactFingerprintsCoverEveryField(t *testing.T) {
	record := CheckedFactRecord{
		ID: "proof", Name: "checked.type", ValueType: "u32", Provenance: "checked",
		Witness: "u32", Scope: "facts.oak:1:1", Dependencies: []string{"a", "b"},
	}
	authority, err := NewCheckedFactAuthority([]CheckedFactRecord{record})
	if err != nil {
		t.Fatal(err)
	}
	records := authority.Records()
	records[0].Scope = "mutated"
	records[0].Dependencies[0] = "mutated"
	if authority.Records()[0].Scope != record.Scope || authority.Records()[0].Dependencies[0] != "a" {
		t.Fatal("authority records alias returned inspection data")
	}
	changed := record
	changed.Scope = "facts.oak:1:2"
	other, err := NewCheckedFactAuthority([]CheckedFactRecord{changed})
	if err != nil {
		t.Fatal(err)
	}
	if authority.Fingerprint() == "" || authority.Fingerprint() == other.Fingerprint() {
		t.Fatalf("authority fingerprints = %q and %q", authority.Fingerprint(), other.Fingerprint())
	}

	cfg := CFG{Name: "fingerprint_fact", Entry: 0, Results: []Type{"u32"}, Blocks: []Block{{
		ID: 0, Operations: []Operation{{
			Code: OpConstInt, Results: []Value{{ID: 1, Type: "u32"}}, Attributes: []Attribute{{Name: AttributeValue, Value: "1"}},
			Facts: []Fact{{ID: record.ID, Name: record.Name, Values: []ValueID{1}, Provenance: record.Provenance, Witness: record.Witness, Scope: record.Scope, Dependencies: record.Dependencies}},
		}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}},
	}}}
	before := fingerprintCFG(cfg)
	cfg.Blocks[0].Operations[0].Facts[0].Dependencies = []string{"b", "a"}
	if after := fingerprintCFG(cfg); before == after {
		t.Fatal("ordered checked fact dependencies are absent from CFG fingerprint")
	}
}

func findCheckedFact(cfg CFG, id string) (Fact, bool) {
	for _, block := range cfg.Blocks {
		for _, operation := range block.Operations {
			for _, fact := range operation.Facts {
				if fact.ID == id {
					return fact, true
				}
			}
		}
	}
	return Fact{}, false
}
