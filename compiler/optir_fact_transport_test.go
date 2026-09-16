package compiler

import (
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/optir"
)

func TestCheckedTypeFactSurvivesOptIRProjectionSCCPAndGVN(t *testing.T) {
	module, err := New().WithSource("optir_facts.oak", `common: (x: u32): u32 {
  left: u32 = x + u32(1)
  right: u32 = x + u32(1)
  left + right
}
main: (): i32 = 0
`).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	common, ok := optIRFunction(module, "common")
	if !ok {
		t.Fatalf("common was not projected: %+v", module.Refusals)
	}
	if common.CheckedFactsHash == "" || common.CheckedFactsHash != common.CheckedFacts.Fingerprint() {
		t.Fatalf("checked fact authority fingerprint = %q / %q", common.CheckedFactsHash, common.CheckedFacts.Fingerprint())
	}

	var sourceFact optir.Fact
	for _, node := range common.Structured.Body.Nodes {
		if node.Operation == nil || node.Operation.Code != optir.OpIntAdd || node.Operation.Source.Line != 3 {
			continue
		}
		if len(node.Operation.Facts) != 1 {
			t.Fatalf("right add checked facts = %#v", node.Operation.Facts)
		}
		sourceFact = node.Operation.Facts[0]
	}
	if sourceFact.ID == "" || sourceFact.Scope != "line 3:18" || sourceFact.Provenance != "checked" || sourceFact.Witness != "u32" || len(sourceFact.Values) != 1 {
		t.Fatalf("source checked fact = %+v", sourceFact)
	}
	if err := optir.VerifyFunctionCheckedFacts(common.Structured, common.CheckedFacts); err != nil {
		t.Fatalf("structured authority verification: %v", err)
	}
	for name, cfg := range map[string]optir.CFG{
		"projected": common.CFG,
		"SCCP":      common.SCCPSimplified,
		"GVN/DCE":   common.Simplified,
		"LICM":      common.LoopInvariant,
	} {
		if err := optir.VerifyCFGCheckedFacts(cfg, common.CheckedFacts); err != nil {
			t.Fatalf("%s authority verification: %v", name, err)
		}
	}
	sccpFact, ok := compilerFindOptIRFact(common.SCCPSimplified, sourceFact.ID)
	if !ok || !reflect.DeepEqual(sccpFact, sourceFact) {
		t.Fatalf("SCCP fact = %+v, ok=%v; want %+v", sccpFact, ok, sourceFact)
	}
	gvnFact, ok := compilerFindOptIRFact(common.Simplified, sourceFact.ID)
	if !ok || gvnFact.Values[0] == sourceFact.Values[0] || gvnFact.Scope != sourceFact.Scope || gvnFact.Provenance != sourceFact.Provenance || gvnFact.Witness != sourceFact.Witness {
		t.Fatalf("GVN-remapped fact = %+v, ok=%v; source %+v", gvnFact, ok, sourceFact)
	}
}

func TestCheckedTypeFactLoweringKeepsMultiNodeScalarFormsSupported(t *testing.T) {
	module, err := New().WithSource("optir_fact_forms.oak", `forms: (x: u8, flag: Bool): u32 {
  widened: u32 = u32(x)
  selected: u32 = (flag && true) ? { widened + u32(1) } | { widened }
  matched: u32 = flag ?
    | true -> selected
    | false -> widened
  matched
}
main: (): i32 = 0
`).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	forms, ok := optIRFunction(module, "forms")
	if !ok {
		t.Fatalf("multi-node scalar forms were refused: %+v", module.Refusals)
	}
	if err := optir.VerifyFunctionCheckedFacts(forms.Structured, forms.CheckedFacts); err != nil {
		t.Fatalf("multi-node structured facts: %v", err)
	}
	if err := optir.VerifyCFGCheckedFacts(forms.LoopInvariant, forms.CheckedFacts); err != nil {
		t.Fatalf("multi-node optimized facts: %v", err)
	}
}

func compilerFindOptIRFact(cfg optir.CFG, id string) (optir.Fact, bool) {
	for _, block := range cfg.Blocks {
		for _, operation := range block.Operations {
			for _, fact := range operation.Facts {
				if fact.ID == id {
					return fact, true
				}
			}
		}
	}
	return optir.Fact{}, false
}
