package asm

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

func TestCheckedIndexFactsRequireIndependentAuthority(t *testing.T) {
	declaration := "read: (v: []u32, i: u32) -> u32"
	body := "  bind x0, w1 = v\n  bind w2 = i\n  cmp w1, #4\n  b.lo short\n  ldr w0, [x0, w2, uxtw #2]\n  ret\nshort:\n  mov w0, #0\n  ret"
	unit, errors := ParseUnit("facts.oakasm", declaration+" = {\n"+body+"\n}\n")
	if len(errors) != 0 {
		t.Fatal(errors)
	}
	signature, err := parseSignature(declaration)
	if err != nil {
		t.Fatal(err)
	}
	function := unit.Functions[0]
	for index, item := range function.Items {
		instruction, ok := item.(Instruction)
		if !ok || instruction.Mnemonic != "ldr" {
			continue
		}
		instruction.CheckedFacts = []CheckedFactRef{{ID: "p", Kind: "index-in-extent", Container: "v", Operand: 1, Extent: 4}}
		function.Items[index] = instruction
	}
	if findings := Check(function, signature, nil); !containsFinding(findings, "without a dominating index guard") {
		t.Fatalf("metadata without authority must not license access: %v", findings)
	}
	authority := map[string]typechecker.IndexProof{"p": {
		ID: "p", Proposition: "index-in-extent", Container: "v", Extent: 4,
		Scope: "facts:1:1", Provenance: "checked", Witness: "Oak.Extents.indexUnder",
	}}
	if findings := CheckWithFacts(function, signature, nil, authority); len(findings) != 0 {
		t.Fatalf("authorized exact use must pass: %v", findings)
	}

	for name, test := range map[string]struct {
		mutate func(*Instruction)
		want   string
	}{
		"unknown ID":      {func(instruction *Instruction) { instruction.CheckedFacts[0].ID = "unknown" }, "no typechecker authority"},
		"wrong container": {func(instruction *Instruction) { instruction.CheckedFacts[0].Container = "other" }, "maps container"},
		"wrong operand":   {func(instruction *Instruction) { instruction.CheckedFacts[0].Operand = 0 }, "without a dominating index guard"},
		"too large":       {func(instruction *Instruction) { instruction.CheckedFacts[0].Extent = 5 }, "machine region of 4"},
	} {
		t.Run(name, func(t *testing.T) {
			clone := *function
			clone.Items = append([]Item(nil), function.Items...)
			for index, item := range clone.Items {
				instruction, ok := item.(Instruction)
				if !ok || instruction.Mnemonic != "ldr" {
					continue
				}
				instruction.CheckedFacts = append([]CheckedFactRef(nil), instruction.CheckedFacts...)
				test.mutate(&instruction)
				clone.Items[index] = instruction
			}
			findings := strings.Join(CheckWithFacts(&clone, signature, nil, authority), "\n")
			if !strings.Contains(findings, test.want) {
				t.Fatalf("expected %q, got %s", test.want, findings)
			}
		})
	}
}

func containsFinding(findings []string, text string) bool {
	for _, finding := range findings {
		if strings.Contains(finding, text) {
			return true
		}
	}
	return false
}
