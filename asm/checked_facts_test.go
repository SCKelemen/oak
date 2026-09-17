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

// A bound the checker derives from the machine code must not displace a
// stronger one the typechecker proved (docs/spec/94-assembler.md §7,
// checker.provenIndexBound). Found by measurement: giving a scaled table
// index a local bound stopped the proof from being read, and three
// binary searches kept a guard they had been eliding.
func TestProvenBoundSurvivesALocalFact(t *testing.T) {
	declaration := "lookup: (v: []u32, i: u32) -> u32"
	// The index is `i * 3`, so the checker derives a bound of its own from
	// the guard on i; the region holds only four elements, so that derived
	// bound does not admit the access and the proof must be consulted.
	body := "  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10, x11, x13\n  adrl x9, table\n  add x13, x9, #0\n  movz w10, #4\n  cmp w2, w10\n  b.hs short\n  movz w11, #3\n  mul w9, w2, w11\n  ldr w0, [x13, w9, uxtw #2]\n  ret\nshort:\n  mov w0, #0\n  ret"
	unit, errors := ParseUnit("proven.oakasm", declaration+" = {\n"+body+"\n}\n")
	if len(errors) != 0 {
		t.Fatal(errors)
	}
	signature, err := parseSignature(declaration)
	if err != nil {
		t.Fatal(err)
	}
	function := unit.Functions[0]
	function.Tables = map[string]Table{"table": {Size: 16, Elem: 4}}
	for index, item := range function.Items {
		instruction, ok := item.(Instruction)
		if !ok || instruction.Mnemonic != "ldr" {
			continue
		}
		instruction.CheckedFacts = []CheckedFactRef{{ID: "p", Kind: "index-in-extent", Container: "t", Operand: 1, Extent: 4}}
		function.Items[index] = instruction
	}
	// Without authority the derived bound is all there is, and it does not
	// reach: `i < 4` scaled by three admits ten elements of a four-element
	// region.
	if findings := Check(function, signature, nil); len(findings) == 0 {
		t.Fatalf("the derived bound alone must not admit the access")
	}
	authority := map[string]typechecker.IndexProof{"p": {
		ID: "p", Proposition: "index-in-extent", Container: "t", Extent: 4,
		Scope: "proven:1:1", Provenance: "checked", Witness: "Oak.Extents.scaledUnderBound",
	}}
	if findings := CheckWithFacts(function, signature, nil, authority); len(findings) != 0 {
		t.Fatalf("the proof must be read even though the checker holds a fact: %v", findings)
	}
}
