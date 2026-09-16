package lrat

import (
	"fmt"
	"strings"
	"testing"
)

const testFormula = "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n"
const testProof = "5 2 0 1 2 0\n5 d 1 2 0\n6 0 5 3 4 0\n"

func TestCheck(t *testing.T) {
	result, err := Check(testFormula, testProof)
	if err != nil {
		t.Fatal(err)
	}
	if result.Additions != 2 || result.Deletions != 2 {
		t.Fatalf("counted %+v, want 2 additions and 2 deletions", result)
	}
}

func TestCheckRefusesInvalidProofs(t *testing.T) {
	cases := map[string]struct{ proof, want string }{
		"no conflict":          {"5 2 0 1 0\n6 0 5 3 4 0\n", "reach no conflict"},
		"hint not unit":        {"5 0 1 0\n", "neither unit nor the conflict"},
		"dead hint":            {"5 2 0 1 2 0\n5 d 1 2 0\n6 0 5 1 2 0\n", "names no live clause"},
		"id does not increase": {"4 2 0 1 2 0\n", "does not increase"},
		"RAT hint":             {"5 2 0 -1 2 0\n", "RAT steps are not spoken"},
		"no empty clause":      {"5 2 0 1 2 0\n", "never derives the empty clause"},
		"undeclared variable":  {"5 3 0 1 2 0\n", "names no declared variable"},
		"satisfied hint":       {"5 -2 0 1 2 0\n", "already satisfied"},
		"malformed step":       {"5 2 1 2 0\n", "an addition is"},
	}
	for name, test := range cases {
		_, err := Check(testFormula, test.proof)
		if err == nil || !strings.Contains(err.Error(), test.want) {
			t.Errorf("%s: want an error mentioning %q, got %v", name, test.want, err)
		}
	}
}

func TestCheckWords(t *testing.T) {
	words := []uint32{
		Magic, 2, 4, 12, 19, 6, 9, 0,
		2, 1, 3,
		2, 0, 3,
		2, 1, 2,
		2, 0, 2,
		0, 5, 1, 3, 2, 1, 2,
		1, 5, 2, 1, 2,
		0, 6, 0, 3, 5, 3, 4,
	}
	result, err := CheckWords(words)
	if err != nil {
		t.Fatal(err)
	}
	if result.Additions != 2 || result.Deletions != 2 {
		t.Fatalf("counted %+v, want 2 additions and 2 deletions", result)
	}
	if _, err := CheckWords(words[:len(words)-1]); err == nil {
		t.Fatal("accepted a truncated word record")
	}
	unknown := append([]uint32(nil), words...)
	unknown[20] = 2
	if _, err := CheckWords(unknown); err == nil || !strings.Contains(err.Error(), "neither an addition") {
		t.Fatalf("unknown step kind: %v", err)
	}
}

func TestCheckRejectsMinIntLiteral(t *testing.T) {
	minInt := -int(^uint(0)>>1) - 1
	if _, _, err := ParseDIMACS(fmt.Sprintf("p cnf 1 1\n%d 0\n", minInt)); err == nil {
		t.Fatal("accepted MinInt as a declared literal")
	}
	if _, err := Check("p cnf 1 0\n", fmt.Sprintf("1 %d 0 0\n", minInt)); err == nil {
		t.Fatal("accepted MinInt in a certificate clause")
	}
}

func TestCheckLargeDeclaredDomainAndSparseID(t *testing.T) {
	maxInt := int(^uint(0) >> 1)
	formula := fmt.Sprintf("p cnf %d 1\n0\n", maxInt)
	if _, err := Check(formula, ""); err != nil {
		t.Fatalf("large unused declared domain: %v", err)
	}

	proof := fmt.Sprintf("%d 0 1 2 0\n", maxInt)
	result, err := Check("p cnf 1 2\n1 0\n-1 0\n", proof)
	if err != nil {
		t.Fatalf("sparse clause id: %v", err)
	}
	if result.Additions != 1 {
		t.Fatalf("sparse clause id counted %+v", result)
	}
}

func TestDenseDomainRequiresInputEvidenceAboveLimit(t *testing.T) {
	large := uint64(denseVariableLimit + 1)
	if useDenseLiteralDomain(large, 0) {
		t.Fatal("an unevidenced large declaration selected dense allocation")
	}
	if !useDenseLiteralDomain(large, large) {
		t.Fatal("an input-backed large declaration lost the dense fast path")
	}
}

func TestCheckWordsLargeDomainsAndSparseIDs(t *testing.T) {
	largeDomain := []uint32{Magic, ^uint32(0), 1, 1, 0, 1, 0, 0, 0}
	if _, err := CheckWords(largeDomain); err != nil {
		t.Fatalf("large unused word domain: %v", err)
	}

	words := []uint32{
		Magic, 1, 2, 4, 6, ^uint32(0), 2, 0,
		1, 1,
		1, 0,
		0, ^uint32(0), 0, 2, 1, 2,
	}
	result, err := CheckWords(words)
	if err != nil {
		t.Fatalf("sparse word clause id: %v", err)
	}
	if result.Additions != 1 {
		t.Fatalf("sparse word clause id counted %+v", result)
	}
}

func TestCheckWordsRefusesOverflowingRegions(t *testing.T) {
	max := ^uint32(0)
	cases := map[string][]uint32{
		"literal words": {Magic, 1, 0, max, 0, 0, 0, 0},
		"step words":    {Magic, 1, 0, 0, max, 0, 0, 0},
		"clause count":  {Magic, 1, max, 0, 0, 0, 0, 0},
		"clause length": {Magic, 1, 1, 1, 0, 1, 0, 0, max},
		"add literals":  {Magic, 1, 0, 0, 3, 1, 0, 0, 0, 1, max},
		"add hints":     {Magic, 1, 0, 0, 4, 1, 0, 0, 0, 1, 0, max},
		"delete ids":    {Magic, 1, 0, 0, 3, 1, 0, 0, 1, 1, max},
		"clause residue": {Magic, 0, 1, 2, 0, 1, 0, 0,
			0, 0},
	}
	for name, words := range cases {
		if _, err := CheckWords(words); err == nil {
			t.Errorf("%s: accepted malformed word bounds", name)
		}
	}

	valid := []uint32{Magic, 0, 1, 1, 0, 1, 0, 0, 0}
	withTrailing := append(append([]uint32(nil), valid...), 0)
	if _, err := CheckWords(withTrailing); err == nil {
		t.Fatal("accepted words beyond the declared step region")
	}
}
