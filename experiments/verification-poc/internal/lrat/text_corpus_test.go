package lrat

import (
	"encoding/json"
	"fmt"
	"os"
	"testing"
)

type textCase struct {
	Name     string `json:"name"`
	CNF      string `json:"cnf"`
	Proof    string `json:"proof"`
	Expected bool   `json:"expected"`
}

func checkTextCorpus(t *testing.T, decoded []differentialCase) {
	t.Helper()
	cases := []textCase{}
	for _, c := range decoded {
		if c.Kind != "proof" {
			continue
		}
		cnf, proof := proofTexts(c)
		cases = append(cases, textCase{Name: c.Name, CNF: cnf, Proof: proof, Expected: c.Expected})
	}
	cnf := "p cnf 1 2\n1 0\n-1 0\n"
	proof := "3 0 1 2 0\n"
	add := func(name, formula, certificate string, expected bool) {
		cases = append(cases, textCase{Name: name, CNF: formula, Proof: certificate, Expected: expected})
	}
	add("comments-and-ascii-whitespace", "c formula\r\np\tcnf 1 2\r\n1\t0\r\n-1\v\f0\r\n", "c proof\r\n3\t0\t1\t2\t0\r\n", true)
	add("multiline-clause", "p cnf 2 3\n1\n0 -1\n2 0\n-2 0", "4 0 1 2 3 0", true)
	add("signed-and-leading-zero-integers", "p cnf +01 02\n+1 -0\n-1 +00\n", "03 +0 +1 +2 -0", true)
	add("initial-empty-proof", "p cnf 0 1\n0", "", true)
	add("initial-empty-invalid-suffix", "p cnf 0 1\n0", "garbage", false)
	add("empty-derived-then-deleted", cnf, proof+"3 d 3 0", true)
	add("high-deletion-stamp-does-not-advance-last", cnf, "99 d 0\n"+proof, true)
	for i, bad := range []string{
		"", "1 0", "p cnf 1", "p other 1 2\n1 0 -1 0", "p cnf -1 2\n1 0 -1 0",
		"p cnf 1 -2", "p cnf 1 2\n1 0 -1", "p cnf 1 1\n1 0 -1 0", "p cnf 1 3\n1 0 -1 0",
		"p cnf 1 2\n2 0 -2 0", "p cnf 1 2\n1 0 -1 0\np cnf 1 2", "p cnf 1 2\n1 0 -1 0\nx",
		"p cnf 2147483648 0", "p cnf 1 1\n-2147483648 0", "p cnf + 0", "p cnf 1 1\n1_0 0",
		"p cnf 1 1\n0x1 0", "p cnf 1 1\n1.0 0", "p cnf 1 1\n1e0 0",
	} {
		add(fmt.Sprintf("malformed-cnf-%d", i), bad, proof, false)
	}
	for i, bad := range []string{
		"", "3", "3 0", "3 0 0", "3 0 1 0", "3 0 1 2", "3 0 1 2 0 0", "3 0 1 2 0 garbage",
		"3 0 -1 2 0", "3 0 1 9 0", "3 0 1 2 2 0", "2 0 1 2 0", "-3 0 1 2 0", "2147483648 0 1 2 0",
		"3 2 0 1 2 0", "2 d 1 0\n3 0 1 2 0", "2 d 1 1 0\n" + proof, "2 d 0 0\n" + proof,
		"2 d 9 0\n" + proof, "2 d -1 0\n" + proof, "2 d 0x0\n" + proof,
		"2 d +0\n" + proof, "2 d -0\n" + proof, "2 d 00\n" + proof,
		proof + "4 0 -1 0", proof + "4 d 9 0", proof + "4 0 0", proof + "4 0 1 2 0 trailing",
	} {
		add(fmt.Sprintf("malformed-lrat-%d", i), cnf, bad, false)
	}
	accepted := 0
	for _, c := range cases {
		result, err := Check(c.CNF, c.Proof)
		actual := err == nil && result.Accepted
		if actual != c.Expected {
			t.Fatalf("%s: Go=%t expected=%t: %v", c.Name, actual, c.Expected, err)
		}
		if actual {
			accepted++
		}
	}
	t.Logf("text corpus: %d cases (%d accepted, %d rejected)", len(cases), accepted, len(cases)-accepted)
	if path := os.Getenv("OAK_LEAN_TEXT_CORPUS_OUT"); path != "" {
		data, err := json.Marshal(cases)
		if err != nil {
			t.Fatal(err)
		}
		if err = os.WriteFile(path, data, 0600); err != nil {
			t.Fatal(err)
		}
	}
}
