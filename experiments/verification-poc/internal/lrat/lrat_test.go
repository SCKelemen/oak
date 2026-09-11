package lrat

import "testing"

func TestRejectMalformedProofs(t *testing.T) {
	cnf := "p cnf 1 2\n1 0\n-1 0\n"
	for _, proof := range []string{"3 0 1 2 0\n", "3 1 0 1 0\n3 d 1 0\n4 0 3 2 0\n"} {
		if _, e := Check(cnf, proof); e != nil {
			t.Fatal(e)
		}
	}
	for _, proof := range []string{"", "3 0 0", "3 0 1 0", "3 0 1 9 0", "3 0 -1 2 0", "2 0 1 2 0", "3 2 0 1 2 0", "2 d 1 0\n3 0 1 2 0", "3 0 1 2 2 0", "3 0 1 2 0\n4 1 0 -1 0"} {
		if _, e := Check(cnf, proof); e == nil {
			t.Fatalf("accepted corrupt proof %q", proof)
		}
	}
}
func TestDIMACSRejectsMalformedInputs(t *testing.T) {
	for _, text := range []string{"", "1 0", "p cnf 1 1\n1", "p cnf 1 1\n2 0", "p cnf 1 0\n1 0", "p cnf 1 0\np cnf 1 0", "p cnf -1 0", "p cnf 1 1\n99999999999999999999999999999 0"} {
		if _, e := Parse(text); e == nil {
			t.Fatalf("accepted invalid DIMACS %q", text)
		}
	}
}
func TestEmptyClauseAndTautology(t *testing.T) {
	if _, e := Check("p cnf 0 1\n0\n", ""); e != nil {
		t.Fatal(e)
	}
	if _, e := Check("p cnf 1 1\n1 -1 0\n", "2 0 1 0"); e == nil {
		t.Fatal("tautology cannot prove contradiction")
	}
	if _, e := Check("p cnf 1 0\n", "1 1 -1 0 0\n"); e == nil {
		t.Fatal("tautological addition is not empty clause")
	}
}
