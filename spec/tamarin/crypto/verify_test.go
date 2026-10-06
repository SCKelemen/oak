package main

import "testing"

func TestSummaryFailsClosed(t *testing.T) {
	want := map[string]string{"live": "verified", "negative": "falsified"}
	valid := "summary of summaries:\n live (exists-trace): verified (2 steps)\n negative (all-traces): falsified - found trace (3 steps)\n"
	if err := checkSummary(valid, want); err != nil {
		t.Fatal(err)
	}
	for _, bad := range []string{
		"live (exists-trace): verified\nnegative (all-traces): falsified",
		"summary of summaries:\n live (exists-trace): verified (2 steps)\n negative (all-traces): analysis incomplete (1 steps)\n",
		"summary of summaries:\n live (exists-trace): verified (2 steps)\n negative (all-traces): verified (3 steps)\n",
		valid + " extra (all-traces): verified (1 steps)\n",
		valid + " extra (all-traces): analysis incomplete (1 steps)\n",
		valid + " live (exists-trace): verified (2 steps)\n",
		valid + "summary of summaries:\n",
	} {
		if err := checkSummary(bad, want); err == nil {
			t.Errorf("accepted incomplete or incorrect evidence: %q", bad)
		}
	}
}
