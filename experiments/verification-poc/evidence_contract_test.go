package main

import (
	"encoding/json"
	"strings"
	"testing"
)

// The evidence contract (roadmap step 4): every accepted verdict states what
// was established, under which assumptions, and through which trust path,
// and the LRAT verdict names the corpus-gated checker and the proof formats it
// refuses.
func TestEvidenceContract(t *testing.T) {
	for _, name := range []string{"enum", "counter", "wrap"} {
		m := fixture(t, name)
		cert, err := localProof(m)
		if err != nil {
			t.Fatal(err)
		}
		verdict, err := verify(m, cert)
		if err != nil {
			t.Fatal(err)
		}
		if !verdict.Accepted || verdict.Claim.Property == "" || verdict.Established == "" || len(verdict.Assumptions) == 0 || len(verdict.TrustPath) == 0 {
			t.Fatalf("%s: incomplete verdict %+v", name, verdict)
		}
		// The claim names the Oak declarations it is about, located in the
		// source it binds by hash and digest.
		claim := verdict.Claim
		if claim.Invariant.Name != m.Config.Invariant || claim.Invariant.Line == 0 || claim.Initial.Line == 0 || claim.Step.Line == 0 || claim.State.Name != m.Document.State || claim.State.Line == 0 {
			t.Fatalf("%s: claim does not locate its declarations: %+v", name, claim)
		}
		if len(claim.SourceHash) != 64 || claim.SemanticDigest != m.Digest || claim.Source != m.Config.Source {
			t.Fatalf("%s: claim does not bind its source: %+v", name, claim)
		}
		joined := strings.Join(verdict.TrustPath, " ")
		for _, want := range []string{"internal/lrat", "CertificateFile.check", "check_refines", "frontend/"} {
			if !strings.Contains(joined, want) {
				t.Fatalf("%s: trust path lacks %q: %v", name, want, verdict.TrustPath)
			}
		}
		if len(verdict.Unsupported) != 4 {
			t.Fatalf("%s: unsupported formats %v", name, verdict.Unsupported)
		}
		encoded, err := json.Marshal(verdict)
		if err != nil {
			t.Fatal(err)
		}
		for _, field := range []string{`"accepted":true`, `"claim"`, `"established"`, `"assumptions"`, `"trust_path"`, `"unsupported"`, `"details"`} {
			if !strings.Contains(string(encoded), field) {
				t.Fatalf("%s: JSON verdict lacks %s: %s", name, field, encoded)
			}
		}
	}
	m := fixture(t, "counter-broken")
	trace, err := findTrace(m)
	if err != nil {
		t.Fatal(err)
	}
	verdict, err := verify(m, trace)
	if err != nil {
		t.Fatal(err)
	}
	if verdict.Claim.Property != "reachable safety counterexample" || verdict.Details["states"] != len(trace.States) {
		t.Fatalf("trace verdict %+v", verdict)
	}
}
