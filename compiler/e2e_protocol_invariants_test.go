package compiler

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// Invariant theorems reach TLC (docs/spec/112-protocols.md section 4,
// docs/spec/125-verification.md section 2a): a theorem over a protocol's
// projected state and data whose body is in the invariant subset — a Bool
// expression, or the accumulator form of bounded loops — is stated in the
// model-checker module as Invariant_<name> and listed in the
// configuration, so TLC and `oak prove` check the same statement.
func TestProtocolInvariantTheoremsInModule(t *testing.T) {
	agree := `
agree: theorem (s: ReplState, d: ReplData) {
  ok: Bool = u32(d.replicas[u32(0)].len) <= u32(d.leader.len) && u32(d.replicas[u32(1)].len) <= u32(d.leader.len)
  i: u32 = 0
  while i < u32(2) {
    k: u32 = 0
    while k < u32(d.replicas[i].len) && k < u32(3) {
      ok = ok && d.replicas[i].log[k] == d.leader.log[k]
      k = k + u32(1)
    }
    i = i + u32(1)
  }
  ok
}
sealed_state: theorem (s: ReplState, d: ReplData) { s == .Normal || d.leader.len > u8(0) }
opaque: theorem (s: ReplState, d: ReplData) { helper(d) }
helper: (d: ReplData): Bool = true
main: (): i32 = 0
`
	tree, err := New().WithSource("repl.oak", replicaLogsSource+agree).Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	decl := Protocols(tree)[0]
	records := RecordDeclarations(tree.Root)
	theorems := InvariantTheorems(tree.Root, decl)
	if len(theorems) != 3 {
		t.Fatalf("theorems over the projection: %d", len(theorems))
	}
	module, err := ProtocolTLAFull(decl, "repl.oak", records, theorems)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"Invariant_agree ==\n    ((replicas[0].len <= leader.len) /\\ (replicas[1].len <= leader.len)) /\\ (\\A i \\in 0..1 : (\\A k \\in 0..2 : (k < replicas[i].len) => (replicas[i].log[k] = leader.log[k])))",
		"Invariant_sealed_state ==\n    ((state = \"Normal\") \\/ (leader.len > 0))",
		"\\* theorem opaque is outside the invariant subset (calls other than width conversions and count/all/any/none do not translate); `oak prove` decides it alone.",
	} {
		if !strings.Contains(module, want) {
			t.Fatalf("module lacks %q:\n%s", want, module)
		}
	}
	cfg := ProtocolTLCConfigFull(decl, records, theorems)
	if !strings.Contains(cfg, "INVARIANT TypeOK\nINVARIANT Invariant_agree\nINVARIANT Invariant_sealed_state\n") || strings.Contains(cfg, "opaque") {
		t.Fatalf("config:\n%s", cfg)
	}
	// The projection agrees with itself, invariants included; a module
	// stating a different invariant is reported at the invariant.
	self, err := ProtocolConformanceWith(decl, module, records, theorems)
	if err != nil {
		t.Fatal(err)
	}
	if !self.Conforms {
		t.Fatalf("self-conformance with invariants:\n%s", FormatTLAConformance(self))
	}
	edited := strings.Replace(module, "(leader.len > 0)", "(leader.len > 1)", 1)
	report, err := ProtocolConformanceWith(decl, edited, records, theorems)
	if err != nil {
		t.Fatal(err)
	}
	found := false
	for _, d := range report.Differences {
		found = found || d.Kind == "invariant"
	}
	if report.Conforms || !found {
		t.Fatalf("a changed invariant is an invariant difference:\n%s", FormatTLAConformance(report))
	}

	if _, _, reason := LocateTLC(); reason != "" {
		t.Skip(reason)
	}
	java, jar, _ := LocateTLC()
	run := func(module, cfg string) string {
		dir := t.TempDir()
		if err := os.WriteFile(filepath.Join(dir, "Repl.tla"), []byte(module), 0o644); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(dir, "Repl.cfg"), []byte(cfg), 0o644); err != nil {
			t.Fatal(err)
		}
		ctx, cancel := context.WithTimeout(context.Background(), 3*time.Minute)
		defer cancel()
		cmd := exec.CommandContext(ctx, java, "-cp", jar, "tlc2.TLC", "-deadlock", "-workers", "1", "Repl.tla")
		cmd.Dir = dir
		out, _ := cmd.CombinedOutput()
		return string(out)
	}
	// The theorems hold, TLC agrees.
	if out := run(module, cfg); !strings.Contains(out, "No error has been found") {
		t.Fatalf("TLC on the true invariants:\n%s", out)
	}
	// A false theorem is violated in TLC exactly as the prover refutes it.
	broken := strings.Replace(replicaLogsSource+agree, "sealed_state: theorem (s: ReplState, d: ReplData) { s == .Normal || d.leader.len > u8(0) }",
		"sealed_state: theorem (s: ReplState, d: ReplData) { d.replicas[u32(0)].len == d.leader.len }", 1)
	tree, err = New().WithSource("repl.oak", broken).Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	decl = Protocols(tree)[0]
	theorems = InvariantTheorems(tree.Root, decl)
	module, err = ProtocolTLAFull(decl, "repl.oak", records, theorems)
	if err != nil {
		t.Fatal(err)
	}
	if out := run(module, ProtocolTLCConfigFull(decl, records, theorems)); !strings.Contains(out, "Invariant Invariant_sealed_state is violated") {
		t.Fatalf("TLC on the false invariant:\n%s", out)
	}
}
