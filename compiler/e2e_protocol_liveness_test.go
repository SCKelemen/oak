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

// Declared fairness and liveness (docs/spec/112-protocols.md sections 1
// and 4): `fair step` / `strongly fair step` join the specification as
// WF/SF on the step's action, and `eventually target` / `eventually from
// -> target` become the `Liveness` property (`<>`, `~>`). The module and
// its generated configuration model-check as is when TLC is available.
func TestE2EProtocolLiveness(t *testing.T) {
	src := `
Quantum: protocol = {
  data { budget: u32 }
  init { budget: u32(2) }
  initial Running
  tick: Running -> Running when data.budget > u32(1) then { data.budget = data.budget - u32(1) }
  tick: Running -> Yielded when data.budget <= u32(1) then { data.budget = u32(2) }
  resume: Yielded -> Running
  signal(on: Bool): Running -> Running
  fair tick
  strongly fair resume
  fair signal
  eventually Yielded
  eventually Running -> Yielded
  eventually Yielded -> Running
  eventually Running -> data.budget == u32(1)
}

main: (): i32 = 0
`
	tree, err := New().WithSource("live.oak", src).Parse().Get()
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	decls := Protocols(tree)
	if len(decls) != 1 {
		t.Fatalf("protocols: %d", len(decls))
	}
	module, err := ProtocolTLAWithRecords(decls[0], "live.oak", RecordDeclarations(tree.Root))
	if err != nil {
		t.Fatalf("render: %v", err)
	}
	for _, want := range []string{
		"Spec == Init /\\ [][Next]_vars /\\ WF_vars(Tick) /\\ SF_vars(Resume) /\\ WF_vars(\\E on \\in On : Signal(on))",
		"Liveness ==\n    <>(state = \"Yielded\")\n    /\\ ((state = \"Running\") ~> (state = \"Yielded\"))\n    /\\ ((state = \"Yielded\") ~> (state = \"Running\"))\n    /\\ ((state = \"Running\") ~> (",
		"budget = 1",
	} {
		if !strings.Contains(module, want) {
			t.Errorf("module lacks %q:\n%s", want, module)
		}
	}
	cfg := ProtocolTLCConfig(decls[0])
	if cfg != "SPECIFICATION Spec\nINVARIANT TypeOK\nPROPERTY Liveness\nCONSTANTS\n    On = {TRUE, FALSE}\n" {
		t.Errorf("cfg:\n%s", cfg)
	}
	// The checker still accepts the program: the entries are the model
	// checker's and the projection into Oak reads neither.
	if _, err := New().WithSource("live.oak", src).EmitC().Get(); err != nil {
		t.Fatalf("compilation failed: %v", err)
	}

	// Shape errors: an unknown step, an unreached state, data without a
	// declaration.
	for _, bad := range []struct{ entry, want string }{
		{"fair nap", "fairness names step nap"},
		{"eventually Halted", "eventually names state Halted"},
		{"eventually Running -> Halted", "eventually names state Halted"},
	} {
		text := strings.Replace(src, "  fair tick\n", "  "+bad.entry+"\n", 1)
		_, err := New().WithSource("bad.oak", text).EmitC().Get()
		if err == nil || !strings.Contains(err.Error(), bad.want) {
			t.Errorf("%s: expected an error mentioning %q, got %v", bad.entry, bad.want, err)
		}
	}
	noData := "Blink: protocol = {\n  initial Off\n  on: Off -> On\n  off: On -> Off\n  eventually data.lit\n}\nmain: (): i32 = 0\n"
	if _, err := New().WithSource("nodata.oak", noData).EmitC().Get(); err == nil || !strings.Contains(err.Error(), "eventually refers to data") {
		t.Errorf("no data: got %v", err)
	}

	jar := os.Getenv("OAK_TLA2TOOLS_JAR")
	if _, err := exec.LookPath("java"); err != nil || jar == "" {
		t.Skip("set OAK_TLA2TOOLS_JAR (and have java) to model-check the generated module")
	}
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "Quantum.tla"), []byte(module), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, "Quantum.cfg"), []byte(cfg), 0o644); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
	defer cancel()
	cmd := exec.CommandContext(ctx, "java", "-cp", jar, "tlc2.TLC", "-deadlock", "Quantum.tla")
	cmd.Dir = dir
	out, err := cmd.CombinedOutput()
	if err != nil || !strings.Contains(string(out), "No error has been found") {
		t.Fatalf("TLC: %v\n%s", err, out)
	}
	// Without the fairness the liveness is not implied: TLC reports the
	// violation, so the declared assumptions are load-bearing.
	unfair := strings.Replace(module, " /\\ WF_vars(Tick)", "", 1)
	if err := os.WriteFile(filepath.Join(dir, "Quantum.tla"), []byte(unfair), 0o644); err != nil {
		t.Fatal(err)
	}
	cmd = exec.CommandContext(ctx, "java", "-cp", jar, "tlc2.TLC", "-deadlock", "Quantum.tla")
	cmd.Dir = dir
	out, _ = cmd.CombinedOutput()
	// TLC 2.19 says "Temporal properties were violated", later releases
	// name the property; both report the violation.
	if !strings.Contains(string(out), "Temporal propert") || !strings.Contains(string(out), "violated") {
		t.Fatalf("TLC without fairness should report the violation:\n%s", out)
	}
}
