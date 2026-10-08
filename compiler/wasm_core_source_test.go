package compiler

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
	"time"
)

// This regression instantiates the reviewed hand-transcribed Core theorem on
// actual original source and compiler-emitted modules. It does not establish
// an importer/production-compiler refinement or enable verified authority.
func TestWasmCoreSourceMatchesLean(t *testing.T) {
	lake := findLake()
	if lake == "" {
		if os.Getenv("OAK_REQUIRE_WASM_LEAN") == "1" {
			t.Fatal("required Wasm Core source correspondence needs lake")
		}
		t.Skip("lake unavailable")
	}
	root, err := filepath.Abs(filepath.Join("..", "spec", "lean"))
	if err != nil {
		t.Fatal(err)
	}
	run := func(args ...string) string {
		t.Helper()
		ctx, cancel := context.WithTimeout(t.Context(), 5*time.Minute)
		defer cancel()
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = root
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("lake %v: %v\n%s", args, err, out)
		}
		return string(out)
	}
	run("build", "Oak.WasmCoreSource")
	var proof strings.Builder
	proof.WriteString("import Oak.WasmCoreSource\nopen Oak Oak.BitwiseFunction Oak.WasmCoreModule\nset_option maxRecDepth 8192\n")
	var names []string
	for _, tc := range bitwiseModuleCases(t) {
		list := func(b []byte) string { return strings.Replace(wasmLeanArray(b), "#[", "[", 1) }
		fmt.Fprintf(&proof, "namespace ActualCore_%s\ndef original : List UInt8 := %s\ndef emitted : List UInt8 := %s\ndef claim : BitwiseSource.Decl := BitwiseSource.fixture .%s\n", tc.name, list([]byte(tc.source)), list(tc.bytes), tc.name)
		proof.WriteString(`theorem source_to_core (s : Store) (a b : BitVec 32) (fuel : Nat) :
    BitwiseSource.Grammar original claim ∧
    LoweringRefinement.evalX (BitwiseSourceLowering.toExpr claim)
      (BitwiseSourceLowering.inputs a b) (fun _ => 0) fuel = some (eval claim.op a b) ∧
    WasmCoreBinary.BinaryModule emitted (module claim.name claim.op) ∧
    ModuleOk (module claim.name claim.op) [closedType] ∧
    Instantiation s (module claim.name claim.op) (allocate s claim.name claim.op)
      (allocatedInstance s claim.name) [] ∧
    exportAddress (allocatedInstance s claim.name) claim.name = some s.functions.length ∧
    Invoke (allocate s claim.name claim.op) s.functions.length [a,b]
      (.call [a,b] (.function s.functions.length) closedType) ∧
    CallSteps (allocate s claim.name claim.op)
      (.call [a,b] (.function s.functions.length) closedType)
      (.result [eval claim.op a b]) ∧
    WasmCoreBitwiseProjection.NumericResult (WasmCoreBitwiseProjection.binop claim.op)
      a b (eval claim.op a b) ∧
    BitwiseModule.invokeModule claim.name emitted a b = .ok (eval claim.op a b) :=
  WasmCoreSource.source_to_core (by decide +kernel : BitwiseSource.accepts original claim .wasm .wasmLocals emitted = true) s a b fuel
`)
		name := "ActualCore_" + tc.name + ".source_to_core"
		names = append(names, name)
		fmt.Fprintf(&proof, "end ActualCore_%s\n#print axioms %s\n", tc.name, name)
		t.Logf("%s: bound %d original source bytes and %d emitted module bytes to all-input arbitrary-store Core derivation", tc.name, len(tc.source), len(tc.bytes))
	}
	path := filepath.Join(t.TempDir(), "ActualCoreSource.lean")
	if err := os.WriteFile(path, []byte(proof.String()), 0600); err != nil {
		t.Fatal(err)
	}
	out := run("env", "lean", path)
	rows := regexp.MustCompile(`(?s)'([^']+)' depends on axioms:\s*\[([^]]*)\]`).FindAllStringSubmatch(out, -1)
	seen := map[string]bool{}
	allowed := map[string]bool{"propext": true, "Classical.choice": true, "Quot.sound": true}
	for _, row := range rows {
		if seen[row[1]] {
			t.Fatalf("duplicate axiom report: %s", row[1])
		}
		seen[row[1]] = true
		for _, a := range strings.Split(row[2], ",") {
			a = strings.TrimSpace(a)
			if a != "" && !allowed[a] {
				t.Fatalf("unexpected axiom in %s: %s", row[1], a)
			}
		}
	}
	for _, name := range names {
		if !seen[name] {
			t.Fatalf("missing axiom report for %s:\n%s", name, out)
		}
	}
	t.Log("all three actual-source Core theorem closures passed the standard-logical-axiom allowlist")
}
