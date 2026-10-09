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

	"github.com/SCKelemen/oak/target"
)

// Pins unchanged original source and complete production compiler/ELF function
// bytes to the typed-source/concrete BTI-enabled execution theorem. Restricted
// grammar, prefetched dispatch, initialized context and export boundaries remain.
func TestArmBTIEnabledCompilerBytes(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_ORACLES") == "1" {
			t.Fatal(err)
		}
		t.Skip("formal Sail lane requires Lean")
	}
	if os.Getenv("OAK_ARM_BTI_LIB") == "" {
		artifact := filepath.Join("..", "spec", "sail", "lean", ".lake", "build", "lib", "lean", "ReturnBTISourceControls.olean")
		if _, err := os.Stat(artifact); err != nil {
			if os.Getenv("OAK_REQUIRE_ORACLES") == "1" {
				t.Fatalf("required BTI proof graph: %v", err)
			}
			t.Skip("formal Sail lane requires the built BTI proof graph")
		}
	}
	var proof strings.Builder
	proof.WriteString("import ReturnBTISourceControls\nopen Oak.SailBridge ReturnExecution Sail PreSail\nset_option maxRecDepth 8192\n")
	list := func(bytes []byte) string {
		values := make([]string, len(bytes))
		for i, b := range bytes {
			values[i] = fmt.Sprint(b)
		}
		return "[" + strings.Join(values, ",") + "]"
	}
	wanted := map[string]bool{}
	for _, tc := range []struct{ op, symbol string }{{"and", "&"}, {"or", "|"}, {"xor", "^"}} {
		original := fmt.Sprintf("mix: (a: u32, b: u32): u32 = a %s b\n", tc.symbol)
		code := sourceBitwiseFunctionBytes(t, original, "mix", target.ArchArm64)
		if len(code) != 8 {
			t.Fatalf("unexpected function extent: %x", code)
		}
		// The exact same original is compiled above and serialized here. Neither
		// a source hash nor reconstructed source/AST is accepted as its identity.
		fmt.Fprintf(&proof, "namespace ActualBTISource_%s\ndef source : List UInt8 := %s\ndef body : List UInt8 := %s\ndef claim : Oak.BitwiseSource.Decl := ⟨[109,105,120], [97], [98], .%s⟩\n", tc.op, list([]byte(original)), list(code), tc.op)
		proof.WriteString(`theorem admitted : ReturnBTISource.accepts source claim .arm64 .aapcs64U32 body = true := by decide +kernel
 theorem source_identity : source = Oak.BitwiseSource.render claim := by decide +kernel
 theorem body_identity : body = Oak.AArch64BitwiseFunction.functionBytes claim.op := by decide +kernel
 theorem compiled_source
  (scalar : ScalarBoundaries) (returns : Boundaries)
  (s : ReturnConfig.State) (ps : ProcState) (v : ReturnConfig.Values) (mv : ReturnMode.Values)
  (guarded compatible : Bool) (h : ReturnBTI.Context s ps v mv guarded compatible)
  (elMode : ReturnELMode.Ready s) (el : ps.EL = ReturnExecution.Functions.EL1)
  (tcr : s.regs.get? Register.TCR_EL1 = some 0#64)
  (bank : ExtendedScalar.Bank) (initialized : s.regs.get? Register._R = some bank)
  (left right : BitVec 32) (hleft : bank[0].extractLsb' 0 32 = left)
  (hright : bank[1].extractLsb' 0 32 = right) (fuel : Nat) :
  ReturnBTISource.Outcome source body claim scalar returns s bank left right fuel :=
  ReturnBTISource.accepted_source_execution admitted scalar returns s ps v mv guarded compatible h
   elMode el tcr bank initialized left right hleft hright fuel
 theorem compiled_initialized (scalar : ScalarBoundaries) (returns : Boundaries)
  (s : ReturnConfig.State) (ps : ProcState) (bank : ExtendedScalar.Bank)
  (left right upperLeft upperRight : BitVec 32) (guarded : Bool) (fuel : Nat) :
  ReturnBTISource.Outcome source body claim scalar returns
   (ReturnBTISourceControls.initial s ps bank left right upperLeft upperRight guarded)
   (ReturnBTISourceControls.inputBank bank left right upperLeft upperRight) left right fuel :=
  ReturnBTISourceControls.initialized_source_success admitted scalar returns s ps bank
   left right upperLeft upperRight guarded fuel
 theorem source_replay (changed : List UInt8) (different : changed ≠ source) :
  ReturnBTISource.accepts changed claim .arm64 .aapcs64U32 body = false :=
  ReturnBTISource.refuses_source_replay changed body claim .arm64 .aapcs64U32
   (by simpa [← source_identity] using different)
 theorem body_replay (changed : List UInt8) (different : changed ≠ body) :
  ReturnBTISource.accepts source claim .arm64 .aapcs64U32 changed = false :=
  ReturnBTISource.refuses_body_replay source changed claim .arm64 .aapcs64U32
   (by simpa [← body_identity] using different)
 theorem body_bit_mutations : ((List.range 8).all fun index => (List.range 8).all fun bit =>
  !(ReturnBTISource.accepts source claim .arm64 .aapcs64U32
   (body.set index (body.getD index 0 ^^^ UInt8.ofNat (2^bit))))) = true := by decide +kernel
 theorem body_extent :
  ReturnBTISource.accepts source claim .arm64 .aapcs64U32 body.dropLast = false ∧
  ReturnBTISource.accepts source claim .arm64 .aapcs64U32 (body ++ [0]) = false := by decide +kernel
`)
		otherSymbol := "&"
		if tc.symbol == "&" {
			otherSymbol = "|"
		}
		changedSources := []string{
			strings.Replace(original, "mix:", "other:", 1),
			fmt.Sprintf("mix: (b: u32, a: u32): u32 = b %s a\n", tc.symbol),
			strings.Replace(original, " "+tc.symbol+" ", " "+otherSymbol+" ", 1),
			strings.Replace(original, "a: u32", "a: u64", 1),
			strings.Replace(original, "): u32", "): u64", 1),
			strings.Replace(original, " = a ", " = b ", 1),
			strings.TrimSuffix(original, "\n") + "\r\n",
			original + "// comment\n",
			original + original,
		}
		for i, changed := range changedSources {
			fmt.Fprintf(&proof, "theorem changed_source_%d : ReturnBTISource.accepts %s claim .arm64 .aapcs64U32 body = false := by decide +kernel\n", i, list([]byte(changed)))
		}
		for _, name := range []string{"admitted", "source_identity", "body_identity", "compiled_source", "compiled_initialized", "source_replay", "body_replay", "body_bit_mutations", "body_extent"} {
			wanted["ActualBTISource_"+tc.op+"."+name] = true
			fmt.Fprintf(&proof, "#print axioms %s\n", name)
		}
		for i := range changedSources {
			name := fmt.Sprintf("changed_source_%d", i)
			wanted["ActualBTISource_"+tc.op+"."+name] = true
			fmt.Fprintf(&proof, "#print axioms %s\n", name)
		}
		fmt.Fprintf(&proof, "end ActualBTISource_%s\n", tc.op)
		t.Logf("unchanged original source %q + complete ARM body %x -> typed source and concrete BTI-enabled execution", original, code)
	}
	path := filepath.Join(t.TempDir(), "CompilerBTIEnabled.lean")
	if err := os.WriteFile(path, []byte(proof.String()), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 60*time.Second)
	defer cancel()
	cmd := exec.CommandContext(ctx, lake, "env", "lean", "-j1", "-M2560", path)
	cmd.Dir = filepath.Join("..", "spec", "sail", "lean")
	if library := os.Getenv("OAK_ARM_BTI_LIB"); library != "" {
		lean, err := exec.LookPath("lean")
		if err != nil {
			t.Fatal(err)
		}
		cmd = exec.CommandContext(ctx, lean, "-j1", "-M2560", path)
		cmd.Dir = filepath.Join("..", "spec", "sail", "lean")
		cmd.Env = append(os.Environ(), "LEAN_PATH="+library)
	}
	if output, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("compiler BTI execution pin: %v\n%s", err, output)
	} else {
		matches := regexp.MustCompile(`'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)`).FindAllStringSubmatch(string(output), -1)
		seen := map[string]bool{}
		for _, match := range matches {
			if seen[match[1]] || !wanted[match[1]] {
				t.Fatalf("unexpected/duplicate closure: %s", match[1])
			}
			seen[match[1]] = true
			for _, axiom := range strings.Split(match[2], ",") {
				switch strings.TrimSpace(axiom) {
				case "", "propext", "Classical.choice", "Quot.sound":
				default:
					t.Fatalf("unexpected proof authority: %s", axiom)
				}
			}
		}
		if len(seen) != len(wanted) {
			t.Fatalf("missing compiler-source-BTI execution closure audit: %s", output)
		}
	}
}
