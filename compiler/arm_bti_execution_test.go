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

// Pins production compiler/ELF bytes to the concrete BTI-enabled selected-decoder
// theorem. Prefetched-word dispatch, initial-state and parser/export boundaries remain.
func TestArmBTIEnabledCompilerBytes(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_ORACLES") == "1" {
			t.Fatal(err)
		}
		t.Skip("formal Sail lane requires Lean")
	}
	if os.Getenv("OAK_ARM_BTI_LIB") == "" {
		artifact := filepath.Join("..", "spec", "sail", "lean", ".lake", "build", "lib", "lean", "ReturnBTIExecution.olean")
		if _, err := os.Stat(artifact); err != nil {
			if os.Getenv("OAK_REQUIRE_ORACLES") == "1" {
				t.Fatalf("required BTI proof graph: %v", err)
			}
			t.Skip("formal Sail lane requires the built BTI proof graph")
		}
	}
	var proof strings.Builder
	proof.WriteString("import ReturnBTIExecution\nopen Oak.SailBridge ReturnExecution Sail PreSail Oak.AArch64BitwiseFunction\n")
	for _, tc := range []struct{ op, symbol string }{{"and", "&"}, {"or", "|"}, {"xor", "^"}} {
		original := fmt.Sprintf("mix: (a: u32, b: u32): u32 = a %s b\n", tc.symbol)
		code := sourceBitwiseFunctionBytes(t, original, "mix", target.ArchArm64)
		if len(code) != 8 {
			t.Fatalf("unexpected function extent: %x", code)
		}
		var values []string
		for _, b := range code {
			values = append(values, fmt.Sprint(b))
		}
		literal := "[" + strings.Join(values, ",") + "]"
		fmt.Fprintf(&proof, "theorem bytes_%s : functionBytes .%s = %s := by decide +kernel\n", tc.op, tc.op, literal)
		fmt.Fprintf(&proof, `theorem compiled_execution_%[1]s
 (scalar : ScalarBoundaries) (returns : Boundaries)
 (s : ReturnConfig.State) (ps : ProcState) (v : ReturnConfig.Values) (mv : ReturnMode.Values)
 (guarded compatible : Bool) (h : ReturnBTI.Context s ps v mv guarded compatible)
 (elMode : ReturnELMode.Ready s) (el : ps.EL = ReturnExecution.Functions.EL1)
 (tcr : s.regs.get? Register.TCR_EL1 = some 0#64)
 (bank : ExtendedScalar.Bank) (initialized : s.regs.get? Register._R = some bank) :
 (ReturnBTIExecution.executeBytes scalar returns %[2]s).run s =
 .ok () (ReturnBTIExecution.finalState .%[1]s s bank) := by
 rw [← bytes_%[1]s]
 exact ReturnBTIExecution.exact_bytes_return scalar returns s ps v mv guarded compatible h elMode el tcr bank initialized .%[1]s
#print axioms compiled_execution_%[1]s
`, tc.op, literal)
		mutated := append([]byte(nil), code...)
		mutated[0] ^= 1
		var bad []string
		for _, b := range mutated {
			bad = append(bad, fmt.Sprint(b))
		}
		fmt.Fprintf(&proof, "example : (functionBytes .%s) ≠ ([%s] : List UInt8) := by decide +kernel\n", tc.op, strings.Join(bad, ","))
		t.Logf("original source %q -> exact ARM bytes %x -> concrete BTI-enabled execution", original, code)
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
		matches := regexp.MustCompile(`'compiled_execution_(and|or|xor)' depends on axioms: \[([^]]*)\]`).FindAllStringSubmatch(string(output), -1)
		seen := map[string]bool{}
		for _, match := range matches {
			if seen[match[1]] {
				t.Fatalf("duplicate closure: %s", match[1])
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
		if len(seen) != 3 {
			t.Fatalf("missing compiler-BTI execution closure audit: %s", output)
		}
	}
}
