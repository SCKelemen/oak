package asm

import (
	"bytes"
	"context"
	"crypto/sha256"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

const sailSTRExecutionName = "memory_single_general_immediate_signed_postidx"

func auditSTRExecutionVectorPrelude(raw, compat string) error {
	const originalHash = "73855de7cdfbef3cc5ba22b64478d1ae031ad56fdc80a4dedc8fdfbb4db1218b"
	if got := fmt.Sprintf("%x", sha256.Sum256([]byte(raw))); got != originalHash {
		return fmt.Errorf("original vector prelude hash = %s, want %s", got, originalHash)
	}
	const original = "val signed = pure"
	if strings.Count(raw, original) != 1 {
		return fmt.Errorf("original signed declaration is not unique")
	}
	if compat != strings.Replace(raw, original, "val oak_signed_compat = pure", 1) {
		return fmt.Errorf("compatibility prelude changed beyond the unused signed declaration's name")
	}
	return nil
}

func TestSailSTRExecutionPreludeExactAndMutated(t *testing.T) {
	data, err := os.ReadFile(filepath.Join("..", "spec", "sail", "str_execution_vector.sail"))
	if err != nil {
		t.Fatal(err)
	}
	compat := string(data)
	raw := strings.Replace(compat, "val oak_signed_compat = pure", "val signed = pure", 1)
	if err := auditSTRExecutionVectorPrelude(raw, compat); err != nil {
		t.Fatal(err)
	}
	for name, mutant := range map[string]string{
		"missing_rename": raw,
		"wrong_name":     strings.Replace(compat, "oak_signed_compat", "unsigned", 1),
		"impure":         strings.Replace(compat, "val oak_signed_compat = pure", "val oak_signed_compat = impure", 1),
		"extra_content":  compat + "\nval extra : unit -> unit\n",
	} {
		t.Run(name, func(t *testing.T) {
			if err := auditSTRExecutionVectorPrelude(raw, mutant); err == nil {
				t.Fatal("changed compatibility prelude was admitted")
			}
		})
	}
	if err := auditSTRExecutionVectorPrelude(raw+"\n", compat); err == nil {
		t.Fatal("changed original prelude was admitted")
	}
}

// Independently reconstruct the only permitted edits to raw Sail output.
// Namespace/import/runtime-open framing and one explicit callback binder may change;
// neither the instruction body nor the generated register helpers may change.
// This is a source-fidelity check, not a correctness proof of Sail's backend.
func auditSTRExecutionLeanFraming(rawDefs, rawFunctions, defs, functions string) error {
	replace := func(source, from, to string) (string, error) {
		if count := strings.Count(source, from); count != 1 {
			return "", fmt.Errorf("Lean frame %q count = %d, want 1", from, count)
		}
		return strings.Replace(source, from, to, 1), nil
	}
	expectedDefs, err := replace(rawDefs, "import Sail\n", "import Sail\n\nnamespace STRExecution\n")
	if err != nil {
		return err
	}
	expectedDefs += "\nend STRExecution\n"
	if defs != expectedDefs {
		return fmt.Errorf("generated STR definitions changed beyond their namespace frame")
	}
	expected := rawFunctions
	for _, edit := range [][2]string{
		{"import Out.Defs\nimport Out.Specialization\nimport Out.FakeReal\n", "import STRExecution.Defs\nimport STRExecution.Interface\n"},
		{"namespace Out.Functions", "namespace STRExecution.Functions\n\nopen PreSail"},
		{"end Out.Functions", "end STRExecution.Functions"},
		{"def " + sailSTRExecutionName + " ", "def " + sailSTRExecutionName + " (boundaries : Boundaries) "},
	} {
		expected, err = replace(expected, edit[0], edit[1])
		if err != nil {
			return err
		}
	}
	if functions != expected {
		return fmt.Errorf("generated STR functions changed beyond imports, namespace/runtime open, and callback binder")
	}
	return nil
}

func TestSailSTRExecutionLeanFramingExactAndMutated(t *testing.T) {
	const rawDefs = "import Sail\ninductive Register where | _R\n"
	const defs = "import Sail\n\nnamespace STRExecution\ninductive Register where | _R\n\nend STRExecution\n"
	const raw = "import Sail\nimport Out.Defs\nimport Out.Specialization\nimport Out.FakeReal\n" +
		"namespace Out.Functions\ndef " + sailSTRExecutionName + " (n : Nat) : SailM Unit := do\n" +
		"  boundaries.check n\n  boundaries.store n\nend Out.Functions\n"
	const framed = "import Sail\nimport STRExecution.Defs\nimport STRExecution.Interface\n" +
		"namespace STRExecution.Functions\n\nopen PreSail\ndef " + sailSTRExecutionName + " (boundaries : Boundaries) (n : Nat) : SailM Unit := do\n" +
		"  boundaries.check n\n  boundaries.store n\nend STRExecution.Functions\n"
	if err := auditSTRExecutionLeanFraming(rawDefs, raw, defs, framed); err != nil {
		t.Fatal(err)
	}
	for name, mutant := range map[string]string{
		"erased_check":     strings.Replace(framed, "  boundaries.check n\n", "", 1),
		"success_stub":     strings.Replace(framed, "boundaries.store n", "pure ()", 1),
		"different_index":  strings.Replace(framed, "boundaries.store n", "boundaries.store 0", 1),
		"post_mem_effect":  strings.Replace(framed, "end STRExecution.Functions", "  boundaries.check n\nend STRExecution.Functions", 1),
		"missing_binder":   strings.Replace(framed, " (boundaries : Boundaries)", "", 1),
		"different_import": strings.Replace(framed, "import Sail", "import FakeRuntime", 1),
		"extra_definition": framed + "def extra := true\n",
	} {
		t.Run(name, func(t *testing.T) {
			if err := auditSTRExecutionLeanFraming(rawDefs, raw, defs, mutant); err == nil {
				t.Fatal("changed generated instruction was admitted")
			}
		})
	}
	for _, mutant := range []struct{ defs, rawDefs, raw string }{
		{strings.Replace(defs, "_R", "other", 1), rawDefs, raw},
		{defs, rawDefs + "import Sail\n", raw},
		{defs, rawDefs, raw + "def " + sailSTRExecutionName + " (n : Nat) := n\n"},
	} {
		if err := auditSTRExecutionLeanFraming(mutant.rawDefs, mutant.raw, mutant.defs, framed); err == nil {
			t.Fatal("changed definitions or ambiguous transformation marker was admitted")
		}
	}
}

func TestSailSTRExecutionGenerationCurrent(t *testing.T) {
	sail, err := exec.LookPath("sail")
	if err != nil {
		home, err := os.UserHomeDir()
		if err != nil {
			t.Fatal(err)
		}
		sail = filepath.Join(home, ".opam", "default", "bin", "sail")
		if _, err := os.Stat(sail); err != nil {
			requireOracle(t, "Sail unavailable for original STR generation")
		}
	}
	goTool, err := exec.LookPath("go")
	if err != nil {
		requireOracle(t, "Go unavailable for original STR generator")
	}
	root, err := filepath.Abs(filepath.Join("..", "spec", "sail"))
	if err != nil {
		t.Fatal(err)
	}
	for _, file := range []string{"aarch64.sail", "aarch_types.sail", "aarch_mem.sail", "prelude.sail"} {
		if _, err := os.Stat(filepath.Join(filepath.Dir(sailArmModel), file)); err != nil {
			requireOracle(t, "pinned Arm STR source unavailable: "+err.Error())
		}
	}
	out := t.TempDir()
	ctx, cancel := context.WithTimeout(context.Background(), 3*time.Minute)
	defer cancel()
	cmd := exec.CommandContext(ctx, goTool, "run", filepath.Join(root, "str_execution_regen.go"),
		"--sail", sail, "--output-dir", out)
	cmd.Dir = out
	cmd.WaitDelay = 5 * time.Second
	if log, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("original STR generation failed: %v (context: %v)\n%s", err, ctx.Err(), log)
	}
	read := func(root, name string) []byte {
		t.Helper()
		data, err := os.ReadFile(filepath.Join(root, name))
		if err != nil {
			t.Fatal(err)
		}
		return data
	}
	for _, name := range []string{"str_execution.sail", "str_execution_vector.sail", "lean/STRExecution/Defs.lean", "lean/STRExecution/Generated.lean"} {
		if !bytes.Equal(read(out, name), read(root, name)) {
			t.Errorf("%s differs from the pinned generator; run spec/sail/str_execution_regen.go", name)
		}
	}
	if err := auditSTRExecutionVectorPrelude(string(read(out, "raw/vector.sail")),
		string(read(root, "str_execution_vector.sail"))); err != nil {
		t.Fatal(err)
	}
	if err := auditSTRExecutionLeanFraming(
		string(read(out, "raw/Out/Defs.lean")), string(read(out, "raw/Out.lean")),
		string(read(root, "lean/STRExecution/Defs.lean")), string(read(root, "lean/STRExecution/Generated.lean"))); err != nil {
		t.Fatal(err)
	}
}
