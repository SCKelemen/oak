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

// Independently specified semantic repairs, not imported from the generator.
// Every other byte of the raw function bodies must survive framing unchanged.
const strRawSyndromeCondition = `if ((((← readReg PSTATE).EL == EL0) || ((← readReg PSTATE).EL == EL1)) : Bool)`
const strGuardedSyndromeCondition = `if ((← do
    if ((← readReg PSTATE).EL == EL0) then pure true
    else pure ((← readReg PSTATE).EL == EL1)) : Bool)`
const strRawMemoryCondition = `if (((((← (memory.HaveNV2Ext ())) && (acctype == AccType_NV2REGISTER)) && ((BitVec.join1 [(BitVec.access
                 (← readReg SCTLR_EL2) 25)]) == 1#1)) || (← (memory.BigEndian ()))) : Bool)`
const strGuardedMemoryCondition = `if ((← do
      let nvEndian ← do
        if (← memory.HaveNV2Ext ()) then
          if (acctype == AccType_NV2REGISTER) then
            pure ((BitVec.join1 [(BitVec.access (← readReg SCTLR_EL2) 25)]) == 1#1)
          else pure false
        else pure false
      if nvEndian then pure true else memory.BigEndian ()) : Bool)`

const strRawArchVersionExpression = `(pure ((((((version == ARMv8p0) || ((version == ARMv8p1) && (← readReg __v81_implemented))) || ((version == ARMv8p2) && (← readReg __v82_implemented))) || ((version == ARMv8p3) && (← readReg __v83_implemented))) || ((version == ARMv8p4) && (← readReg __v84_implemented))) || ((version == ARMv8p5) && (← readReg __v85_implemented))))`
const strGuardedArchVersionExpression = `(do
    let through1 ← do
      if version == ARMv8p0 then pure true
      else if version == ARMv8p1 then readReg __v81_implemented else pure false
    let through2 ← do
      if through1 then pure true
      else if version == ARMv8p2 then readReg __v82_implemented else pure false
    let through3 ← do
      if through2 then pure true
      else if version == ARMv8p3 then readReg __v83_implemented else pure false
    let through4 ← do
      if through3 then pure true
      else if version == ARMv8p4 then readReg __v84_implemented else pure false
    if through4 then pure true
    else if version == ARMv8p5 then readReg __v85_implemented else pure false)`

func auditSTRExecutionRawBooleanCoverage(raw string) error {
	// The reviewed raw export contains exactly the three effectful Boolean
	// conditions above. A different export needs a fresh semantic audit.
	const reviewed = "232dab067cacb31824c8a2ac5a5f76435f7ecb5db9f7e328e5fb2626494ffb62"
	if got := fmt.Sprintf("%x", sha256.Sum256([]byte(raw))); got != reviewed {
		return fmt.Errorf("raw STR export changed: re-audit short-circuit sites (%s)", got)
	}
	return nil
}

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
// Namespace/import/runtime-open framing, explicit callback binders, and exactly
// three short-circuit repairs may change. This is not a general correctness proof
// of Sail's backend. The generation test also independently pins the whole raw
// output so new Boolean sites cannot silently evade the finite repair audit.
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
		{strRawSyndromeCondition, strGuardedSyndromeCondition},
		{strRawMemoryCondition, strGuardedMemoryCondition},
		{strRawArchVersionExpression, strGuardedArchVersionExpression},
		{"import Out.Defs\nimport Out.Specialization\nimport Out.FakeReal\n", "import STRExecution.Defs\nimport STRExecution.Interface\n"},
		{"namespace Out.Functions", "namespace STRExecution.Functions\n\nopen PreSail"},
		{"end Out.Functions", "end STRExecution.Functions"},
		{"def " + sailSTRExecutionName + " ", "def " + sailSTRExecutionName + " (boundaries : Boundaries) "},
		{"def aset_Mem ", "def aset_Mem (boundaries : Boundaries) (memory : MemoryBoundaries) "},
		{"def AArch64_aset_MemSingle ", "def AArch64_aset_MemSingle (boundaries : Boundaries) (memory : MemoryBoundaries) (single : MemSingleBoundaries) "},
	} {
		expected, err = replace(expected, edit[0], edit[1])
		if err != nil {
			return err
		}
	}
	if functions != expected {
		return fmt.Errorf("generated STR functions changed beyond framing and the three audited short-circuit repairs")
	}
	return nil
}

func TestSailSTRExecutionLeanFramingExactAndMutated(t *testing.T) {
	const rawDefs = "import Sail\ninductive Register where | _R\n"
	const defs = "import Sail\n\nnamespace STRExecution\ninductive Register where | _R\n\nend STRExecution\n"
	const raw = "import Sail\nimport Out.Defs\nimport Out.Specialization\nimport Out.FakeReal\n" +
		strRawSyndromeCondition + "\n" + strRawMemoryCondition + "\n" + strRawArchVersionExpression + "\n" +
		"namespace Out.Functions\ndef " + sailSTRExecutionName + " (n : Nat) : SailM Unit := do\n" +
		"  boundaries.check n\n  boundaries.store n\ndef aset_Mem (n : Nat) : SailM Unit := memory.store n\n" +
		"def AArch64_aset_MemSingle (n : Nat) : SailM Unit := single.store n\nend Out.Functions\n"
	const framed = "import Sail\nimport STRExecution.Defs\nimport STRExecution.Interface\n" +
		strGuardedSyndromeCondition + "\n" + strGuardedMemoryCondition + "\n" + strGuardedArchVersionExpression + "\n" +
		"namespace STRExecution.Functions\n\nopen PreSail\ndef " + sailSTRExecutionName + " (boundaries : Boundaries) (n : Nat) : SailM Unit := do\n" +
		"  boundaries.check n\n  boundaries.store n\ndef aset_Mem (boundaries : Boundaries) (memory : MemoryBoundaries) (n : Nat) : SailM Unit := memory.store n\n" +
		"def AArch64_aset_MemSingle (boundaries : Boundaries) (memory : MemoryBoundaries) (single : MemSingleBoundaries) (n : Nat) : SailM Unit := single.store n\nend STRExecution.Functions\n"
	if err := auditSTRExecutionLeanFraming(rawDefs, raw, defs, framed); err != nil {
		t.Fatal(err)
	}
	for name, mutant := range map[string]string{
		"erased_check":          strings.Replace(framed, "  boundaries.check n\n", "", 1),
		"success_stub":          strings.Replace(framed, "boundaries.store n", "pure ()", 1),
		"different_index":       strings.Replace(framed, "boundaries.store n", "boundaries.store 0", 1),
		"post_mem_effect":       strings.Replace(framed, "end STRExecution.Functions", "  boundaries.check n\nend STRExecution.Functions", 1),
		"missing_binder":        strings.Replace(framed, " (boundaries : Boundaries)", "", 1),
		"memory_stub":           strings.Replace(framed, "memory.store n", "pure ()", 1),
		"missing_memory_binder": strings.Replace(framed, " (memory : MemoryBoundaries)", "", 1),
		"missing_single_binder": strings.Replace(framed, " (single : MemSingleBoundaries)", "", 1),
		"single_stub":           strings.Replace(framed, "single.store n", "pure ()", 1),
		"eager_syndrome":        strings.Replace(framed, strGuardedSyndromeCondition, strRawSyndromeCondition, 1),
		"eager_memory":          strings.Replace(framed, strGuardedMemoryCondition, strRawMemoryCondition, 1),
		"eager_version":         strings.Replace(framed, strGuardedArchVersionExpression, strRawArchVersionExpression, 1),
		"wrong_version_flag":    strings.Replace(framed, "readReg __v84_implemented", "readReg __v85_implemented", 1),
		"skip_version_guard":    strings.Replace(framed, "if version == ARMv8p4", "if true", 1),
		"drop_version_read":     strings.Replace(framed, "readReg __v84_implemented", "pure true", 1),
		"drop_prior_or_result":  strings.Replace(framed, "if through3 then pure true", "if false then pure true", 1),
		"read_later_flag":       strings.Replace(framed, "if through4 then pure true", "if through4 then readReg __v85_implemented", 1),
		"skip_nv_query":         strings.Replace(framed, "if (← memory.HaveNV2Ext ())", "if false", 1),
		"skip_acctype_guard":    strings.Replace(framed, "if (acctype == AccType_NV2REGISTER)", "if true", 1),
		"wrong_sctlr_bit":       strings.Replace(framed, "(← readReg SCTLR_EL2) 25", "(← readReg SCTLR_EL2) 24", 1),
		"duplicate_endian":      strings.Replace(framed, "then pure true else memory.BigEndian ()", "then memory.BigEndian () else memory.BigEndian ()", 1),
		"skip_endian":           strings.Replace(framed, "else memory.BigEndian ()", "else pure false", 1),
		"wrong_syndrome_el":     strings.Replace(framed, "then pure true", "then pure false", 1),
		"different_import":      strings.Replace(framed, "import Sail", "import FakeRuntime", 1),
		"extra_definition":      framed + "def extra := true\n",
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
		{defs, rawDefs, raw + strRawMemoryCondition},
		{defs, rawDefs, raw + strRawArchVersionExpression},
		{defs, rawDefs, strings.Replace(raw, strRawSyndromeCondition, "true", 1)},
		{defs, rawDefs, strings.Replace(raw, strRawArchVersionExpression, "pure true", 1)},
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
	raw := string(read(out, "raw/Out.lean"))
	if err := auditSTRExecutionRawBooleanCoverage(raw); err != nil {
		t.Fatal(err)
	}
	for _, mutant := range []string{
		raw + "\ndef newEffect := do pure (false && (← memory.BigEndian ()))\n",
		strings.Replace(raw, strRawMemoryCondition, "if true", 1),
		strings.Replace(raw, strRawSyndromeCondition, strRawMemoryCondition, 1),
		strings.Replace(raw, strRawArchVersionExpression, "pure true", 1),
	} {
		if mutant == raw {
			t.Fatal("Boolean coverage mutation did not change raw output")
		}
		if err := auditSTRExecutionRawBooleanCoverage(mutant); err == nil {
			t.Fatal("unreviewed raw Boolean export admitted")
		}
	}
	if err := auditSTRExecutionLeanFraming(
		string(read(out, "raw/Out/Defs.lean")), raw,
		string(read(root, "lean/STRExecution/Defs.lean")), string(read(root, "lean/STRExecution/Generated.lean"))); err != nil {
		t.Fatal(err)
	}
}
