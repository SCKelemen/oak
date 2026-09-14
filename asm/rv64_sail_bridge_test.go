package asm

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// The Oak ↔ Sail bridge (spec/lean-sail, docs/spec/94-assembler.md §9)
// restates the Oak.RiscV definitions it proves against the Sail model's
// Lean export. The restatement must not drift: every definition line
// inside the OAK-DEF block is required verbatim in spec/lean/Oak/RiscV.lean.
// When the export is generated and built (external/sail-riscv, not
// vendored), the bridge project itself is built too.
func TestRV64SailBridgeDefinitionsMatch(t *testing.T) {
	spec, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "RiscV.lean"))
	if err != nil {
		t.Fatal(err)
	}
	// RiscV.lean restates the semantics, Encoding.lean the encoder's table
	// and placement; both blocks must be the specification's lines.
	for _, name := range []string{"RiscV.lean", "Encoding.lean"} {
		bridge, err := os.ReadFile(filepath.Join("..", "spec", "lean-sail", "OakSailBridge", name))
		if err != nil {
			t.Fatal(err)
		}
		text := string(bridge)
		start, end := strings.Index(text, "-- OAK-DEF-BEGIN"), strings.Index(text, "-- OAK-DEF-END")
		if start < 0 || end < start {
			t.Fatalf("%s lacks its OAK-DEF block", name)
		}
		block := text[start:end]
		var checked int
		for _, line := range strings.Split(block, "\n") {
			trimmed := strings.TrimSpace(line)
			if trimmed == "" || strings.HasPrefix(trimmed, "--") || strings.HasPrefix(trimmed, "/--") || strings.HasPrefix(trimmed, "deriving") {
				continue
			}
			if !strings.Contains(string(spec), line) {
				t.Errorf("%s: bridge definition line drifted from spec/lean/Oak/RiscV.lean:\n%s", name, line)
			}
			checked++
		}
		if checked < 20 {
			t.Fatalf("%s: only %d definition lines checked; the OAK-DEF block looks truncated", name, checked)
		}
	}
}

func TestRV64SailBridgeBuilds(t *testing.T) {
	// The export's top-level module object marks a complete build; a
	// partial one (a build in progress) would make the bridge's lake
	// rebuild the dependency in place.
	export := filepath.Join("..", "external", "sail-riscv", "build", "model", "Lean_RV64D", ".lake", "build", "lib", "lean", "LeanRV64D.olean")
	if _, err := os.Stat(export); err != nil {
		requireOracle(t, "the Sail RISC-V Lean export is not built under external/sail-riscv (see spec/lean-sail/README.md)")
		return
	}
	lake, err := exec.LookPath("lake")
	if err != nil {
		requireOracle(t, "lake not present")
		return
	}
	cmd := exec.Command(lake, "build")
	cmd.Dir = filepath.Join("..", "spec", "lean-sail")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("lake build of the bridge: %v\n%s", err, out)
	}
}

// The bridge inside Oak's own Lean project (spec/lean/Oak/SailRiscVBridge.lean)
// restates the Sail Lean library's bit-vector primitives and the export's
// prelude helpers verbatim; when the library and the export are fetched
// under external/, every restated definition line must appear in them.
// shift_bits_right_arith is the one deliberate difference (the export's
// Int shift amount taken as the natural it is) and is excluded.
func TestRV64SailBridgeStubsMatchSail(t *testing.T) {
	bridge, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "SailRiscVBridge.lean"))
	if err != nil {
		t.Fatal(err)
	}
	export := filepath.Join("..", "external", "sail-riscv", "build", "model", "Lean_RV64D")
	// The support library's definitions moved between its modules across
	// releases (Sail.lean in v4, Common.lean in v5): every module counts.
	libraryFiles, _ := filepath.Glob(filepath.Join(export, ".lake", "packages", "Sail", "Sail", "*.lean"))
	var library []byte
	for _, path := range libraryFiles {
		text, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		library = append(append(library, text...), '\n')
	}
	prelude, preErr := os.ReadFile(filepath.Join(export, "LeanRV64D", "Prelude.lean"))
	defs, defErr := os.ReadFile(filepath.Join(export, "LeanRV64D", "Defs.lean"))
	if len(libraryFiles) == 0 || preErr != nil || defErr != nil {
		requireOracle(t, "the Sail Lean library and export are not fetched under external/sail-riscv")
		return
	}
	normalize := func(text string) string {
		return strings.Join(strings.Fields(text), " ")
	}
	// zero_extend lives in the export's Defs module, the rest in its Prelude.
	lib, pre := normalize(string(library)), normalize(string(prelude))+" "+normalize(string(defs))
	checked := 0
	for _, line := range strings.Split(string(bridge), "\n") {
		trimmed := strings.TrimSpace(line)
		if !strings.HasPrefix(trimmed, "def ") && !strings.HasPrefix(trimmed, "notation") {
			continue
		}
		if strings.Contains(trimmed, "shift_bits_right_arith") {
			continue
		}
		want := normalize(trimmed)
		if strings.Contains(lib, want) || strings.Contains(pre, want) {
			checked++
			continue
		}
		// Multi-line definitions in the sources: the header line suffices.
		if idx := strings.Index(want, " :="); idx > 0 && (strings.Contains(lib, want[:idx]) || strings.Contains(pre, want[:idx])) {
			checked++
			continue
		}
		t.Errorf("restated Sail definition not found verbatim in the library or export:\n%s", trimmed)
	}
	if checked < 12 {
		t.Fatalf("only %d restated definitions checked", checked)
	}
}
