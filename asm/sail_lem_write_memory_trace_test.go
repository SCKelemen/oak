package asm

import (
	"crypto/sha256"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// Copy the contiguous, already source-audited memory declarations, not a
// restatement of their behavior. The complete fragment's unrelated FPAdd
// external has no Lem implementation. No effect or register is stubbed here.
func sailMemoryEffectFragment(source string) (string, error) {
	for _, audit := range []func(string) error{
		auditSailRAMWrapper, auditSailRegisterMemoryWrapper, auditSailNoDeviceWriteTrace,
	} {
		if err := audit(source); err != nil {
			return "", err
		}
	}
	active, err := stripSailComments(source)
	if err != nil {
		return "", err
	}
	const startMarker = `val ___WriteRAM = "write_ram"`
	if strings.Count(active, startMarker) != 1 {
		return "", fmt.Errorf("RAM external binding marker must occur exactly once")
	}
	start := strings.Index(active, startMarker)
	_, close, err := exactSailFunctionBodyAndClose(active, "__WriteMemory")
	if err != nil {
		return "", err
	}
	if close <= start {
		return "", fmt.Errorf("RAM declarations are not in source order")
	}
	fragment := "default Order dec\n$include <prelude.sail>\n\n" + source[start:close+1] + "\n"
	// Re-audit the actual standalone generator input, including the closing
	// brace and no-device trace boundary, not just its source of origin.
	for _, audit := range []func(string) error{
		auditSailRAMWrapper, auditSailRegisterMemoryWrapper, auditSailNoDeviceWriteTrace,
	} {
		if err := audit(fragment); err != nil {
			return "", err
		}
	}
	return fragment, nil
}

func TestSailMemoryEffectFragmentExactAndMutated(t *testing.T) {
	source, err := os.ReadFile(filepath.Join("..", "spec", "sail", "arm_primitives.sail"))
	if err != nil {
		t.Fatal(err)
	}
	fragment, err := sailMemoryEffectFragment(string(source))
	if err != nil {
		t.Fatal(err)
	}
	const prefix = "default Order dec\n$include <prelude.sail>\n\n"
	body := strings.TrimSuffix(strings.TrimPrefix(fragment, prefix), "\n")
	if !strings.HasPrefix(fragment, prefix) || !strings.Contains(string(source), body) ||
		strings.Count(body, "function ") != 3 || strings.Contains(body, "FPAdd") {
		t.Fatal("memory fragment must preserve the contiguous three-function source block")
	}
	// Comments preserve offsets but cannot contribute declarations or braces.
	commentedPrefix := "/* val ___WriteRAM = \"write_ram\" } */\n" + string(source)
	if got, err := sailMemoryEffectFragment(commentedPrefix); err != nil || got != fragment {
		t.Fatalf("inactive prefix changed extraction: %v", err)
	}
	for _, mutant := range []string{
		"/*\n" + string(source) + "\n*/",
		strings.Replace(string(source), "register __defaultRAM : bits(56)", "register __defaultRAM : bits(52)", 1),
		strings.Replace(string(source), "__WriteRAM(56, N, __defaultRAM, address, val_name);", "();", 1),
		string(source) + "\nfunction __WriteMemory (N, address, val_name) = { () }\n",
	} {
		if _, err := sailMemoryEffectFragment(mutant); err == nil {
			t.Fatal("changed memory declarations were extracted as the official fragment")
		}
	}
}

func TestSailLemWriteMemoryTraces(t *testing.T) {
	oracle := newSailLemOracle(t)
	version, err := oracle.run(t, "", oracle.sail, "--version")
	if err != nil || !strings.HasPrefix(string(version), "Sail 0.20.2 (") {
		t.Fatalf("write-memory export requires pinned Sail 0.20.2: %v\n%s", err, version)
	}
	// These support modules are imported by Sail's generated Lem but are not
	// shipped as compiled modules in libsail. Translate their original sources
	// as well, without empty stand-ins or hand-written OCaml replacements.
	for name, want := range map[string]string{
		"sail2_string.lem":    "b5c56f43bfa19f9454a4dc0123ab78672c1cfd21d9d700cde618fb065f7fc50b",
		"sail2_undefined.lem": "0f2ae38f0f3c68f0117c11976979c32627d61061e52db48259f3c5636d1b060e",
	} {
		contents, err := os.ReadFile(filepath.Join(oracle.library, name))
		if err != nil {
			t.Fatal(err)
		}
		if got := fmt.Sprintf("%x", sha256.Sum256(contents)); got != want {
			t.Fatalf("%s hash = %s, want %s", name, got, want)
		}
	}
	// Check the official sources too: a matching local fragment alone is not
	// evidence that these declarations still match the pinned Arm model.
	for _, input := range []struct {
		file  string
		audit func(string) error
	}{
		{"no_devices.sail", auditSailRAMWrapper},
		{"no_devices.sail", auditSailNoDeviceWriteTrace},
		{"aarch_mem.sail", auditSailRegisterMemoryWrapper},
	} {
		contents, err := os.ReadFile(filepath.Join(filepath.Dir(sailArmModel), input.file))
		if err != nil {
			requireOracle(t, "official memory source unavailable: "+err.Error())
		}
		if err := input.audit(string(contents)); err != nil {
			t.Fatal(err)
		}
	}
	source, err := os.ReadFile(filepath.Join("..", "spec", "sail", "arm_primitives.sail"))
	if err != nil {
		t.Fatal(err)
	}
	fragment, err := sailMemoryEffectFragment(string(source))
	if err != nil {
		t.Fatal(err)
	}
	harness, err := os.ReadFile(filepath.Join("..", "spec", "sail", "lem", "write_memory_trace_test.ml"))
	if err != nil {
		t.Fatal(err)
	}
	const write = "__WriteRAM(56, N, __defaultRAM, address, val_name);"
	for _, tc := range []sailMemoryMutation{
		{name: "official"},
		{"bypass_selector", write, "__WriteRAM(56, N, address, address, val_name);"},
		{"duplicate_write", write, write + "\n    " + write},
		{"wrong_address", write, "__WriteRAM(56, N, __defaultRAM, __defaultRAM, val_name);"},
		{"wrong_data", write, "__WriteRAM(56, N, __defaultRAM, address, not_vec(val_name));"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			input := fragment
			if tc.old != "" {
				if strings.Count(input, tc.old) != 1 {
					t.Fatal("mutation must change exactly one occurrence")
				}
				input = strings.Replace(input, tc.old, tc.replacement, 1)
			}
			dir := t.TempDir()
			for name, contents := range map[string][]byte{
				"memory_effects.sail": []byte(input), "aarch64_extras.lem": oracle.armExtras,
				"write_memory_trace_test.ml": harness,
			} {
				if err := os.WriteFile(filepath.Join(dir, name), contents, 0600); err != nil {
					t.Fatal(err)
				}
			}
			for _, args := range [][]string{
				{oracle.sail, "memory_effects.sail", "--no-memo-z3", "--lem", "--lem-lib", "Aarch64_extras", "--lem-output-dir", dir, "-o", "oak_memory"},
				{oracle.lem, "-ocaml", "-lib", oracle.library, "-outdir", dir,
					filepath.Join(oracle.library, "sail2_string.lem"), filepath.Join(oracle.library, "sail2_undefined.lem"),
					"aarch64_extras.lem", "oak_memory_types.lem", "oak_memory.lem"},
				{oracle.ocamlfind, "ocamlopt", "-package", "libsail", "-linkpkg", "-open", "Libsail",
					"sail2_string.ml", "sail2_undefined.ml", "aarch64_extras.ml", "oak_memory_types.ml", "oak_memory.ml", "write_memory_trace_test.ml", "-o", "write_memory_trace_test"},
			} {
				out, err := oracle.run(t, dir, args[0], args[1:]...)
				if err != nil {
					t.Fatalf("oracle must generate and build, including mutants: %v\n%s", err, out)
				}
			}
			out, err := oracle.run(t, dir, filepath.Join(dir, "write_memory_trace_test"))
			if tc.old == "" {
				if err != nil || strings.TrimSpace(string(out)) != "Arm Lem WriteMemory traces: 99 checks passed" {
					t.Fatalf("official wrapper trace oracle: %v\n%s", err, out)
				}
				t.Log(strings.TrimSpace(string(out)))
			} else if err == nil || !strings.Contains(string(out), "WriteMemory trace check failed:") {
				t.Fatalf("mutant must fail a trace assertion, not infrastructure: %v\n%s", err, out)
			}
		})
	}
}
