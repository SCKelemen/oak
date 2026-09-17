package asm

import (
	"crypto/sha256"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

const sailStateLiftingHash = "bb53566d894b041a02d0c0dc054a14ed795f6358bb1acba94e33b1ed8ba0c7b2"
const sailStateMonadHash = "7f6b1572543ce6d5af0e34d67a7f39db365f13fc373e025650b9801733a59d24"

// The general liftState interpreter mentions the non-executable universal set.
// Keep the exact imports and the independent emitEventS/runTraceS definitions;
// do not replace Choose, add an interpreter, or change either replay function.
func sailStateReplayFragment(source []byte) (string, error) {
	if got := fmt.Sprintf("%x", sha256.Sum256(source)); got != sailStateLiftingHash {
		return "", fmt.Errorf("sail2_state_lifting.lem hash = %s, want %s", got, sailStateLiftingHash)
	}
	text := string(source)
	const lift = "val liftState :"
	const replay = "val emitEventS :"
	if strings.Count(text, lift) != 1 || strings.Count(text, replay) != 1 {
		return "", fmt.Errorf("state replay extraction markers must be unique")
	}
	start, end := strings.Index(text, lift), strings.Index(text, replay)
	if end <= start {
		return "", fmt.Errorf("state replay extraction markers out of order")
	}
	return text[:start] + text[end:], nil
}

func TestSailLemStateReplay(t *testing.T) {
	oracle := newSailLemOracle(t)
	fragment := checkedSailMemoryFragment(t, oracle)
	read := func(path string) []byte {
		t.Helper()
		contents, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		return contents
	}
	monad := read(filepath.Join(oracle.library, "sail2_state_monad.lem"))
	if got := fmt.Sprintf("%x", sha256.Sum256(monad)); got != sailStateMonadHash {
		t.Fatalf("sail2_state_monad.lem hash = %s, want %s", got, sailStateMonadHash)
	}
	lifting := read(filepath.Join(oracle.library, "sail2_state_lifting.lem"))
	replay, err := sailStateReplayFragment(lifting)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := sailStateReplayFragment(append(append([]byte(nil), lifting...), '\n')); err == nil {
		t.Fatal("changed upstream replay source was accepted")
	}
	promptHarness := read(filepath.Join("..", "spec", "sail", "lem", "write_memory_trace_test.ml"))
	stateHarness := read(filepath.Join("..", "spec", "sail", "lem", "state_replay_test.ml"))
	for _, tc := range []struct{ name, file, old, replacement string }{
		{name: "official"},
		{"unchecked_selector", "sail2_state_replay.lem", "if v' = v then Just s else Nothing)\n  | E_write_reg", "Just s)\n  | E_write_reg"},
		{"accept_false_ack", "sail2_state_replay.lem", "if success then Just (put_mem_bytes addr sz v B0 s) else Nothing", "Just (put_mem_bytes addr sz v B0 s)"},
		{"drop_bytes", "sail2_state_monad.lem", "List.foldl write_byte s.memstate a_v", "List.foldl write_byte s.memstate []"},
		{"preserve_tags", "sail2_state_monad.lem", "List.foldl write_tag s.tagstate addrs", "List.foldl write_tag s.tagstate []"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			files := map[string][]byte{
				"memory_effects.sail": []byte(fragment), "aarch64_extras.lem": oracle.armExtras,
				"sail2_state_monad.lem": monad, "sail2_state_replay.lem": []byte(replay),
				"write_memory_trace_test.ml": promptHarness, "state_replay_test.ml": stateHarness,
			}
			if tc.file != "" {
				original := string(files[tc.file])
				if strings.Count(original, tc.old) != 1 {
					t.Fatal("runtime mutation must replace exactly one occurrence")
				}
				files[tc.file] = []byte(strings.Replace(original, tc.old, tc.replacement, 1))
			}
			dir := t.TempDir()
			for name, contents := range files {
				if err := os.WriteFile(filepath.Join(dir, name), contents, 0600); err != nil {
					t.Fatal(err)
				}
			}
			for _, args := range [][]string{
				{oracle.sail, "memory_effects.sail", "--no-memo-z3", "--lem", "--lem-lib", "Aarch64_extras", "--lem-output-dir", dir, "-o", "oak_memory"},
				{oracle.lem, "-ocaml", "-lib", oracle.library, "-outdir", dir,
					filepath.Join(oracle.library, "sail2_string.lem"), filepath.Join(oracle.library, "sail2_undefined.lem"),
					"sail2_state_monad.lem", "sail2_state_replay.lem", "aarch64_extras.lem", "oak_memory_types.lem", "oak_memory.lem"},
				{oracle.ocamlfind, "ocamlopt", "-package", "libsail", "-linkpkg", "-open", "Libsail",
					"sail2_string.ml", "sail2_undefined.ml", "sail2_state_monad.ml", "sail2_state_replay.ml",
					"aarch64_extras.ml", "oak_memory_types.ml", "oak_memory.ml", "write_memory_trace_test.ml", "state_replay_test.ml", "-o", "state_replay_test"},
			} {
				out, err := oracle.run(t, dir, args[0], args[1:]...)
				if err != nil {
					t.Fatalf("state oracle must generate and build, including mutants: %v\n%s", err, out)
				}
			}
			out, err := oracle.run(t, dir, filepath.Join(dir, "state_replay_test"))
			const promptSuccess = "Arm Lem WriteMemory traces: 99 checks passed\n"
			if tc.file == "" {
				if err != nil || string(out) != promptSuccess+"Arm Lem state replay: 84 checks passed\n" {
					t.Fatalf("official state replay oracle: %v\n%s", err, out)
				}
				t.Log(strings.TrimSpace(string(out)))
			} else if err == nil || !strings.Contains(string(out), promptSuccess) || !strings.Contains(string(out), "State replay check failed:") {
				t.Fatalf("runtime mutant must pass prompt checks then fail a state assertion: %v\n%s", err, out)
			}
		})
	}
}
