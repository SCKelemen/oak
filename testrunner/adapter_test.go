package testrunner

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/compiler"
)

func TestSimulationRejectsHiddenEffects(t *testing.T) {
	for name, hidden := range map[string]string{
		"unused-ffi":     `clock: (): c.UInt64 = c.extern("get_clock")`,
		"spoof-reporter": `testing_discard: (): () = c.extern("oak_test_host_discard")`,
		"unsafe":         `hidden: (): () { unsafe {} }`,
		"generic":        `hidden[T]: (x: T): T { arm64.isb(); x }`,
		"machine":        `hidden: (): () { arm64.wfe() }`,
		"atomic-storage": `cell: Atomic[u32]`,
		"atomic-call":    `hidden: (): () { atomic_fence_seq_cst() }`,
	} {
		t.Run(name, func(t *testing.T) {
			_, err := compiler.New().WithSimulation(nil).WithSource("hidden.oak", hidden+"\nSimSafe: (data: []u8): () {}\n").EmitC().Get()
			if err == nil || !strings.Contains(err.Error(), "simulation boundary:") {
				t.Fatalf("hidden effect escaped boundary check: %v", err)
			}
		})
	}
}

func compileAdapterFixture(t *testing.T, dir, source string) string {
	t.Helper()
	if _, err := exec.LookPath("cc"); err != nil {
		t.Skip("requires cc")
	}
	cpath, object := filepath.Join(dir, "adapter.c"), filepath.Join(dir, "adapter.o")
	if err := os.WriteFile(cpath, []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	if out, err := exec.Command("cc", "-c", cpath, "-o", object).CombinedOutput(); err != nil {
		t.Fatalf("compile adapter: %v %s", err, out)
	}
	data, err := os.ReadFile(object)
	if err != nil {
		t.Fatal(err)
	}
	hash := sha256.Sum256(data)
	m := adapterManifest{Version: 1, Name: "fixture", Deterministic: true,
		Bindings: []compiler.SimulationBinding{{Name: "adapt", Symbol: "fixture_apply", Parameters: []string{"c.UInt32"}, Return: "c.UInt32"}},
		Objects:  []adapterObject{{Path: "adapter.o", SHA256: hex.EncodeToString(hash[:])}},
	}
	encoded, err := json.Marshal(m)
	if err != nil {
		t.Fatal(err)
	}
	manifest := filepath.Join(dir, "adapter.json")
	if err := os.WriteFile(manifest, encoded, 0600); err != nil {
		t.Fatal(err)
	}
	return manifest
}

func TestNativeAdapterReplayPinsImplementation(t *testing.T) {
	if runtime.GOOS == "darwin" {
		// The adapter contract admits self-contained archives and ELF
		// relocatable objects; Apple's toolchain produces Mach-O objects.
		t.Skip("native adapters require an ELF toolchain")
	}
	dir := fixture(t, map[string]string{"a_test.oak": `import(testing)
adapt: (x: c.UInt32): c.UInt32 = c.extern("fixture_apply")
SimNative: (data: []u8): () {
  state: [1]TestChoices
  choices: [*]TestChoices = span(&state)
  value: u32 = u32(test_byte(choices, data))
  test_check(u32(adapt(c.UInt32(value))) < u32(7), u32(7002))
}
`})
	manifest := compileAdapterFixture(t, dir, "#include <stdint.h>\nuint32_t fixture_apply(uint32_t x) { return x; }\n")
	code, results, stderr := runCLI(t, "-adapter", manifest, "-runs", "4", dir)
	if code != 1 || len(results) != 1 || results[0].Failure != "invariant:7002" {
		t.Fatalf("adapter: %d %+v %s", code, results, stderr)
	}
	artifact := results[0].Artifact
	code, results, stderr = runCLI(t, "-adapter", manifest, "-replay", artifact, dir)
	if code != 1 || results[0].Failure != "reproduced invariant:7002" {
		t.Fatalf("replay: %d %+v %s", code, results, stderr)
	}
	// A stale manifest fails before linking. A rebuilt, re-pinned manifest
	// passes validation but still cannot masquerade as the original build.
	object := filepath.Join(dir, "adapter.o")
	data, _ := os.ReadFile(object)
	os.WriteFile(object, append(data, 0), 0600)
	code, results, _ = runCLI(t, "-adapter", manifest, "-replay", artifact, dir)
	if code != 2 || !strings.Contains(results[0].Failure, "SHA-256 mismatch") {
		t.Fatalf("hash drift: %d %+v", code, results)
	}
	compileAdapterFixture(t, dir, "#include <stdint.h>\nuint32_t fixture_apply(uint32_t x) { return x + 1; }\n")
	code, results, _ = runCLI(t, "-adapter", manifest, "-replay", artifact, dir)
	if code != 2 || !strings.Contains(results[0].Failure, "build mismatch") {
		t.Fatalf("object drift: %d %+v", code, results)
	}
	code, results, _ = runCLI(t, "-runs", "1", dir)
	if code != 2 || !strings.Contains(results[0].Failure, "undeclared extern") {
		t.Fatalf("missing manifest: %d %+v", code, results)
	}
	path := filepath.Join(dir, "a_test.oak")
	source, _ := os.ReadFile(path)
	os.WriteFile(path, []byte(strings.Replace(string(source), "(x: c.UInt32): c.UInt32", "(x: c.UInt64): c.UInt32", 1)), 0600)
	code, results, _ = runCLI(t, "-adapter", manifest, "-runs", "1", dir)
	if code != 2 || !strings.Contains(results[0].Failure, "ABI mismatch") {
		t.Fatalf("ABI drift: %d %+v", code, results)
	}
}

func TestAdapterRejectsUnpinnedDependencies(t *testing.T) {
	dir := t.TempDir()
	manifest := compileAdapterFixture(t, dir, "#include <stdint.h>\nuint32_t fixture_apply(uint32_t x) { return x; }\n")
	for _, data := range [][]byte{[]byte("!<thin>\n"), []byte("INPUT(/tmp/outside.so)"), {127, 'E', 'L', 'F', 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0}} {
		raw, _ := os.ReadFile(manifest)
		var m adapterManifest
		json.Unmarshal(raw, &m)
		hash := sha256.Sum256(data)
		m.Objects[0].SHA256 = hex.EncodeToString(hash[:])
		encoded, _ := json.Marshal(m)
		os.WriteFile(manifest, encoded, 0600)
		os.WriteFile(filepath.Join(dir, "adapter.o"), data, 0600)
		if _, err := loadAdapter(manifest); err == nil || !strings.Contains(err.Error(), "self-contained") {
			t.Fatalf("untracked dependency accepted: %v", err)
		}
	}
}
