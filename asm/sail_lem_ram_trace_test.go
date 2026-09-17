package asm

import (
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

type sailLemOracle struct {
	lem, ocamlfind, sail, library string
	armExtras                     []byte
	run                           func(*testing.T, string, string, ...string) ([]byte, error)
}

// Both event oracles use the same source-pinned prompt runtime. In particular,
// do not silently substitute the sequential Lem backend for missing tools.
func newSailLemOracle(t *testing.T) sailLemOracle {
	t.Helper()
	tool := func(name string) string {
		t.Helper()
		path, err := exec.LookPath(name)
		if err != nil {
			home, _ := os.UserHomeDir()
			path = filepath.Join(home, ".opam", "default", "bin", name)
			if _, err := os.Stat(path); err != nil {
				requireOracle(t, name+" not installed (Lem RAM trace oracle)")
			}
		}
		return path
	}
	lem, ocamlfind, sail := tool("lem"), tool("ocamlfind"), tool("sail")
	// ocamlfind invokes ocamlopt by name. Keep the selected switch's tools first.
	t.Setenv("PATH", filepath.Dir(ocamlfind)+string(os.PathListSeparator)+os.Getenv("PATH"))
	run := func(t *testing.T, dir, command string, args ...string) ([]byte, error) {
		t.Helper()
		ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
		defer cancel()
		cmd := exec.CommandContext(ctx, command, args...)
		cmd.Dir = dir
		cmd.WaitDelay = 5 * time.Second
		out, err := cmd.CombinedOutput()
		if ctx.Err() != nil {
			t.Fatalf("oracle command timed out: %s %v\n%s", command, args, out)
		}
		return out, err
	}
	requireRun := func(dir, command string, args ...string) []byte {
		t.Helper()
		out, err := run(t, dir, command, args...)
		if err != nil {
			t.Fatalf("%s %v: %v\n%s", command, args, err, out)
		}
		return out
	}
	version, err := run(t, "", ocamlfind, "query", "-format", "%v", "libsail")
	if err != nil {
		requireOracle(t, "libsail OCaml runtime unavailable: "+string(version))
	}
	if strings.TrimSpace(string(version)) != "0.20.2" {
		t.Fatalf("Lem RAM oracle needs libsail 0.20.2, got %q", version)
	}
	if got := strings.TrimSpace(string(requireRun("", lem, "-v"))); got != "Lem 2026-05-01" {
		t.Fatalf("Lem RAM oracle needs Lem 2026-05-01, got %q", got)
	}
	share := strings.TrimSpace(string(requireRun("", sail, "--dir")))
	library := filepath.Join(share, "src", "gen_lib")
	runtime := strings.TrimSpace(string(requireRun("", ocamlfind, "query", "libsail")))
	// Pin both the Lem definitions used while translating the Arm wrapper and
	// the installed generated OCaml sources for the runtime we link. This is
	// source provenance, not a proof that the compiled runtime implements them.
	for _, pin := range []struct{ name, lemHash, mlHash string }{
		{"sail2_prompt_monad", "5811b4e8ceddd09f9ea7f16b41341554e547a8142fe4fabdef3df7229f4c75b6", "3211001cd85fcbfa62a7a78946bff0dd60502b0277fa240afa2aada10a1d348d"},
		{"sail2_prompt", "7bab2f6c9408e824c014f5a2778e8964668d579b233ec24a5a39208c5e5b2903", "8ea9dc0c42c9b655e0666ffc2ab88a123358254010987920ec5fba8cc7d80275"},
		{"sail2_values", "5851d30de60d0dd651396f71641104265ce0514859c28301154f3325c0c3353b", "23642696eea41288e75bc02b89ad0531c6e69dff32933b98b189aa366db16716"},
		{"sail2_instr_kinds", "ac27afcc7e1943ed6b8bc67234a19ed1b1f32f38a43c0f71c7336c52ebfd02b2", "b4bce95eb3518add5a882ee83cc545208daa5e6dbb748a2e21ae99a5b392938f"},
	} {
		for path, want := range map[string]string{
			filepath.Join(library, pin.name+".lem"): pin.lemHash,
			filepath.Join(runtime, pin.name+".ml"):  pin.mlHash,
		} {
			contents, err := os.ReadFile(path)
			if err != nil {
				t.Fatal(err)
			}
			if got := fmt.Sprintf("%x", sha256.Sum256(contents)); got != want {
				t.Fatalf("%s hash = %s, want %s", path, got, want)
			}
		}
	}
	source, err := os.ReadFile(filepath.Join(filepath.Dir(sailArmModel), "..", "aarch64_extras.lem"))
	if err != nil {
		requireOracle(t, "official Arm Lem source unavailable: "+err.Error())
	}
	if err := auditLemPlainRAM(source); err != nil {
		t.Fatal(err)
	}
	return sailLemOracle{lem, ocamlfind, sail, library, source, run}
}

// This executes the official Lem external wrapper, not a Go restatement of
// its semantics. It is a regression oracle, NOT a kernel-checked proof of
// execution, an architectural interpreter, or permission to admit BBM bodies.
func TestSailLemRAMTraces(t *testing.T) {
	oracle := newSailLemOracle(t)
	harness, err := os.ReadFile(filepath.Join("..", "spec", "sail", "lem", "ram_trace_test.ml"))
	if err != nil {
		t.Fatal(err)
	}
	const ea = "write_mem_ea Write_plain () address size >>"
	const write = "write_mem Write_plain () address size value >>= fun _ ->"
	for _, tc := range []struct{ name, old, replacement string }{
		{name: "official"},
		{"drop_EA", ea, "return () >>"},
		{"release_EA", ea, "write_mem_ea Write_release () address size >>"},
		{"drop_data", write, "return true >>= fun _ ->"},
		{"release_data", write, "write_mem Write_release () address size value >>= fun _ ->"},
		{"reject_false_ack", write + "\n  return ()", "write_mem Write_plain () address size value >>= fun ok ->\n  if ok then return () else Fail \"ack\""},
	} {
		t.Run(tc.name, func(t *testing.T) {
			input := string(oracle.armExtras)
			if tc.old != "" {
				if strings.Count(input, tc.old) != 1 {
					t.Fatal("mutation must replace exactly one occurrence")
				}
				input = strings.Replace(input, tc.old, tc.replacement, 1)
			}
			dir := t.TempDir()
			for name, contents := range map[string][]byte{
				"aarch64_extras.lem": []byte(input), "ram_trace_test.ml": harness,
			} {
				if err := os.WriteFile(filepath.Join(dir, name), contents, 0600); err != nil {
					t.Fatal(err)
				}
			}
			for _, args := range [][]string{
				{oracle.lem, "-ocaml", "-lib", oracle.library, "-outdir", dir, filepath.Join(dir, "aarch64_extras.lem")},
				{oracle.ocamlfind, "ocamlopt", "-package", "libsail", "-linkpkg", "-open", "Libsail", "aarch64_extras.ml", "ram_trace_test.ml", "-o", "ram_trace_test"},
			} {
				out, err := oracle.run(t, dir, args[0], args[1:]...)
				if err != nil {
					t.Fatalf("oracle must build, including mutants: %v\n%s", err, out)
				}
			}
			out, err := oracle.run(t, dir, filepath.Join(dir, "ram_trace_test"))
			if tc.old == "" {
				if err != nil || strings.TrimSpace(string(out)) != "Arm Lem RAM traces: 80 checks passed" {
					t.Fatalf("official trace oracle: %v\n%s", err, out)
				}
				t.Log(strings.TrimSpace(string(out)))
			} else if err == nil || !strings.Contains(string(out), "RAM trace check failed:") {
				t.Fatalf("mutant must fail a trace assertion, not compilation or infrastructure: %v\n%s", err, out)
			}
		})
	}
}
