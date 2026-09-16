package main

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// ml ask 5.27: two modes of the same package must import into one Lean
// library without rewriting either generated file. Check the ordinary
// default too, and that the namespace and float mode do not affect C.
func TestBuildLeanNamespace(t *testing.T) {
	root := writeTree(t, map[string]string{
		"oak.mod": "module example.com/namespaces\n",
		"canon/canon.oak": `package canon
pub Cell: type = struct { value: u32 }
inc: (x: u32): u32 = x + 1
pub bump: (cell: Cell): Cell {
  result: Cell = cell
  result.value = inc(result.value)
  result
}
pub add: (a: f32, b: f32): f32 = a + b
`,
	})
	work, err := filepath.EvalSymlinks(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	var cSource string
	for _, tt := range []struct{ module, namespace, mode string }{
		{"Default", "", ""},
		{"Plain", "Ml.Canon", ""},
		{"Bits", "Ml.CanonBits", "bits"},
	} {
		args := []string{"-o", filepath.Join(work, tt.module+".c"), "-lean", filepath.Join(work, tt.module+".lean")}
		if tt.namespace != "" {
			args = append(args, "-lean-namespace", tt.namespace)
		}
		if tt.mode != "" {
			args = append(args, "-lean-floats", tt.mode)
		}
		args = append(args, filepath.Join(root, "canon"))
		if code, out := runCLI(t, buildPackage, args); code != 0 {
			t.Fatalf("%s build: %d\n%s", tt.module, code, out)
		}
		read := func(ext string) string {
			data, err := os.ReadFile(filepath.Join(work, tt.module+ext))
			if err != nil {
				t.Fatal(err)
			}
			return string(data)
		}
		if generated := read(".c"); cSource == "" {
			cSource = generated
		} else if generated != cSource {
			t.Fatalf("%s namespace or float mode changed the C output", tt.module)
		}
		namespace := tt.namespace
		if namespace == "" {
			namespace = "Oak.Canon"
		}
		lean := read(".lean")
		if !strings.Contains(lean, "\nnamespace "+namespace+"\n") || !strings.HasSuffix(lean, "end "+namespace+"\n") {
			t.Fatalf("%s namespace missing:\n%s", tt.module, lean)
		}
		if strings.Contains(lean, "Oak.FloatOps.add32") != (tt.mode == "bits") {
			t.Fatalf("%s lost its float mode:\n%s", tt.module, lean)
		}
	}
	t.Run("LeanImports", func(t *testing.T) {
		lake, err := exec.LookPath("lake")
		if err != nil {
			home, _ := os.UserHomeDir()
			lake = filepath.Join(home, ".elan", "bin", "lake")
			if _, err := os.Stat(lake); err != nil {
				t.Skip("lake not found (PATH or ~/.elan/bin)")
			}
		}
		ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
		defer cancel()
		run := func(args ...string) {
			t.Helper()
			cmd := exec.CommandContext(ctx, lake, args...)
			cmd.Dir = filepath.Join("spec", "lean")
			cmd.Env = append(os.Environ(), "LEAN_PATH="+work+string(os.PathListSeparator)+os.Getenv("LEAN_PATH"))
			if out, err := cmd.CombinedOutput(); err != nil {
				t.Fatalf("lake %v: %v\n%s", args, err, out)
			}
		}
		run("build", "Oak.FloatOps")
		for _, module := range []string{"Default", "Plain", "Bits"} {
			run("env", "lean", "-R", work, "-o", filepath.Join(work, module+".olean"), filepath.Join(work, module+".lean"))
		}
		driver := filepath.Join(work, "Together.lean")
		if err := os.WriteFile(driver, []byte(`import Default
import Plain
import Bits

example : Oak.Canon.bump { value := 41 } 1 = some { value := 42 } := by decide
example : Ml.Canon.bump { value := 41 } 1 = some { value := 42 } := by decide
example : Ml.CanonBits.bump { value := 41 } 1 = some { value := 42 } := by decide

def main : IO Unit := do
  let a := Float32.ofBits 0x3F800000
  let b := Float32.ofBits 0x40000000
  unless (Ml.Canon.add a b 1).map Float32.toBits == some 0x40400000 do
    throw (IO.userError "ordinary extraction result differs")
  unless (Ml.CanonBits.add a b 1).map Float32.toBits == some 0x40400000 do
    throw (IO.userError "bit-level extraction result differs")
`), 0o644); err != nil {
			t.Fatal(err)
		}
		run("env", "lean", "-R", work, "--run", driver)
	})
}
