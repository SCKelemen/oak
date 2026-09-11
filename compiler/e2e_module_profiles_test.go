package compiler

// Per-module discipline profiles (docs/spec/85-discipline.md section 1,
// 83-modules.md section 4.1): a warning rejects exactly when the module
// owning its primary cause is judged under the strict profile.

import (
	"strings"
	"testing"
)

// unboundedLoop is a while shape that records OAK-D0103 (section 3).
const unboundedLoop = `
pub spin: (n: u32): u32 {
  i: u32 = 0
  while i < n {
    i = i + 1
    n = n - 1
  }
  i
}
`

// A strict root with a dependency (its own module, no profile) whose loop
// is non-canonical: the dependency's warning is its own business.
func profileFixture(t *testing.T, rootManifestExtra string) string {
	t.Helper()
	return writeModule(t, map[string]string{
		"app/oak.mod": "module example.com/app\noak 0.1.0\nrequire example.com/lib 1.0.0\nreplace example.com/lib => ../lib\n" + rootManifestExtra,
		"app/main.oak": `package main
import("example.com/lib")

main: (): i32 {
  i32_bits_u32(lib.spin(u32(3)))
}
`,
		"lib/oak.mod": "module example.com/lib\noak 0.1.0\n",
		"lib/lib.oak": "package lib\n" + unboundedLoop,
	})
}

func TestModuleProfileStrictRootIgnoresDependencyWarnings(t *testing.T) {
	root := profileFixture(t, "profile strict\n")
	if _, err := New().WithPackageDir(root + "/app").EmitC().Get(); err != nil {
		t.Fatalf("a dependency's OAK-D0103 must not reject a strict root: %v", err)
	}
	// The command-line flag says the same thing.
	if _, err := New().WithPackageDir(root + "/app").WithProfile("strict").EmitC().Get(); err != nil {
		t.Fatalf("-profile strict must judge only the root module: %v", err)
	}
}

func TestModuleProfileStrictRootRejectsItsOwnWarnings(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/app\noak 0.1.0\nprofile strict\n",
		"main.oak": "main: (): i32 { i32_bits_u32(spin(u32(3))) }\n" + unboundedLoop,
	})
	_, err := New().WithPackageDir(root).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "OAK-D0103") {
		t.Fatalf("a strict manifest must reject the root's own OAK-D0103, got %v", err)
	}
	// The command-line flag overrides the manifest for the root module.
	if _, err := New().WithPackageDir(root).WithProfile("default").EmitC().Get(); err != nil {
		t.Fatalf("-profile default must override the manifest's strict: %v", err)
	}
}

func TestModuleProfileStrictDependencyRejectsItsOwnWarnings(t *testing.T) {
	root := writeModule(t, map[string]string{
		"app/oak.mod": "module example.com/app\noak 0.1.0\nrequire example.com/lib 1.0.0\nreplace example.com/lib => ../lib\n",
		"app/main.oak": `package main
import("example.com/lib")

main: (): i32 {
  i32_bits_u32(lib.spin(u32(3)))
}
`,
		"lib/oak.mod": "module example.com/lib\noak 0.1.0\nprofile strict\n",
		"lib/lib.oak": "package lib\n" + unboundedLoop,
	})
	_, err := New().WithPackageDir(root + "/app").EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "OAK-D0103") {
		t.Fatalf("a dependency that promises strict must be held to it, got %v", err)
	}
}

// import(std) under a strict root compiles: the prelude is judged under the
// default profile, the program under strict (ml finding F7).
func TestModuleProfileStrictRootWithPrelude(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/app\noak 0.1.0\n",
		"main.oak": "import(std)\nmain: (): i32 { 0 }\n",
	})
	if _, err := New().WithPackageDir(root).WithProfile("strict").EmitC().Get(); err != nil {
		t.Fatalf("strict root importing the prelude must compile: %v", err)
	}
	// A root warning still rejects with the prelude present.
	root = writeModule(t, map[string]string{
		"oak.mod":  "module example.com/app\noak 0.1.0\n",
		"main.oak": "import(std)\nmain: (): i32 { i32_bits_u32(spin(u32(3))) }\n" + unboundedLoop,
	})
	_, err := New().WithPackageDir(root).WithProfile("strict").EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "OAK-D0103") {
		t.Fatalf("root warning must reject under strict even with the prelude, got %v", err)
	}
}
